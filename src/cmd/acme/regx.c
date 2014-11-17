#include <u.h>
#include <libc.h>
#include <draw.h>
#include <thread.h>
#include <cursor.h>
#include <mouse.h>
#include <keyboard.h>
#include <frame.h>
#include <fcall.h>
#include <plumb.h>
#include "dat.h"
#include "fns.h"
/*
 * Machine Information
 */
typedef struct Inst Inst;
struct Inst
{
	uint	type;	/* < OPERATOR ==> literal, otherwise action */
	union {
		int sid;
		int subid;
		int class;
		Inst *other;
		Inst *right;
	} u;
	union{
		Inst *left;
		Inst *next;
	} u1;
};

typedef struct Ilist Ilist;
struct Ilist
{
	Inst	*inst;		/* Instruction of the thread */
	Rangeset se;
	uint	startp;		/* first char of match */
};


/*
 * Actions and Tokens
 *
 *	0x10000xx are operators, value == precedence
 *	0x20000xx are tokens, i.e. operands for operators
 */
#define	OPERATOR	0x1000000	/* Bit set in all operators */
#define	START		(OPERATOR+0)	/* Start, used for marker on stack */
#define	RBRA		(OPERATOR+1)	/* Right bracket, ) */
#define	LBRA		(OPERATOR+2)	/* Left bracket, ( */
#define	OR		(OPERATOR+3)	/* Alternation, | */
#define	CAT		(OPERATOR+4)	/* Concatentation, implicit operator */
#define	STAR		(OPERATOR+5)	/* Closure, * */
#define	PLUS		(OPERATOR+6)	/* a+ == aa* */
#define	QUEST		(OPERATOR+7)	/* a? == a|nothing, i.e. 0 or 1 a's */
#define	ANY		0x2000000	/* Any character but newline, . */
#define	NOP		(ANY+1)	/* No operation, internal use only */
#define	BOL		(ANY+2)	/* Beginning of line, ^ */
#define	EOL		(ANY+3)	/* End of line, $ */
#define	CCLASS		(ANY+4)	/* Character class, [] */
#define	NCCLASS		(ANY+5)	/* Negated character class, [^] */
#define	END		(ANY+0x77)	/* Terminate: match found */

#define	ISATOR		OPERATOR
#define	ISAND		ANY

#define	QUOTED	0x4000000	/* Bit set for \-ed lex characters */

/*
 * Parser Information
 */
typedef struct Node Node;
struct Node
{
	Inst	*first;
	Inst	*last;
};

#define	NSTACK	20
#define	NPROG	1024
#define	NLIST	127

typedef struct RX RX;

struct RX
{
	Rangeset	sel;
	Rune*	pattern;
	Inst	program[NPROG];
	Inst	*progp;
	Inst	*startinst;	/* First inst. of program; might not be program[0] */
	Inst	*bstartinst;	/* same for backwards machine */
	Channel	*rechan;	/* chan(Inst*) */
	Node	andstack[NSTACK];
	Node	*andp;
	int	atorstack[NSTACK];
	int	*atorp;
	int	lastwasand;	/* Last token was operand */
	int	cursubid;
	int	subidstack[NSTACK];
	int	*subidp;
	int	backwards;
	int	nbra;
	Rune	*exprp;		/* pointer to next character in source expression */
	#define	DCLASS	10	/* allocation increment */
	int	nclass;		/* number active */
	int	Nclass;		/* high water mark */
	Rune	**class;
	int	negateclass;

	Ilist	*tl, *nl;	/* This list, next list */
	Ilist	list[2][NLIST+1];	/* +1 for trailing null */
	Rangeset sempty;
};

int	addinst(Ilist *l, Inst *inst, Rangeset *sep);
void	newmatch(RX*, Rangeset*);
void	bnewmatch(RX*, Rangeset*);
void	pushand(RX*, Inst*, Inst*);
void	pushator(RX*, int);
Node	*popand(RX*, int);
int	popator(RX*);
void   startlex(RX*, Rune*);
int	lex(RX*);
void	operator(RX*, int);
void	operand(RX*, int);
void	evaluntil(RX*,int);
void	optimize(Inst*);
void	bldcclass(RX*);

void
rxfree(RX* rx)
{
	int i;
	for(i=0; i<rx->nclass; i++)
		free(rx->class[i]);
	free(rx->pattern);
	free(rx);
}

void
regerror(RX* rx, char *e)
{
	warning(nil, "regexp: %s\n", e);
	sendp(rx->rechan, nil);
	threadexits(nil);
}

Inst *
newinst(RX* rx, int t)
{
	if(rx->progp >= &rx->program[NPROG])
		regerror(rx, "expression too long");
	rx->progp->type = t;
	rx->progp->u1.left = nil;
	rx->progp->u.right = nil;
	return rx->progp++;
}

void
realcompile(void *arg)
{
	int token;
	RX *rx;

	threadsetname("regcomp");
	rx = arg;
	startlex(rx, rx->pattern);
	rx->atorp = rx->atorstack;
	rx->andp = rx->andstack;
	rx->subidp = rx->subidstack;
	rx->cursubid = 0;
	rx->lastwasand = FALSE;
	/* Start with a low priority operator to prime parser */
	pushator(rx, START-1);
	while((token=lex(rx)) != END){
		if((token&ISATOR) == OPERATOR)
			operator(rx, token);
		else
			operand(rx, token);
	}
	/* Close with a low priority operator */
	evaluntil(rx, START);
	/* Force END */
	operand(rx, END);
	evaluntil(rx, START);
	if(rx->nbra)
		regerror(rx, "unmatched `('");
	--rx->andp;	/* points to first and only operand */
	sendp(rx->rechan, rx->andp->first);
	threadexits(nil);
}

/* r is null terminated */
RX*
rxcompile(Rune *r)
{
	int nr;
	Inst *oprogp;

	nr = runestrlen(r)+1;
	RX* rx=calloc(1, sizeof(RX));
	if(rx == nil)
		return nil;
	rx->rechan = chancreate(sizeof(Inst*), 0);
	chansetname(rx->rechan, "rechan");
	rx->progp = rx->program;
	rx->backwards = FALSE;
	rx->bstartinst = nil;
	rx->pattern = runerealloc(rx->pattern, nr);
	runemove(rx->pattern, r, nr);
	threadcreate(realcompile, rx, STACK);
	rx->startinst = recvp(rx->rechan);
	if(rx->startinst == nil){
		rxfree(rx);
		return nil;
	}
	optimize(rx->program);
	oprogp = rx->progp;
	rx->backwards = TRUE;
	threadcreate(realcompile, rx, STACK);
	rx->bstartinst = recvp(rx->rechan);
	if(rx->bstartinst == nil){
		rxfree(rx);
		return nil;
	}
	optimize(oprogp);
	return rx;
}

void
operand(RX* rx, int t)
{
	Inst *i;
	if(rx->lastwasand)
		operator(rx, CAT);	/* catenate is implicit */
	i = newinst(rx, t);
	if(t == CCLASS){
		if(rx->negateclass)
			i->type = NCCLASS;	/* UGH */
		i->u.class = rx->nclass-1;		/* UGH */
	}
	pushand(rx, i, i);
	rx->lastwasand = TRUE;
}

void
operator(RX* rx, int t)
{
	if(t==RBRA && --rx->nbra<0)
		regerror(rx, "unmatched `)'");
	if(t==LBRA){
		rx->cursubid++;	/* silently ignored */
		rx->nbra++;
		if(rx->lastwasand)
			operator(rx, CAT);
	}else
		evaluntil(rx, t);
	if(t!=RBRA)
		pushator(rx, t);
	rx->lastwasand = FALSE;
	if(t==STAR || t==QUEST || t==PLUS || t==RBRA)
		rx->lastwasand = TRUE;	/* these look like operands */
}

void
pushand(RX* rx, Inst *f, Inst *l)
{
	if(rx->andp >= &rx->andstack[NSTACK])
		error("operand stack overflow");
	rx->andp->first = f;
	rx->andp->last = l;
	rx->andp++;
}

void
pushator(RX* rx, int t)
{
	if(rx->atorp >= &rx->atorstack[NSTACK])
		error("operator stack overflow");
	*rx->atorp++=t;
	if(rx->cursubid >= NRange)
		*rx->subidp++= -1;
	else
		*rx->subidp++=rx->cursubid;
}

Node *
popand(RX* rx, int op)
{
	char buf[64];

	if(rx->andp <= &rx->andstack[0])
		if(op){
			sprint(buf, "missing operand for %c", op);
			regerror(rx, buf);
		}else
			regerror(rx, "malformed regexp");
	return --rx->andp;
}

int
popator(RX* rx)
{
	if(rx->atorp <= &rx->atorstack[0])
		error("operator stack underflow");
	--rx->subidp;
	return *--rx->atorp;
}

void
evaluntil(RX* rx, int pri)
{
	Node *op1, *op2, *t;
	Inst *inst1, *inst2;

	while(pri==RBRA || rx->atorp[-1]>=pri){
		switch(popator(rx)){
		case LBRA:
			op1 = popand(rx, '(');
			inst2 = newinst(rx, RBRA);
			inst2->u.subid = *rx->subidp;
			op1->last->u1.next = inst2;
			inst1 = newinst(rx, LBRA);
			inst1->u.subid = *rx->subidp;
			inst1->u1.next = op1->first;
			pushand(rx, inst1, inst2);
			return;		/* must have been RBRA */
		default:
			error("unknown regexp operator");
			break;
		case OR:
			op2 = popand(rx, '|');
			op1 = popand(rx, '|');
			inst2 = newinst(rx, NOP);
			op2->last->u1.next = inst2;
			op1->last->u1.next = inst2;
			inst1 = newinst(rx, OR);
			inst1->u.right = op1->first;
			inst1->u1.left = op2->first;
			pushand(rx, inst1, inst2);
			break;
		case CAT:
			op2 = popand(rx, 0);
			op1 = popand(rx, 0);
			if(rx->backwards && op2->first->type!=END){
				t = op1;
				op1 = op2;
				op2 = t;
			}
			op1->last->u1.next = op2->first;
			pushand(rx, op1->first, op2->last);
			break;
		case STAR:
			op2 = popand(rx, '*');
			inst1 = newinst(rx, OR);
			op2->last->u1.next = inst1;
			inst1->u.right = op2->first;
			pushand(rx, inst1, inst1);
			break;
		case PLUS:
			op2 = popand(rx, '+');
			inst1 = newinst(rx, OR);
			op2->last->u1.next = inst1;
			inst1->u.right = op2->first;
			pushand(rx, op2->first, inst1);
			break;
		case QUEST:
			op2 = popand(rx, '?');
			inst1 = newinst(rx, OR);
			inst2 = newinst(rx, NOP);
			inst1->u1.left = inst2;
			inst1->u.right = op2->first;
			op2->last->u1.next = inst2;
			pushand(rx, inst1, inst2);
			break;
		}
	}
}


void
optimize(Inst *start)
{
	Inst *inst, *target;

	for(inst=start; inst->type!=END; inst++){
		target = inst->u1.next;
		while(target->type == NOP)
			target = target->u1.next;
		inst->u1.next = target;
	}
}

void
startlex(RX* rx, Rune *s)
{
       rx->exprp = s;
       rx->nbra = 0;
}

int
lex(RX* rx){
	int c;

	c = *rx->exprp++;
	switch(c){
	case '\\':
		if(*rx->exprp)
			if((c= *rx->exprp++)=='n')
				c='\n';
		break;
	case 0:
		c = END;
		--rx->exprp;	/* In case we come here again */
		break;
	case '*':
		c = STAR;
		break;
	case '?':
		c = QUEST;
		break;
	case '+':
		c = PLUS;
		break;
	case '|':
		c = OR;
		break;
	case '.':
		c = ANY;
		break;
	case '(':
		c = LBRA;
		break;
	case ')':
		c = RBRA;
		break;
	case '^':
		c = BOL;
		break;
	case '$':
		c = EOL;
		break;
	case '[':
		c = CCLASS;
		bldcclass(rx);
		break;
	}
	return c;
}

int
nextrec(RX* rx)
{
	if(rx->exprp[0]==0 || (rx->exprp[0]=='\\' && rx->exprp[1]==0))
		regerror(rx, "malformed `[]'");
	if(rx->exprp[0] == '\\'){
		rx->exprp++;
		if(*rx->exprp=='n'){
			rx->exprp++;
			return '\n';
		}
		return *rx->exprp++|QUOTED;
	}
	return *rx->exprp++;
}

void
bldcclass(RX* rx)
{
	int c1, c2, n, na;
	Rune *classp;

	classp = runemalloc(DCLASS);
	n = 0;
	na = DCLASS;
	/* we have already seen the '[' */
	if(*rx->exprp == '^'){
		classp[n++] = '\n';	/* don't match newline in negate case */
		rx->negateclass = TRUE;
		rx->exprp++;
	}else
		rx->negateclass = FALSE;
	while((c1 = nextrec(rx)) != ']'){
		if(c1 == '-'){
    Error:
			free(classp);
			regerror(rx, "malformed `[]'");
		}
		if(n+4 >= na){		/* 3 runes plus NUL */
			na += DCLASS;
			classp = runerealloc(classp, na);
		}
		if(*rx->exprp == '-'){
			rx->exprp++;	/* eat '-' */
			if((c2 = nextrec(rx)) == ']')
				goto Error;
			classp[n+0] = Runemax;
			classp[n+1] = c1;
			classp[n+2] = c2;
			n += 3;
		}else
			classp[n++] = c1 & ~QUOTED;
	}
	classp[n] = 0;
	if(rx->nclass == rx->Nclass){
		rx->Nclass += DCLASS;
		rx->class = realloc(rx->class, rx->Nclass*sizeof(Rune*));
	}
	rx->class[rx->nclass++] = classp;
}

int
classmatch(RX* rx, int classno, int c, int negate)
{
	Rune *p;

	p = rx->class[classno];
	while(*p){
		if(*p == Runemax){
			if(p[1]<=c && c<=p[2])
				return !negate;
			p += 3;
		}else if(*p++ == c)
			return !negate;
	}
	return negate;
}

/*
 * Note optimization in addinst:
 * 	*l must be pending when addinst called; if *l has been looked
 *		at already, the optimization is a bug.
 */
int
addinst(Ilist *l, Inst *inst, Rangeset *sep)
{
	Ilist *p;

	for(p = l; p->inst; p++){
		if(p->inst==inst){
			if((sep)->r[0].q0 < p->se.r[0].q0)
				p->se= *sep;	/* this would be bug */
			return 0;	/* It's already there */
		}
	}
	p->inst = inst;
	p->se= *sep;
	(p+1)->inst = nil;
	return 1;
}

/* either t!=nil or r!=nil, and we match the string in the appropriate place */
int
rxexecute(RX* rx, Text *t, Rune *r, uint startp, uint eof, Rangeset *rp)
{
	int flag;
	Inst *inst;
	Ilist *tlp;
	uint p;
	int nnl, ntl;
	int nc, c;
	int wrapped;
	int startchar;

	flag = 0;
	p = startp;
	startchar = 0;
	wrapped = 0;
	nnl = 0;
	if(rx->startinst->type<OPERATOR)
		startchar = rx->startinst->type;
	rx->list[0][0].inst = rx->list[1][0].inst = nil;
	rx->sel.r[0].q0 = -1;
	if(t != nil)
		nc = t->file->b.nc;
	else
		nc = runestrlen(r);
	/* Execute machine once for each character */
	for(;;p++){
	doloop:
		if(p>=eof || p>=nc){
			switch(wrapped++){
			case 0:		/* let loop run one more click */
			case 2:
				break;
			case 1:		/* expired; wrap to beginning */
				if(rx->sel.r[0].q0>=0 || eof!=Infinity)
					goto Return;
				rx->list[0][0].inst = rx->list[1][0].inst = nil;
				p = 0;
				goto doloop;
			default:
				goto Return;
			}
			c = 0;
		}else{
			if(((wrapped && p>=startp) || rx->sel.r[0].q0>0) && nnl==0)
				break;
			if(t != nil)
				c = textreadc(t, p);
			else
				c = r[p];
		}
		/* fast check for first char */
		if(startchar && nnl==0 && c!=startchar)
			continue;
		rx->tl = rx->list[flag];
		rx->nl = rx->list[flag^=1];
		rx->nl->inst = nil;
		ntl = nnl;
		nnl = 0;
		if(rx->sel.r[0].q0<0 && (!wrapped || p<startp || startp==eof)){
			/* Add first instruction to this list */
			rx->sempty.r[0].q0 = p;
			if(addinst(rx->tl, rx->startinst, &rx->sempty))
			if(++ntl >= NLIST){
	Overflow:
				warning(nil, "regexp list overflow\n");
				rx->sel.r[0].q0 = -1;
				goto Return;
			}
		}
		/* Execute machine until this list is empty */
		for(tlp = rx->tl; inst = tlp->inst; tlp++){	/* assignment = */
	Switchstmt:
			switch(inst->type){
			default:	/* regular character */
				if(inst->type==c){
	Addinst:
					if(addinst(rx->nl, inst->u1.next, &tlp->se))
					if(++nnl >= NLIST)
						goto Overflow;
				}
				break;
			case LBRA:
				if(inst->u.subid>=0)
					tlp->se.r[inst->u.subid].q0 = p;
				inst = inst->u1.next;
				goto Switchstmt;
			case RBRA:
				if(inst->u.subid>=0)
					tlp->se.r[inst->u.subid].q1 = p;
				inst = inst->u1.next;
				goto Switchstmt;
			case ANY:
				if(c!='\n')
					goto Addinst;
				break;
			case BOL:
				if(p==0 || (t!=nil && textreadc(t, p-1)=='\n') || (r!=nil && r[p-1]=='\n')){
	Step:
					inst = inst->u1.next;
					goto Switchstmt;
				}
				break;
			case EOL:
				if(c == '\n')
					goto Step;
				break;
			case CCLASS:
				if(c>=0 && classmatch(rx, inst->u.class, c, 0))
					goto Addinst;
				break;
			case NCCLASS:
				if(c>=0 && classmatch(rx, inst->u.class, c, 1))
					goto Addinst;
				break;
			case OR:
				/* evaluate right choice later */
				if(addinst(tlp, inst->u.right, &tlp->se))
				if(++ntl >= NLIST)
					goto Overflow;
				/* efficiency: advance and re-evaluate */
				inst = inst->u1.left;
				goto Switchstmt;
			case END:	/* Match! */
				tlp->se.r[0].q1 = p;
				newmatch(rx, &tlp->se);
				break;
			}
		}
	}
    Return:
	*rp = rx->sel;
	return rx->sel.r[0].q0 >= 0;
}

void
newmatch(RX* rx, Rangeset *sp)
{
	if(rx->sel.r[0].q0<0 || sp->r[0].q0<rx->sel.r[0].q0 ||
	   (sp->r[0].q0==rx->sel.r[0].q0 && sp->r[0].q1>rx->sel.r[0].q1))
		rx->sel = *sp;
}

int
rxbexecute(RX* rx, Text *t, uint startp, Rangeset *rp)
{
	int flag;
	Inst *inst;
	Ilist *tlp;
	int p;
	int nnl, ntl;
	int c;
	int wrapped;
	int startchar;

	flag = 0;
	nnl = 0;
	wrapped = 0;
	p = startp;
	startchar = 0;
	if(rx->bstartinst->type<OPERATOR)
		startchar = rx->bstartinst->type;
	rx->list[0][0].inst = rx->list[1][0].inst = nil;
	rx->sel.r[0].q0= -1;
	/* Execute machine once for each character, including terminal NUL */
	for(;;--p){
	doloop:
		if(p <= 0){
			switch(wrapped++){
			case 0:		/* let loop run one more click */
			case 2:
				break;
			case 1:		/* expired; wrap to end */
				if(rx->sel.r[0].q0>=0)
					goto Return;
				rx->list[0][0].inst = rx->list[1][0].inst = nil;
				p = t->file->b.nc;
				goto doloop;
			case 3:
			default:
				goto Return;
			}
			c = 0;
		}else{
			if(((wrapped && p<=startp) || rx->sel.r[0].q0>0) && nnl==0)
				break;
			c = textreadc(t, p-1);
		}
		/* fast check for first char */
		if(startchar && nnl==0 && c!=startchar)
			continue;
		rx->tl = rx->list[flag];
		rx->nl = rx->list[flag^=1];
		rx->nl->inst = nil;
		ntl = nnl;
		nnl = 0;
		if(rx->sel.r[0].q0<0 && (!wrapped || p>startp)){
			/* Add first instruction to this list */
			/* the minus is so the optimizations in addinst work */
			rx->sempty.r[0].q0 = -p;
			if(addinst(rx->tl, rx->bstartinst, &rx->sempty))
			if(++ntl >= NLIST){
	Overflow:
				warning(nil, "regexp list overflow\n");
				rx->sel.r[0].q0 = -1;
				goto Return;
			}
		}
		/* Execute machine until this list is empty */
		for(tlp = rx->tl; inst = tlp->inst; tlp++){	/* assignment = */
	Switchstmt:
			switch(inst->type){
			default:	/* regular character */
				if(inst->type == c){
	Addinst:
					if(addinst(rx->nl, inst->u1.next, &tlp->se))
					if(++nnl >= NLIST)
						goto Overflow;
				}
				break;
			case LBRA:
				if(inst->u.subid>=0)
					tlp->se.r[inst->u.subid].q0 = p;
				inst = inst->u1.next;
				goto Switchstmt;
			case RBRA:
				if(inst->u.subid >= 0)
					tlp->se.r[inst->u.subid].q1 = p;
				inst = inst->u1.next;
				goto Switchstmt;
			case ANY:
				if(c != '\n')
					goto Addinst;
				break;
			case BOL:
				if(c=='\n' || p==0){
	Step:
					inst = inst->u1.next;
					goto Switchstmt;
				}
				break;
			case EOL:
				if(p<t->file->b.nc && textreadc(t, p)=='\n')
					goto Step;
				break;
			case CCLASS:
				if(c>0 && classmatch(rx, inst->u.class, c, 0))
					goto Addinst;
				break;
			case NCCLASS:
				if(c>0 && classmatch(rx, inst->u.class, c, 1))
					goto Addinst;
				break;
			case OR:
				/* evaluate right choice later */
				if(addinst(rx->tl, inst->u.right, &tlp->se))
				if(++ntl >= NLIST)
					goto Overflow;
				/* efficiency: advance and re-evaluate */
				inst = inst->u1.left;
				goto Switchstmt;
			case END:	/* Match! */
				tlp->se.r[0].q0 = -tlp->se.r[0].q0; /* minus sign */
				tlp->se.r[0].q1 = p;
				bnewmatch(rx, &tlp->se);
				break;
			}
		}
	}
    Return:
	*rp = rx->sel;
	return rx->sel.r[0].q0 >= 0;
}

void
bnewmatch(RX *rx, Rangeset *sp)
{
        int  i;

        if(rx->sel.r[0].q0<0 || sp->r[0].q0>rx->sel.r[0].q1 || (sp->r[0].q0==rx->sel.r[0].q1 && sp->r[0].q1<rx->sel.r[0].q0))
                for(i = 0; i<NRange; i++){       /* note the reversal; q0<=q1 */
                        rx->sel.r[i].q0 = sp->r[i].q1;
                        rx->sel.r[i].q1 = sp->r[i].q0;
                }
}
