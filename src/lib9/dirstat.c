#include <u.h>
#define NOPLAN9DEFINES
#include <libc.h>

#include <sys/stat.h>

extern int _p9dir(struct stat*, char*, Dir*, char**, char*);

Dir*
dirstat(char *file)
{
	struct stat st;
	int nstr;
	Dir *d;
	char *str;

	if(stat(file, &st) < 0)
		return nil;

	nstr = _p9dir(&st, file, nil, nil, nil);
	d = mallocz(sizeof(Dir)+nstr, 1);
	if(d == nil)
		return nil;
	str = (char*)&d[1];
	_p9dir(&st, file, d, &str, str+nstr);
	return d;
}

