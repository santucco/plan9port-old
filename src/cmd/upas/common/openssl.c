#include <u.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <libc.h>
#include <thread.h>
#include "common.h"

AUTOLIB(ssl)
AUTOLIB(crypto)

enum
{
	STACK = 8192,
	BSIZE = 0x10000
};

struct openssl {
	SSL_CTX* ctx;
	SSL* ssl;
	int	fd;
	int efd;
};

typedef struct openssl openssl;

static void
opensslinit(void)
{
	SSL_library_init();
	SSL_load_error_strings();
}

static void
opensslproc(void *v)
{	
	openssl* ssl = v;
	char buf[BSIZE];
	int n, m, c;

	m = ssl->fd > ssl->efd ? ssl->fd : ssl->efd;
	m++;
	while(1){
		fd_set rs;
		FD_ZERO(&rs);
		FD_SET(ssl->fd, &rs);
		FD_SET(ssl->efd, &rs);
		n = select(m, &rs, 0, 0, 0);
		if(n < 0){
			werrstr("opensslproc: %s", strerror(errno));
			break;
		}
		if(FD_ISSET(ssl->fd, &rs)){
			n=read(ssl->fd, buf, sizeof buf);
			if(n==0)
				break;
			if(n < 0) {
				werrstr("openssl: %s", strerror(errno));
				break;
			}
			for(c=SSL_write(ssl->ssl, buf, n); c > 0 && c < n; c+=SSL_write(ssl->ssl, buf + c, n - c));
			if(c < 0) {
				ERR_error_string_n(ERR_get_error(), buf, sizeof buf);
				werrstr("openssl: %s", buf);
				break;
			}
		}
		if(FD_ISSET(ssl->efd, &rs)){
			n=SSL_read(ssl->ssl, buf, sizeof buf);
			if(n==0)
				break;
			if(n < 0) {
				ERR_error_string_n(ERR_get_error(), buf, sizeof buf);
				werrstr("openssl: %s", buf);
				break;
			}
			for(c=write(ssl->fd, buf, n); c > 0 && c < n; c+=write(ssl->fd, buf + c, n - c));
			if(c < 0) {
				werrstr("openssl: %s", strerror(errno));
				break;
			}
		}
	}
	close(ssl->fd);
	close(ssl->efd);
	SSL_CTX_free(ssl->ctx);
	SSL_free(ssl->ssl);
	free(ssl);
}

int
opensslhandshake(int fd)
{
	SSL_CTX* ctx;
	SSL*     ssl;
	static int inited;
	openssl *pssl;
	int fds[2];
	char buf[1024];
	
	if(!inited){
		opensslinit();
		inited = 1;
	}
	
	ctx = SSL_CTX_new(SSLv23_client_method());
	ssl = SSL_new(ctx); 
	SSL_set_fd(ssl, fd);
	pssl=malloc(sizeof *pssl);
	if(SSL_connect(ssl) <=0 || !pssl || pipe(fds) < 0){
		ERR_error_string_n(ERR_get_error(), buf, sizeof buf);
		werrstr("openssl: %s", buf);
		SSL_CTX_free(ctx);
		SSL_free(ssl);
		if(pssl)
			free(pssl);
		return -1;
	}
		
	pssl->ctx = ctx;
	pssl->ssl = ssl;
	pssl->fd = fds[0];
	pssl->efd = fd;
	proccreate(opensslproc, pssl, STACK);
	return fds[1];
}
