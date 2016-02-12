#include <u.h>
#include <libc.h>
#include <tos.h>

static uvlong order = 0x0001020304050607ULL;

static void
be2vlong(vlong *to, uchar *f)
{
	uchar *t, *o;
	int i;

	t = (uchar*)to;
	o = (uchar*)&order;
	for(i = 0; i < sizeof order; i++)
		t[o[i]] = f[i];
}

vlong
nsec(void)
{
	uchar b[8];
	vlong t;
	int f, n;

	t = 0;
	if((f = open("/dev/bintime", OREAD|OCEXEC)) >= 0){
		n = pread(f, b, sizeof(b), 0);
		close(f);
		if(n == sizeof(b))
			be2vlong(&t, b);
	}
	return t;
}
