#include	"l.h"

static Prog *PP;

static long	movt(int, long, int);
static long	ofmvl(Prog*, Adr*, int);
static long	ofstm(int, int);
static void		checkfpregs(Prog*, ulong, int*, int*);
static long	ovfpr(long, int, int, int, int);

void
asmout(Prog *p, Optab *o)
{
	long o1, o2, o3, o4, o5, o6, v;
	int r, rf, rt, rt2, lo, hi;
	Sym *s;

PP = p;
	o1 = 0;
	o2 = 0;
	o3 = 0;
	o4 = 0;
	o5 = 0;
	o6 = 0;
	switch(o->type) {
	default:
		diag("unknown asm %d", o->type);
		prasm(p);
		break;

	case 0:		/* pseudo ops */
		break;

	case 1:		/* op R,[R],R */
		o1 = oprrr(p->as, p->scond);
		rf = p->from.reg;
		rt = p->to.reg;
		r = p->reg;
		if(p->to.type == D_NONE)
			rt = 0;
		if(p->as == AMOVW || p->as == AMVN)
			r = 0;
		else if(r == NREG)
			r = rt;
		o1 |= rf | (r<<16) | (rt<<12);
		break;

	case 2:		/* movbu $I,[R],R */
		aclass(&p->from);
		o1 = oprrr(p->as, p->scond);
		o1 |= immrot(instoffset);
		rt = p->to.reg;
		r = p->reg;
		if(p->to.type == D_NONE)
			rt = 0;
		if(p->as == AMOVW || p->as == AMVN)
			r = 0;
		else if(r == NREG)
			r = rt;
		o1 |= (r<<16) | (rt<<12);
		break;

	case 3:		/* add R<<[IR],[R],R */
	mov:
		aclass(&p->from);
		o1 = oprrr(p->as, p->scond);
		o1 |= p->from.offset;
		rt = p->to.reg;
		r = p->reg;
		if(p->to.type == D_NONE)
			rt = 0;
		if(p->as == AMOVW || p->as == AMVN)
			r = 0;
		else if(r == NREG)
			r = rt;
		o1 |= (r<<16) | (rt<<12);
		break;

	case 4:		/* add $I,[R],R */
		aclass(&p->from);
		o1 = oprrr(AADD, p->scond);
		o1 |= immrot(instoffset);
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o1 |= r << 16;
		o1 |= p->to.reg << 12;
		break;

	case 5:		/* bra s */
		v = -8;
		if(p->cond == UP) {
			s = p->to.sym;
			if(s->type != SUNDEF)
				diag("bad branch sym type");
			v = (ulong)s->value >> (Roffset-2);
			dynreloc(s, p->pc, 0);
		}
		else if(p->cond != P)
			v = (p->cond->pc - pc) - 8;
		o1 = opbra(p->as, p->scond);
		o1 |= (v >> 2) & 0xffffff;
		break;

	case 6:		/* b ,O(R) -> add $O,R,PC */
		aclass(&p->to);
		o1 = oprrr(AADD, p->scond);
		o1 |= immrot(instoffset);
		o1 |= p->to.reg << 16;
		o1 |= REGPC << 12;
		break;

	case 7:		/* bl ,O(R) -> mov PC,link; add $O,R,PC */
		aclass(&p->to);
		o1 = oprrr(AADD, p->scond);
		o1 |= immrot(0);
		o1 |= REGPC << 16;
		o1 |= REGLINK << 12;

		o2 = oprrr(AADD, p->scond);
		o2 |= immrot(instoffset);
		o2 |= p->to.reg << 16;
		o2 |= REGPC << 12;
		break;

	case 8:		/* sll $c,[R],R -> mov (R<<$c),R */
		aclass(&p->from);
		o1 = oprrr(p->as, p->scond);
		r = p->reg;
		if(r == NREG)
			r = p->to.reg;
		o1 |= r;
		o1 |= (instoffset&31) << 7;
		o1 |= p->to.reg << 12;
		break;

	case 9:		/* sll R,[R],R -> mov (R<<R),R */
		o1 = oprrr(p->as, p->scond);
		r = p->reg;
		if(r == NREG)
			r = p->to.reg;
		o1 |= r;
		o1 |= (p->from.reg << 8) | (1<<4);
		o1 |= p->to.reg << 12;
		break;

	case 10:	/* svc/swi [$con] */
		o1 = oprrr(p->as, p->scond);
		if(p->to.type != D_NONE) {
			aclass(&p->to);
			o1 |= instoffset & 0xffffff;
		}
		break;

	case 11:	/* word */
		switch(aclass(&p->to)) {
		case C_LCON:
			if(!dlm)
				break;
			if(p->to.name != D_EXTERN && p->to.name != D_STATIC)
				break;
		case C_ADDR:
			if(p->to.sym->type == SUNDEF)
				ckoff(p->to.sym, p->to.offset);
			dynreloc(p->to.sym, p->pc, 1);
		}
		o1 = instoffset;
		break;

	case 12:	/* movw $lcon, reg */
		o1 = omvl(p, &p->from, p->to.reg);
		break;

	case 13:	/* op $lcon, [R], R */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;
		o2 = oprrr(p->as, p->scond);
		o2 |= REGTMP;
		r = p->reg;
		if(p->as == AMOVW || p->as == AMVN)
			r = 0;
		else if(r == NREG)
			r = p->to.reg;
		o2 |= r << 16;
		if(p->to.type != D_NONE)
			o2 |= p->to.reg << 12;
		break;

	case 14:	/* movb/movbu/movh/movhu R,R */
		o1 = oprrr(ASLL, p->scond);

		if(p->as == AMOVBU || p->as == AMOVHU)
			o2 = oprrr(ASRL, p->scond);
		else
			o2 = oprrr(ASRA, p->scond);

		r = p->to.reg;
		o1 |= (p->from.reg)|(r<<12);
		o2 |= (r)|(r<<12);
		if(p->as == AMOVB || p->as == AMOVBU) {
			o1 |= (24<<7);
			o2 |= (24<<7);
		} else {
			o1 |= (16<<7);
			o2 |= (16<<7);
		}
		break;

	case 15:	/* mul r,[r,]r */
		o1 = oprrr(p->as, p->scond);
		rf = p->from.reg;
		rt = p->to.reg;
		r = p->reg;
		if(r == NREG)
			r = rt;
		if(rt == r) {
			r = rf;
			rf = rt;
		}
		if(0)
		if(rt == r || rf == REGPC || r == REGPC || rt == REGPC) {
			diag("bad registers in MUL");
			prasm(p);
		}
		o1 |= (rf<<8) | r | (rt<<16);
		break;


	case 16:	/* div r,[r,]r */
		o1 = 0xf << 28;
		o2 = 0;
		break;

	case 17:
		o1 = oprrr(p->as, p->scond);
		rf = p->from.reg;
		rt = p->to.reg;
		rt2 = p->to.offset;
		r = p->reg;
		o1 |= (rf<<8) | r | (rt<<16) | (rt2<<12);
		break;

	case 20:	/* mov/movb/movbu R,O(R) */
		aclass(&p->to);
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o1 = osr(p->as, p->from.reg, instoffset, r, p->scond);
		break;

	case 21:	/* mov/movbu O(R),R -> lr */
		aclass(&p->from);
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o1 = olr(instoffset, r, p->to.reg, p->scond);
		if(p->as != AMOVW)
			o1 |= 1<<22;
		break;

	case 22:	/* movb/movh/movhu O(R),R -> lr,shl,shr */
		aclass(&p->from);
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o1 = olr(instoffset, r, p->to.reg, p->scond);

		o2 = oprrr(ASLL, p->scond);
		o3 = oprrr(ASRA, p->scond);
		r = p->to.reg;
		if(p->as == AMOVB) {
			o2 |= (24<<7)|(r)|(r<<12);
			o3 |= (24<<7)|(r)|(r<<12);
		} else {
			o2 |= (16<<7)|(r)|(r<<12);
			if(p->as == AMOVHU)
				o3 = oprrr(ASRL, p->scond);
			o3 |= (16<<7)|(r)|(r<<12);
		}
		break;

	case 23:	/* movh/movhu R,O(R) -> sb,sb */
		aclass(&p->to);
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o1 = osr(AMOVH, p->from.reg, instoffset, r, p->scond);

		o2 = oprrr(ASRL, p->scond);
		o2 |= (8<<7)|(p->from.reg)|(REGTMP<<12);

		o3 = osr(AMOVH, REGTMP, instoffset+1, r, p->scond);
		break;

	case 30:	/* mov/movb/movbu R,L(R) */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o2 = osrr(p->from.reg, REGTMP,r, p->scond);
		if(p->as != AMOVW)
			o2 |= 1<<22;
		break;

	case 31:	/* mov/movbu L(R),R -> lr[b] */
	case 32:	/* movh/movb L(R),R -> lr[b] */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o2 = olrr(REGTMP,r, p->to.reg, p->scond);
		if(p->as == AMOVBU || p->as == AMOVB)
			o2 |= 1<<22;
		if(o->type == 31)
			break;

		o3 = oprrr(ASLL, p->scond);

		if(p->as == AMOVBU || p->as == AMOVHU)
			o4 = oprrr(ASRL, p->scond);
		else
			o4 = oprrr(ASRA, p->scond);

		r = p->to.reg;
		o3 |= (r)|(r<<12);
		o4 |= (r)|(r<<12);
		if(p->as == AMOVB || p->as == AMOVBU) {
			o3 |= (24<<7);
			o4 |= (24<<7);
		} else {
			o3 |= (16<<7);
			o4 |= (16<<7);
		}
		break;

	case 33:	/* movh/movhu R,L(R) -> sb, sb */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o2 = osrr(p->from.reg, REGTMP, r, p->scond);
		o2 |= (1<<22) ;

		o3 = oprrr(ASRL, p->scond);
		o3 |= (8<<7)|(p->from.reg)|(p->from.reg<<12);
		o3 |= (1<<6);	/* ROR 8 */

		o4 = oprrr(AADD, p->scond);
		o4 |= (REGTMP << 12) | (REGTMP << 16);
		o4 |= immrot(1);

		o5 = osrr(p->from.reg, REGTMP,r,p->scond);
		o5 |= (1<<22);

		o6 = oprrr(ASRL, p->scond);
		o6 |= (24<<7)|(p->from.reg)|(p->from.reg<<12);
		o6 |= (1<<6);	/* ROL 8 */

		break;
		
	case 34:	/* mov $lacon,R */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;

		o2 = oprrr(AADD, p->scond);
		o2 |= REGTMP;
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o2 |= r << 16;
		if(p->to.type != D_NONE)
			o2 |= p->to.reg << 12;
		break;

	case 35:	/* mov PSR,R */
		o1 = (2<<23) | (0xf<<16) | (0<<0);
		o1 |= (p->scond & C_SCOND) << 28;
		o1 |= (p->from.reg & 1) << 22;
		o1 |= p->to.reg << 12;
		break;

	case 36:	/* mov R,PSR */
		o1 = (2<<23) | (0x29f<<12) | (0<<4);
		if(p->scond & C_FBIT)
			o1 ^= 0x010 << 12;
		o1 |= (p->scond & C_SCOND) << 28;
		o1 |= (p->to.reg & 1) << 22;
		o1 |= p->from.reg << 0;
		break;

	case 37:	/* mov $con,PSR */
		aclass(&p->from);
		o1 = (2<<23) | (0x29f<<12) | (0<<4);
		if(p->scond & C_FBIT)
			o1 ^= 0x010 << 12;
		o1 |= (p->scond & C_SCOND) << 28;
		o1 |= immrot(instoffset);
		o1 |= (p->to.reg & 1) << 22;
		o1 |= p->from.reg << 0;
		break;

	case 38:	/* movm $con,oreg -> stm */
		o1 = (0x4 << 25);
		o1 |= p->from.offset & 0xffff;
		o1 |= p->to.reg << 16;
		aclass(&p->to);
		goto movm;

	case 39:	/* movm oreg,$con -> ldm */
		o1 = (0x4 << 25) | (1 << 20);
		o1 |= p->to.offset & 0xffff;
		o1 |= p->from.reg << 16;
		aclass(&p->from);
	movm:
		if(instoffset != 0)
			diag("offset must be zero in MOVM");
		o1 |= (p->scond & C_SCOND) << 28;
		if(p->scond & C_PBIT)
			o1 |= 1 << 24;
		if(p->scond & C_UBIT)
			o1 |= 1 << 23;
		if(p->scond & C_SBIT)
			o1 |= 1 << 22;
		if(p->scond & C_WBIT)
			o1 |= 1 << 21;
		break;

	case 40:	/* swp oreg,reg,reg */
		aclass(&p->from);
		if(instoffset != 0)
			diag("offset must be zero in SWP");
		o1 = (0x2<<23) | (0x9<<4);
		if(p->as != ASWPW)
			o1 |= 1 << 22;
		o1 |= p->from.reg << 16;
		o1 |= p->reg << 0;
		o1 |= p->to.reg << 12;
		o1 |= (p->scond & C_SCOND) << 28;
		if(!debug['5'])
			diag("SWP instruction used\n%P", p);
		break;

	case 41:	/* rfe -> movm.s.w.u 0(r13),[r15] */
		o1 = 0xe8fd8000;
		break;

	case 50:	/* floating point store */
		v = regoff(&p->to);
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o1 = ofsr(p->as, p->from.reg, v, r, p->scond, p);
		break;

	case 51:	/* floating point load */
		v = regoff(&p->from);
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o1 = ofsr(p->as, p->to.reg, v, r, p->scond, p) | (1<<20);
		break;

	case 52:	/* floating point store, long offset UGLY */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o2 = oprrr(AADD, p->scond) | (REGTMP << 12) | (REGTMP << 16) | r;
		o3 = ofsr(p->as, p->from.reg, 0, REGTMP, p->scond, p);
		break;

	case 53:	/* floating point load, long offset UGLY */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o2 = oprrr(AADD, p->scond) | (REGTMP << 12) | (REGTMP << 16) | r;
		o3 = ofsr(p->as, p->to.reg, 0, REGTMP, p->scond, p) | (1<<20);
		break;

	case 54:	/* old floating point arith */
		o1 = oprrr(p->as, p->scond);
		if(p->from.type == D_FCONST) {
			rf = chipfloat(p->from.ieee);
			if(rf < 0){
				diag("invalid floating-point immediate\n%P", p);
				rf = 0;
			}
			rf |= (1<<3);
		} else
			rf = p->from.reg;
		rt = p->to.reg;
		r = p->reg;
		if(p->to.type == D_NONE)
			rt = 0;	/* CMP[FD] */
		else if(o1 & (1<<15))
			r = 0;	/* monadic */
		else if(r == NREG)
			r = rt;
		o1 |= rf | (r<<16) | (rt<<12);
		break;

	case 55:	/* floating point fix and float */
		o1 = oprrr(p->as, p->scond);
		rf = p->from.reg;
		rt = p->to.reg;
		if(p->to.type == D_NONE){
			rt = 0;
			diag("to.type==D_NONE (asm/fp)");
		}
		if(p->from.type == D_REG)
			o1 |= (rf<<12) | (rt<<16);
		else
			o1 |= rf | (rt<<12);
		break;

	/* old arm 7500 fp using coproc 1 (1<<8) */
	case 56:	/* move to FP[CS]R */
		o1 = ((p->scond & C_SCOND) << 28) | (0xe << 24) | (1<<8) | (1<<4);
		o1 |= ((p->to.reg+1)<<21) | (p->from.reg << 12);
		break;

	case 57:	/* move from FP[CS]R */
		o1 = ((p->scond & C_SCOND) << 28) | (0xe << 24) | (1<<8) | (1<<4);
		o1 |= ((p->from.reg+1)<<21) | (p->to.reg<<12) | (1<<20);
		break;
	case 58:	/* movbu R,R */
		o1 = oprrr(AAND, p->scond);
		o1 |= immrot(0xff);
		rt = p->to.reg;
		r = p->from.reg;
		if(p->to.type == D_NONE)
			rt = 0;
		if(r == NREG)
			r = rt;
		o1 |= (r<<16) | (rt<<12);
		break;

	case 59:	/* movw/bu R<<I(R),R -> ldr indexed */
		if(p->from.reg == NREG) {
			if(p->as != AMOVW)
				diag("byte MOV from shifter operand");
			goto mov;
		}
		if(p->from.offset&(1<<4))
			diag("bad shift in LDR");
		o1 = olrr(p->from.offset, p->from.reg, p->to.reg, p->scond);
		if(p->as == AMOVBU)
			o1 |= 1<<22;
		break;

	case 60:	/* movb R(R),R -> ldrsb indexed */
		if(p->from.reg == NREG) {
			diag("byte MOV from shifter operand");
			goto mov;
		}
		if(p->from.offset&(~0xf))
			diag("bad shift in LDRSB");
		o1 = olhrr(p->from.offset, p->from.reg, p->to.reg, p->scond);
		o1 ^= (1<<5)|(1<<6);
		break;

	case 61:	/* movw/b/bu R,R<<[IR](R) -> str indexed */
		if(p->to.reg == NREG)
			diag("MOV to shifter operand");
		o1 = osrr(p->from.reg, p->to.offset, p->to.reg, p->scond);
		if(p->as == AMOVB || p->as == AMOVBU)
			o1 |= 1<<22;
		break;

	case 62:	/* case R -> movw	R<<2(PC),PC */
		o1 = olrr(p->from.reg, REGPC, REGPC, p->scond);
		o1 |= 2<<7;
		break;

	case 63:	/* bcase */
		if(p->cond != P) {
			o1 = p->cond->pc;
			if(dlm)
				dynreloc(S, p->pc, 1);
		}
		break;

	/* reloc ops */
	case 64:	/* mov/movb/movbu R,addr */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		o2 = osr(p->as, p->from.reg, 0, REGTMP, p->scond);
		break;

	case 65:	/* mov/movbu addr,R */
	case 66:	/* movh/movhu/movb addr,R */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;
		o2 = olr(0, REGTMP, p->to.reg, p->scond);
		if(p->as == AMOVBU || p->as == AMOVB)
			o2 |= 1<<22;
		if(o->type == 65)
			break;

		o3 = oprrr(ASLL, p->scond);

		if(p->as == AMOVBU || p->as == AMOVHU)
			o4 = oprrr(ASRL, p->scond);
		else
			o4 = oprrr(ASRA, p->scond);

		r = p->to.reg;
		o3 |= (r)|(r<<12);
		o4 |= (r)|(r<<12);
		if(p->as == AMOVB || p->as == AMOVBU) {
			o3 |= (24<<7);
			o4 |= (24<<7);
		} else {
			o3 |= (16<<7);
			o4 |= (16<<7);
		}
		break;

	case 67:	/* movh/movhu R,addr -> sb, sb */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		o2 = osr(p->as, p->from.reg, 0, REGTMP, p->scond);

		o3 = oprrr(ASRL, p->scond);
		o3 |= (8<<7)|(p->from.reg)|(p->from.reg<<12);
		o3 |= (1<<6);	/* ROR 8 */

		o4 = oprrr(AADD, p->scond);
		o4 |= (REGTMP << 12) | (REGTMP << 16);
		o4 |= immrot(1);

		o5 = osr(p->as, p->from.reg, 0, REGTMP, p->scond);

		o6 = oprrr(ASRL, p->scond);
		o6 |= (24<<7)|(p->from.reg)|(p->from.reg<<12);
		o6 |= (1<<6);	/* ROL 8 */
		break;

	case 68:	/* floating point store -> ADDR */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		o2 = ofsr(p->as, p->from.reg, 0, REGTMP, p->scond, p);
		break;

	case 69:	/* floating point load <- ADDR */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;
		o2 = ofsr(p->as, p->to.reg, 0, REGTMP, p->scond, p) | (1<<20);
		break;

	/* ArmV4 ops: */
	case 70:	/* movh/movhu R,O(R) -> strh */
		aclass(&p->to);
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o1 = oshr(p->from.reg, instoffset, r, p->scond);
		break;	
	case 71:	/* movb/movh/movhu O(R),R -> ldrsb/ldrsh/ldrh */
		aclass(&p->from);
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o1 = olhr(instoffset, r, p->to.reg, p->scond);
		if(p->as == AMOVB)
			o1 ^= (1<<5)|(1<<6);
		else if(p->as == AMOVH)
			o1 ^= (1<<6);
		break;
	case 72:	/* movh/movhu R,L(R) -> strh */
		o1 = omvl(p, &p->to, REGTMP);
		if(!o1)
			break;
		r = p->to.reg;
		if(r == NREG)
			r = o->param;
		o2 = oshrr(p->from.reg, REGTMP,r, p->scond);
		break;	
	case 73:	/* movb/movh/movhu L(R),R -> ldrsb/ldrsh/ldrh */
		o1 = omvl(p, &p->from, REGTMP);
		if(!o1)
			break;
		r = p->from.reg;
		if(r == NREG)
			r = o->param;
		o2 = olhrr(REGTMP, r, p->to.reg, p->scond);
		if(p->as == AMOVB)
			o2 ^= (1<<5)|(1<<6);
		else if(p->as == AMOVH)
			o2 ^= (1<<6);
		break;

	/* VFP ops: */
	case 74:	/* vfp floating point arith */
		o1 = opvfprrr(p->as, p->scond);
		rf = p->from.reg;
		rt = p->to.reg;
		r = p->reg;
		if(r == NREG)
			r = rt;
		if(((o1>>20)&0xf) == 0xb)
			r = 0;	/* monadic */
		o1 = ovfpr(o1, r, rt, rf, 0);
		break;
	case 75:	/* vfp floating point compare */
		o1 = opvfprrr(p->as, p->scond);
		rf = p->from.reg;
		if(p->from.type == D_FCONST) {
			if(p->from.ieee->h != 0 || p->from.ieee->l != 0)
				diag("invalid floating-point immediate\n%P", p);
			o1 |= 1<<16;
			rf = 0;
		}
		rt = p->reg;
		o1 = ovfpr(o1, 0, rt, rf, 0);
		o2 = 0x0ef1fa10;	/* MRS APSR_nzcv, FPSCR */
		o2 |= (p->scond & C_SCOND) << 28;
		break;
	case 76:	/* vfp floating point fix and float */
		rf = p->from.reg;
		rt = p->to.reg;
		if(p->from.type == D_REG) {
			o1 = 0x0e000a10;	/* VMOV S,R (single precision) */
			o1 |= (p->scond & C_SCOND) << 28;
			o1 |= rf<<12 | rt<<16;
			o2 = opvfprrr(p->as, p->scond);
			o2 = ovfpr(o2, 0, rt, 0, 0) | rt;
		} else {
			o1 = opvfprrr(p->as, p->scond);
			o1 = ovfpr(o1, 0, 0, rf, 0) | FREGTMP<<12;
			o2 = 0x0e100a10;	/* VMOV R,S */
			o2 |= (p->scond & C_SCOND) << 28;
			o2 |= rt<<12 | FREGTMP<<16;
		}
		break;

	case 77:	/* eret/wfe/wfi */
		o1 = oprrr(p->as, p->scond);
		break;

	case 78:	/* cps $con */
		o1 = 0xf102<<16;
		o1 |= p->from.offset & 0x1f;
		break;
	case 79:	/* cpsid/cpsie iflags[,$con] */
		o1 = 0xf1<<24;
		if(p->as == ACPSID)
			o1 |= 3<<18;
		else	/* ACPSIE */
			o1 |= 2<<18;
		o1 |= p->from.offset;
		if(p->to.reg != NREG){
			o1 |= 1<<17;
			o1 |= p->to.offset & 0x1f;
		}
		break;

	case 80:	/* dmb/dsb/isb limit */
		o1 = 0xf57ff04<<4;
		if(p->as == AISB)
			o1 |= 1<<5;
		else if(p->as == ADMB)
			o1 |= 1<<4;
		r = 0xf;
		if(p->from.type == D_CONST)
			r = p->from.offset & 0xf;
		o1 |= r;
		break;

	case 81:	/* clz reg,reg */
		o1 = oprrr(p->as, p->scond);
		rf = p->from.reg;
		rt = p->to.reg;
		o1 |= rt<<12 | rf;
		break;

	case 82:	/* ldrex (reg),reg*/
		aclass(&p->from);
		if(instoffset != 0)
			diag("offset must be zero in LDREX");
		o1 = oprrr(p->as, p->scond);
		o1 |= p->from.reg << 16;
		o1 |= p->to.reg << 12;
		break;
	case 83:	/* strex reg,(reg),reg*/
		aclass(&p->from);
		if(instoffset != 0)
			diag("offset must be zero in STREX");
		o1 = oprrr(p->as, p->scond);
		o1 |= p->from.reg << 16;
		o1 |= p->reg << 0;
		o1 |= p->to.reg << 12;
		break;

	case 84:	/* vmsr, move to VFP control */
		o1 = ((p->scond & C_SCOND) << 28) | (0xee << 20) | (0xA<<8) | (1<<4);
		o1 |= (p->to.reg<<16) | (p->from.reg << 12);
		break;
	case 85:	/* vmrs, move from VFP control */
		if(p->to.type == D_PSR) {
			if(p->to.reg != 0 || p->from.reg != 1)
				diag("can only move FPSCR to PSR");
			p->to.reg = 15;	/* special encoding of APSR_nzcv */
		}
		o1 = ((p->scond & C_SCOND) << 28) | (0xef << 20) | (0xA<<8) | (1<<4);
		o1 |= (p->from.reg<<16) | (p->to.reg<<12);
		break;

	case 86:	/* fmov zfcon,freg */
		if(p->as == AMOVD) {
			o1 = 0x0eb00b00;	// VMOV imm 64
			o2 = opvfprrr(ASUBD, p->scond);
		} else {
			o1 = 0x0eb00a00;	// VMOV imm 32
			o2 = opvfprrr(ASUBF, p->scond);
		}
		v = 0x70;	// 1.0
		r = p->to.reg;

		// movf $1.0, r
		o1 |= (p->scond & C_SCOND) << 28;
		o1 |= (v&0xf) << 0;
		o1 |= (v&0xf0) << 12;
		o1 = ovfpr(o1, 0, r, 0, 0);

		// subf r,r,r
		o2 = ovfpr(o2, r, r, r, 0);
		break;
	case 87:	/* fmov sfcon,freg */
		o1 = 0xe<<24 | 0xb<<20 | 0xa<<8 | 0 << 6;	/* VMOV imm */
		if(p->as == AMOVD)
			o1 |= 1<<8;
		o1 |= (p->scond & C_SCOND) << 28;
		v = chipfloat(p->from.ieee);
		o1 |= (v&0xf) << 0;
		o1 |= (v&0xf0) << 12;
		o1 = ovfpr(o1, 0, p->to.reg, 0, 0);
		break;
	case 88:	/* fmov lfcon,freg */
		o1 = ofmvl(p, &p->from, p->to.reg);
		break;

	case 91:	/* push $regs */
		if(p->scond & (C_UBIT|C_PBIT|C_WBIT))
			diag("illegal .IA/.IB/.W on push");
		/* fall through */
	case 89:	/* movmf $con,oreg -> vstm */
		checkfpregs(p, p->from.offset, &lo, &hi);
		o1 = ofstm(p->as, p->scond);
		o1 = ovfpr(o1, 0, lo, 0, 1);
		if(p->to.reg != NREG)
			o1 |= p->to.reg << 16;
		r = hi-lo+1;
		if(o1 & (1<<8))
			r *= 2;
		o1 |= r;
		aclass(&p->to);
		if(instoffset != 0)
			diag("offset must be zero in MOVMF");
		break;

	case 92:	/* pop $regs */
		if(p->scond & (C_UBIT|C_PBIT|C_WBIT))
			diag("illegal .IA/.IB/.W on pop");
		/* fall through */
	case 90:	/* movmf oreg,$con -> vldm */
		checkfpregs(p, p->to.offset, &lo, &hi);
		o1 = ofstm(p->as, p->scond) | (1<<20);
		o1 = ovfpr(o1, 0, lo, 0, 1);
		if(p->from.reg != NREG)
			o1 |= p->from.reg << 16;
		r = hi-lo+1;
		if(o1 & (1<<8))
			r *= 2;
		o1 |= r;
		aclass(&p->from);
		if(instoffset != 0)
			diag("offset must be zero in MOVMF");
		break;
	}

	if(debug['a'] > 1)
		Bprint(&bso, "%2d ", o->type);

	v = p->pc;
	switch(o->size) {
	default:
		if(debug['a'])
			Bprint(&bso, " %.8lux:\t\t%P\n", v, p);
		break;
	case 4:
		if(debug['a'])
			Bprint(&bso, " %.8lux: %.8lux\t%P\n", v, o1, p);
		lputl(o1);
		break;
	case 8:
		if(debug['a'])
			Bprint(&bso, " %.8lux: %.8lux %.8lux%P\n", v, o1, o2, p);
		lputl(o1);
		lputl(o2);
		break;
	case 12:
		if(debug['a'])
			Bprint(&bso, " %.8lux: %.8lux %.8lux %.8lux%P\n", v, o1, o2, o3, p);
		lputl(o1);
		lputl(o2);
		lputl(o3);
		break;
	case 16:
		if(debug['a'])
			Bprint(&bso, " %.8lux: %.8lux %.8lux %.8lux %.8lux%P\n",
				v, o1, o2, o3, o4, p);
		lputl(o1);
		lputl(o2);
		lputl(o3);
		lputl(o4);
		break;
	case 20:
		if(debug['a'])
			Bprint(&bso, " %.8lux: %.8lux %.8lux %.8lux %.8lux %.8lux%P\n",
				v, o1, o2, o3, o4, o5, p);
		lputl(o1);
		lputl(o2);
		lputl(o3);
		lputl(o4);
		lputl(o5);
		break;
	case 24:
		if(debug['a'])
			Bprint(&bso, " %.8lux: %.8lux %.8lux %.8lux %.8lux %.8lux %.8lux%P\n",
				v, o1, o2, o3, o4, o5, o6, p);
		lputl(o1);
		lputl(o2);
		lputl(o3);
		lputl(o4);
		lputl(o5);
		lputl(o6);
		break;
	}
}

long
oprrr(int a, int sc)
{
	long o;

	o = (sc & C_SCOND) << 28;
	if(sc & C_SBIT)
		o |= 1 << 20;
	if(sc & (C_PBIT|C_WBIT))
		diag(".P/.W on dp instruction");
	switch(a) {
	case AMULU:
	case AMUL:	return o | (0x0<<21) | (0x9<<4);
	case AMULA:	return o | (0x1<<21) | (0x9<<4);
	case AMULLU:	return o | (0x4<<21) | (0x9<<4);
	case AMULL:	return o | (0x6<<21) | (0x9<<4);
	case AMULALU:	return o | (0x5<<21) | (0x9<<4);
	case AMULAL:	return o | (0x7<<21) | (0x9<<4);
	case AAND:	return o | (0x0<<21);
	case AEOR:	return o | (0x1<<21);
	case ASUB:	return o | (0x2<<21);
	case ARSB:	return o | (0x3<<21);
	case AADD:	return o | (0x4<<21);
	case AADC:	return o | (0x5<<21);
	case ASBC:	return o | (0x6<<21);
	case ARSC:	return o | (0x7<<21);
	case ATST:	return o | (0x8<<21) | (1<<20);
	case ATEQ:	return o | (0x9<<21) | (1<<20);
	case ACMP:	return o | (0xa<<21) | (1<<20);
	case ACMN:	return o | (0xb<<21) | (1<<20);
	case AORR:	return o | (0xc<<21);
	case AMOVW:	return o | (0xd<<21);
	case ABIC:	return o | (0xe<<21);
	case AMVN:	return o | (0xf<<21);
	case ASLL:	return o | (0xd<<21) | (0<<5);
	case ASRL:	return o | (0xd<<21) | (1<<5);
	case ASRA:	return o | (0xd<<21) | (2<<5);
	case ASWI:	return o | (0xf<<24);
	case AERET:	return o | (0x16<<20) | (3<<5) | (7<<1);
	case AWFE:	return o | (0x19<<21) | (0xf<<12) | (1<<1);
	case AWFI:	return o | (0x19<<21) | (0xf<<12) | (1<<1) | (1<<0);
	case ACLZ:	return o | (0x16<<20) | (0xf<<16) | (0xf<<8) | (1<<4);
	case ALDREX:	return o | (0x19<<20) | (0xf<<8) | (9<<4) | 0xf;
	case ALDREXB:	return o | (0x1d<<20) | (0xf<<8) | (9<<4) | 0xf;
	case ALDREXD:	return o | (0x1b<<20) | (0xf<<8) | (9<<4) | 0xf;
	case ALDREXH:	return o | (0x1f<<20) | (0xf<<8) | (9<<4) | 0xf;
	case ASTREX:	return o | (0x18<<20) | (0xf<<8) | (9<<4);
	case ASTREXB:	return o | (0x1c<<20) | (0xf<<8) | (9<<4);
	case ASTREXD:	return o | (0x1a<<20) | (0xf<<8) | (9<<4);
	case ASTREXH:	return o | (0x1e<<20) | (0xf<<8) | (9<<4);

	/* old arm 7500 fp using coproc 1 (1<<8) */
	case AADDD:	return o | (0xe<<24) | (0x0<<20) | (1<<8) | (1<<7);
	case AADDF:	return o | (0xe<<24) | (0x0<<20) | (1<<8);
	case AMULD:	return o | (0xe<<24) | (0x1<<20) | (1<<8) | (1<<7);
	case AMULF:	return o | (0xe<<24) | (0x1<<20) | (1<<8);
	case ASUBD:	return o | (0xe<<24) | (0x2<<20) | (1<<8) | (1<<7);
	case ASUBF:	return o | (0xe<<24) | (0x2<<20) | (1<<8);
	case ADIVD:	return o | (0xe<<24) | (0x4<<20) | (1<<8) | (1<<7);
	case ADIVF:	return o | (0xe<<24) | (0x4<<20) | (1<<8);
	case ACMPD:
	case ACMPF:	return o | (0xe<<24) | (0x9<<20) | (0xF<<12) | (1<<8) | (1<<4);	/* arguably, ACMPF should expand to RNDF, CMPD */

	case AMOVF:
	case AMOVDF:	return o | (0xe<<24) | (0x0<<20) | (1<<15) | (1<<8);
	case AMOVD:
	case AMOVFD:	return o | (0xe<<24) | (0x0<<20) | (1<<15) | (1<<8) | (1<<7);

	case AMOVWF:	return o | (0xe<<24) | (0<<20) | (1<<8) | (1<<4);
	case AMOVWD:	return o | (0xe<<24) | (0<<20) | (1<<8) | (1<<4) | (1<<7);
	case AMOVFW:	return o | (0xe<<24) | (1<<20) | (1<<8) | (1<<4);
	case AMOVDW:	return o | (0xe<<24) | (1<<20) | (1<<8) | (1<<4) | (1<<7);

	case ACLREX:	return (0x1E<<27) | (0x57<<20) | (0xFF<<12) | (1<<4) | 0xF;
	}
	diag("bad rrr %d", a);
	prasm(curp);
	return 0;
}

long
opvfprrr(int a, int sc)
{
	long o;

	o = (sc & C_SCOND) << 28;
	if(sc & (C_SBIT|C_PBIT|C_WBIT))
		diag(".S/.P/.W on vfp instruction");
	o |= 0xe<<24;
	switch(a) {
	case AMOVWD:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0x8<<16 | 1<<7;
	case AMOVWF:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0x8<<16 | 1<<7;
	case AMOVDW:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0xD<<16 | 1<<7;
	case AMOVFW:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0xD<<16 | 1<<7;
	case AMOVWDU:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0x8<<16 | 0<<7;
	case AMOVWFU:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0x8<<16 | 0<<7;
	case AMOVDWU:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0xC<<16 | 1<<7;
	case AMOVFWU:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0xC<<16 | 1<<7;
	case AMOVFD:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0x7<<16 | 1<<7;
	case AMOVDF:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0x7<<16 | 1<<7;
	case AMOVF:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0x0<<16 | 0<<7;
	case AMOVD:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0x0<<16 | 0<<7;
	case ACMPF:	return o | 0xa<<8 | 0xb<<20 | 1<<6 | 0x4<<16 | 0<<7;
	case ACMPD:	return o | 0xb<<8 | 0xb<<20 | 1<<6 | 0x4<<16 | 0<<7;
	case AADDF:	return o | 0xa<<8 | 0x3<<20;
	case AADDD:	return o | 0xb<<8 | 0x3<<20;
	case ASUBF:	return o | 0xa<<8 | 0x3<<20 | 1<<6;
	case ASUBD:	return o | 0xb<<8 | 0x3<<20 | 1<<6;
	case AMULF:	return o | 0xa<<8 | 0x2<<20;
	case AMULD:	return o | 0xb<<8 | 0x2<<20;
	case ADIVF:	return o | 0xa<<8 | 0x8<<20;
	case ADIVD:	return o | 0xb<<8 | 0x8<<20;
	case AABSF:	return o | 0xa<<8 | 0xb<<20 | 3<<6;
	case AABSD:	return o | 0xb<<8 | 0xb<<20 | 3<<6;
	case AMLAF:	return o | 0xa<<8 | 0x0<<20 | 0<<6;
	case AMLAD:	return o | 0xb<<8 | 0x0<<20 | 0<<6;
	case AMLSF:	return o | 0xa<<8 | 0x0<<20 | 1<<6;
	case AMLSD:	return o | 0xb<<8 | 0x0<<20 | 1<<6;
	case ANMULF:	return o | 0xa<<8 | 0x2<<20 | 1<<6;
	case ANMULD:  return o | 0xb<<8 | 0x2<<20 | 1<<6;
	case ANMLAF: return o | 0xa<<8 | 0x1<<20 | 1<<6;
	case ANMLAD: return o | 0xb<<8 | 0x1<<20 | 1<<6;
	case ANMLSF: return o | 0xa<<8 | 0x1<<20 | 0<<6;
	case ANMLSD: return o | 0xb<<8 | 0x1<<20 | 0<<6;
	case ASQRTF:	return o | 0xa<<8 | 0xb<<20 | 1<<16 | 3<<6;
	case ASQRTD:	return o | 0xb<<8 | 0xb<<20 | 1<<16 | 3<<6;
	case ANEGF:	return o | 0xa<<8 | 0xb<<20 | 1<<16 | 1<<6;
	case ANEGD:	return o | 0xb<<8 | 0xb<<20 | 1<<16 | 1<<6;
	}
	diag("bad vfp rrr %d", a);
	prasm(curp);
	return 0;
}

static long
ofstm(int a, int sc)
{
	long o;

	o = (sc & C_SCOND) << 28;
	if(sc & C_SBIT)
		diag(".S on vfp movmf instruction");
	if(sc & C_PBIT && sc & C_UBIT)
		diag("allowed only one of .IA/.DB");
	o |= 6<<25;
	if(sc & C_WBIT)
		o |= 1<<21;
	if(sc & C_PBIT)
		o |= 1<<24;
	if(sc & C_UBIT)
		o |= 1<<23;
	switch(a) {
	case AMOVMF:	return o | 5<<9;
	case AMOVMD:	return o | 5<<9 | 1<<8;
	case APUSHF:	return o | 0x12<<20 | REGSP<<16 | 5<<9;
	case APUSHD:	return o | 0x12<<20 | REGSP<<16 | 5<<9 | 1<<8;
	case APOPF:	return o | 0xb<<20 | REGSP<<16 | 5<<9;
	case APOPD:	return o | 0xb<<20 | REGSP<<16 | 5<<9 | 1<<8;
	}
	diag("bad vfp stm %A", a);
	prasm(curp);
	return 0;
}

long
opbra(int a, int sc)
{

	if(sc & (C_SBIT|C_PBIT|C_WBIT))
		diag(".S/.P/.W on bra instruction");
	sc &= C_SCOND;
	if(a == ABL)
		return (sc<<28)|(0x5<<25)|(0x1<<24);
	if(sc != 0xe)
		diag(".COND on bcond instruction");
	switch(a) {
	case ABEQ:	return (0x0<<28)|(0x5<<25);
	case ABNE:	return (0x1<<28)|(0x5<<25);
	case ABCS:	return (0x2<<28)|(0x5<<25);
	case ABHS:	return (0x2<<28)|(0x5<<25);
	case ABCC:	return (0x3<<28)|(0x5<<25);
	case ABLO:	return (0x3<<28)|(0x5<<25);
	case ABMI:	return (0x4<<28)|(0x5<<25);
	case ABPL:	return (0x5<<28)|(0x5<<25);
	case ABVS:	return (0x6<<28)|(0x5<<25);
	case ABVC:	return (0x7<<28)|(0x5<<25);
	case ABHI:	return (0x8<<28)|(0x5<<25);
	case ABLS:	return (0x9<<28)|(0x5<<25);
	case ABGE:	return (0xa<<28)|(0x5<<25);
	case ABLT:	return (0xb<<28)|(0x5<<25);
	case ABGT:	return (0xc<<28)|(0x5<<25);
	case ABLE:	return (0xd<<28)|(0x5<<25);
	case AB:	return (0xe<<28)|(0x5<<25);
	}
	diag("bad bra %A", a);
	prasm(curp);
	return 0;
}

long
olr(long v, int b, int r, int sc)
{
	long o;

	if(sc & C_SBIT)
		diag(".S on LDR/STR instruction");
	o = (sc & C_SCOND) << 28;
	if(!(sc & C_PBIT))
		o |= 1 << 24;
	if(!(sc & C_UBIT))
		o |= 1 << 23;
	if(sc & C_WBIT)
		o |= 1 << 21;
	o |= (0x1<<26) | (1<<20);
	if(v < 0) {
		v = -v;
		o ^= 1 << 23;
	}
	if(v >= (1<<12))
		diag("literal span too large: %ld (R%d)\n%P", v, b, PP);
	o |= v;
	o |= b << 16;
	o |= r << 12;
	return o;
}

long
olhr(long v, int b, int r, int sc)
{
	long o;

	if(sc & C_SBIT)
		diag(".S on LDRH/STRH instruction");
	o = (sc & C_SCOND) << 28;
	if(!(sc & C_PBIT))
		o |= 1 << 24;
	if(sc & C_WBIT)
		o |= 1 << 21;
	o |= (1<<23) | (1<<20)|(0xb<<4);
	if(v < 0) {
		v = -v;
		o ^= 1 << 23;
	}
	if(v >= (1<<8))
		diag("literal span too large: %ld (R%d)\n%P", v, b, PP);
	o |= (v&0xf)|((v>>4)<<8)|(1<<22);
	o |= b << 16;
	o |= r << 12;
	return o;
}

long
osr(int a, int r, long v, int b, int sc)
{
	long o;

	o = olr(v, b, r, sc) ^ (1<<20);
	if(a != AMOVW)
		o |= 1<<22;
	return o;
}

long
oshr(int r, long v, int b, int sc)
{
	long o;

	o = olhr(v, b, r, sc) ^ (1<<20);
	return o;
}

long
osrr(int r, int i, int b, int sc)
{

	return olr(i, b, r, sc) ^ ((1<<25) | (1<<20));
}

long
oshrr(int r, int i, int b, int sc)
{
	return olhr(i, b, r, sc) ^ ((1<<22) | (1<<20));
}

long
olrr(int i, int b, int r, int sc)
{

	return olr(i, b, r, sc) ^ (1<<25);
}

long
olhrr(int i, int b, int r, int sc)
{
	return olhr(i, b, r, sc) ^ (1<<22);
}

static long
ovfpr(long o, int rn, int rd, int rm, int forces)
{
	if((o & (1<<8)) == 0) {	/* single-precision puts low-order bit in D, M and N */
		if(!forces) {
			if(NFREG <= 16)
				return o | rn<<16 | rd<<12 | rm;	/* in single-precision, map Fn to S(2n) */
			diag("reference to register > F15 in single-precision not implemented");
		}
		rn = ((rn>>1)&0xf) | ((rn&1)<<4);
		rd = ((rd>>1)&0xf) | ((rd&1)<<4);
		rm = ((rm>>1)&0xf) | ((rm&1)<<4);
	}
	o |= (rn&0xf)<<16 | ((rn&0x10)<<(7-4));
	o |= (rd&0xf)<<12 | ((rd&0x10)<<(22-4));
	o |= (rm&0xf)<<0 | ((rm&0x10)<<(5-4));
	return o;
}

long
ovfpmem(int a, int r, long v, int b, int sc, Prog *p)
{
	long o;

	if(sc & (C_SBIT|C_PBIT|C_WBIT))
		diag(".S/.P/.W on VLDR/VSTR instruction");
	o = (sc & C_SCOND) << 28;
	o |= 0xd<<24 | (1<<23);
	if(v < 0) {
		v = -v;
		o ^= 1 << 23;
	}
	if(v & 3)
		diag("odd offset for floating point op: %ld\n%P", v, p);
	else if(v >= (1<<10))
		diag("literal span too large: %ld\n%P", v, p);
	o |= (v>>2) & 0xFF;
	o |= b << 16;
	switch(a) {
	default:
		diag("bad fst %A", a);
	case AMOVD:
		o |= 0xb<<8;
		break;
	case AMOVF:
		o |= 0xa<<8;
		break;
	}
	o = ovfpr(o, 0, r, 0, 0);
	return o;
}

long
ofsr(int a, int r, long v, int b, int sc, Prog *p)
{
	long o;

	if(vfp)
		return ovfpmem(a, r, v, b, sc, p);
	if(sc & C_SBIT)
		diag(".S on FLDR/FSTR instruction");
	o = (sc & C_SCOND) << 28;
	if(!(sc & C_PBIT))
		o |= 1 << 24;
	if(sc & C_WBIT)
		o |= 1 << 21;
	o |= (6<<25) | (1<<24) | (1<<23);
	if(v < 0) {
		v = -v;
		o ^= 1 << 23;
	}
	if(v & 3)
		diag("odd offset for floating point op: %ld\n%P", v, p);
	else if(v >= (1<<10))
		diag("literal span too large: %ld\n%P", v, p);
	o |= (v>>2) & 0xFF;
	o |= b << 16;
	o |= r << 12;
	o |= 1 << 8;

	switch(a) {
	default:
		diag("bad fst %A", a);
	case AMOVD:
		o |= 1<<15;
	case AMOVF:
		break;
	}
	return o;
}

static long
movt(int sc, long v, int dr)
{
	long o;

	v >>= 16;
	o = (sc&C_SCOND)<<28 | (3<<24) | (4<<20);
	o |= (v&0xF000)<<4 | (v&0x0FFF);
	o |= dr << 12;
	return o;
}

long
omvl(Prog *p, Adr *a, int dr)
{	
	long v, o1;
	if(p->cond == nil) {
		aclass(a);
		v = immrot(~instoffset);
		if(v == 0) {
			diag("missing literal");
			prasm(p);
			return 0;
		}
		o1 = oprrr(AMVN, p->scond&C_SCOND);
		o1 |= v;
		o1 |= dr << 12;
	} else {
		v = p->cond->pc - p->pc - 8;
		o1 = olr(v, REGPC, dr, p->scond&C_SCOND);
	}
	return o1;
}

static long
ofmvl(Prog *p, Adr *a, int dr)
{	
	long v;

	USED(a);
	if(p->cond == nil)
		diag("missing literal\n%P", p);
	v = p->cond->pc - p->pc - 8;
	return ofsr(p->as, dr, v, REGPC, p->scond&C_SCOND, p) | (1<<20);
}

static Ieee chipfloats[] = {
	{0x00000000, 0x00000000}, /* 0 */
	{0x00000000, 0x3ff00000}, /* 1 */
	{0x00000000, 0x40000000}, /* 2 */
	{0x00000000, 0x40080000}, /* 3 */
	{0x00000000, 0x40100000}, /* 4 */
	{0x00000000, 0x40140000}, /* 5 */
	{0x00000000, 0x3fe00000}, /* .5 */
	{0x00000000, 0x40240000}, /* 10 */
};

int
chipfloat(Ieee *e)
{
	Ieee *p;
	int n, ex, b;

	if(vfp) {
		ex = (e->h>>20)&0x7FF;
		b = ex>>2;
		if(e->l == 0 && (e->h&0xFF) == 0 && (b == 0x100 || b == 0xFF)){
			n = ((e->h>>24)&0x80) | (ex&0x40) | ((ex&0x3)<<4) | ((e->h>>16)&0xF);
			//print("%#.2ux\n", n);
			return n;
		}
		return -1;
	}
	for(n = sizeof(chipfloats)/sizeof(chipfloats[0]); --n >= 0;){
		p = &chipfloats[n];
		if(p->l == e->l && p->h == e->h)
			return n;
	}
	return -1;
}

static void
checkfpregs(Prog *p, ulong regs, int *min, int *max)
{
	int i, lim;

	/* no gaps allowed */
	lim = p->as == APUSHF || p->as == APOPF || p->as == AMOVMF? 32: 16;
	*min = *max = 0;
	for(i = 0; i < lim; i++) {
		if(regs & (1<<i)) {
			*min = i;
			for(; i < lim && (regs & (1<<i)) != 0; i++)
				*max = i;
			for(;; i++) {
				if(i >= lim)
					return;
				if(regs & (1<<i))
					break;
			}
			break;
		}
	}
	diag("invalid floating-point register set\n%P", p);
}
