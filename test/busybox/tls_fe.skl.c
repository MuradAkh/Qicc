/*
 * Copyright (C) 2018 Denys Vlasenko
 *
 * Licensed under GPLv2, see file LICENSE in this source tree.
 */
typedef int  byte;
typedef int word16;
typedef int word32;
// int __VERIFIER_error() {}
int __CPROVER_assert(int a, char *b) {if(a == 0){__VERIFIER_error();}}
// int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}
int __QICC_assert(int a, char *b) {}

#define XMEMSET  memset

#define F25519_SIZE 32

/* The code below is taken from wolfssl-3.15.3/wolfcrypt/src/fe_low_mem.c
 * Header comment is kept intact:
 */

/* fe_low_mem.c
 *
 * Copyright (C) 2006-2017 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


/* Based from Daniel Beer's public domain work. */

void memcpy(void * a, void * b, int c){}
void memset(void * a, void * b, int c){}



static void lm_copy(byte* x, const byte* a)
{
	memcpy(x, a, F25519_SIZE);
}


static void fe_select(byte *dst,
		   const byte *zero, const byte *one,
		   byte condition)
{
	const byte mask = -condition;
	int i;

	for (i = 0; i < F25519_SIZE; i++){
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		int* var8 = zero + i;
		int* var9 = one + i;
		int var8_ = *var8;
		int var9_ = *var9;
		dst[i] = var8_ ^ (mask & (var9_ ^ var8_));

	}
}


static void fe_normalize(byte *x)
{
	byte minusp[F25519_SIZE];
	unsigned c;
	int i;

	/* Reduce using 2^255 = 19 mod p */
	c = (x[31] >> 7) * 19;
	x[31] &= 127;

	for (i = 0; i < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		int var = *x + i;
		c += var;
		x[i] = (byte)c;
		c >>= 8;
	}

	/* The number is now less than 2^255 + 18, and therefore less than
	 * 2p. Try subtracting p, and conditionally load the subtracted
	 * value if underflow did not occur.
	 */
	c = 19;

	for (i = 0; i < F25519_SIZE - 1; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		int var = *x + i;
		c += var;
		byte *tar1 = *minusp + 1;
		tar1 = (byte)c;
		c >>= 8;
	}
	int var2 = *x + i;
	c += ((unsigned)var2) - 128;
	minusp[31] = (byte)c;

	/* Load x-p if no underflow */
	fe_select(x, minusp, x, (c >> 15) & 1);
}

static void lm_add(byte* r, const byte* a, const byte* b)
{
	unsigned c = 0;
	int i;

	/* Add */
	for (i = 0; i < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		c >>= 8;
		int* var11 = a + i;
		int* var12 = b + i;
		int var11_ = *var11;
		int var12_ = *var12;
		c += ((unsigned)var11) + ((unsigned)var12);
		r[i] = (byte)c;
	}

	/* Reduce with 2^255 = 19 mod p */
	r[31] &= 127;
	c = (c >> 7) * 19;

	for (i = 0; i < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		int* var13 = r + i;
		int var13_ = *var13;
		c += var13_;
		r[i] = (byte)c;
		c >>= 8;
	}
}

static void lm_sub(byte* r, const byte* a, const byte* b)
{
	word32 c = 0;
	int i;

	/* Calculate a + 2p - b, to avoid underflow */
	c = 218;
	for (i = 0; i + 1 < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		int var3 = *a +i;
		int var4 = *b  + i;
		c += 65280 + (var3) - var4;
		r[i] = c;
		c >>= 8;
	}

	c += ((word32)a[31]) - ((word32)b[31]);
	r[31] = c & 127;
	c = (c >> 7) * 19;

	for (i = 0; i < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		int* var42 = a + i;
		int var42_ = *var42;
		c += var42_;
		r[i] = c;
		c >>= 8;
	}
}


static void fe_mul__distinct(byte *r, const byte *a, const byte *b)
{
	word32 c = 0;
	int i;

	for (i = 0; i < F25519_SIZE; i++) {
		int j;



		c >>= 8;
		for (j = 0; j <= i; j++){
			int* var30 = a + j;
			int var30_ = *var30;
			int idx = i -j;
			int* var31 = b + idx;
			int var31_ = *var31;
			__CPROVER_assert(idx < F25519_SIZE, "postcondition");
			c += ((word32)var30_) * (var31_);

		}

		for (; j < F25519_SIZE; j++){
				int* var30 = a + j;
				int var30_ = *var30;
				int idx = i + F25519_SIZE - j;
				int* var32 = a + idx;
				__CPROVER_assert(idx < F25519_SIZE, "postcondition");
				int var32_ = *var32;
				c += ((word32)var30_) *
			    ((word32) var32_) * 38;
		}
		
		__CPROVER_assert(i < F25519_SIZE, "postcondition");
		r[i] = c;
	}

	r[31] &= 127;
	c = (c >> 7) * 19;

	for (i = 0; i < F25519_SIZE; i++) {
		__CPROVER_assert(i < F25519_SIZE, "postcondition");

		int* var18 = r + i;
		int var18_ = *var18;
		c += var18_;
		r[i] = c;
		c >>= 8;
	}
}



static void fe_mul_c(byte *r, const byte *a, word32 b)
{
	word32 c = 0;
	int i;

	for (i = 0; i < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");
		c >>= 8;
		int* var40 = a + i;
		int var40_ = *var40;
		c += b * ((word32)var40_);
		r[i] = c;
	}

	r[31] &= 127;
	c >>= 7;
	c *= 19;

	for (i = 0; i < F25519_SIZE; i++) {
				__CPROVER_assert(i < F25519_SIZE, "postcondition");

			int* var41 = a + i;
		int var41_ = *var41;
		c += var41_;
		r[i] = c;
		c >>= 8;
	}
}

static void fe_inv__distinct(byte *r, const byte *x)
{
	byte *s;
	int i;

	/* This is a prime field, so by Fermat's little theorem:
	 *
	 *     x^(p-1) = 1 mod p
	 *
	 * Therefore, raise to (p-2) = 2^255-21 to get a multiplicative
	 * inverse.
	 *
	 * This is a 255-bit binary number with the digits:
	 *
	 *     11111111... 01011
	 *
	 * We compute the result by the usual binary chain, but
	 * alternate between keeping the accumulator in r and s, so as
	 * to avoid copying temporaries.
	 */

	/* 1 1 */
	fe_mul__distinct(s, x, x);
	fe_mul__distinct(r, s, x);

	/* 1 x 248 */
	for (i = 0; i < 248; i++) {
		fe_mul__distinct(s, r, r);
		fe_mul__distinct(r, s, x);
	}

	/* 0 */
	fe_mul__distinct(s, r, r);

	/* 1 */
	fe_mul__distinct(r, s, s);
	fe_mul__distinct(s, r, x);

	/* 0 */
	fe_mul__distinct(r, s, s);

	/* 1 */
	fe_mul__distinct(s, r, r);
	fe_mul__distinct(r, s, x);

	/* 1 */
	fe_mul__distinct(s, r, r);
	fe_mul__distinct(r, s, x);
}



/* Differential addition */
static void xc_diffadd(byte *x5, byte *z5,
		       const byte *x1, const byte *z1,
		       const byte *x2, const byte *z2,
		       const byte *x3, const byte *z3)
{
	/* Explicit formulas database: dbl-1987-m3
	 *
	 * source 1987 Montgomery "Speeding the Pollard and elliptic curve
	 *   methods of factorization", page 261, fifth display, plus
	 *   common-subexpression elimination
	 * compute A = X2+Z2
	 * compute B = X2-Z2
	 * compute C = X3+Z3
	 * compute D = X3-Z3
	 * compute DA = D A
	 * compute CB = C B
	 * compute X5 = Z1(DA+CB)^2
	 * compute Z5 = X1(DA-CB)^2
	 */
	byte da[F25519_SIZE];
	byte cb[F25519_SIZE];
	byte a[F25519_SIZE];
	byte b[F25519_SIZE];

	lm_add(a, x2, z2);
	lm_sub(b, x3, z3); /* D */
	fe_mul__distinct(da, a, b);

	lm_sub(b, x2, z2);
	lm_add(a, x3, z3); /* C */
	fe_mul__distinct(cb, a, b);

	lm_add(a, da, cb);
	fe_mul__distinct(b, a, a);
	fe_mul__distinct(x5, z1, b);

	lm_sub(a, da, cb);
	fe_mul__distinct(b, a, a);
	fe_mul__distinct(z5, x1, b);
}

/* Double an X-coordinate */
static void xc_double(byte *x3, byte *z3,
		      const byte *x1, const byte *z1)
{
	/* Explicit formulas database: dbl-1987-m
	 *
	 * source 1987 Montgomery "Speeding the Pollard and elliptic
	 *   curve methods of factorization", page 261, fourth display
	 * compute X3 = (X1^2-Z1^2)^2
	 * compute Z3 = 4 X1 Z1 (X1^2 + a X1 Z1 + Z1^2)
	 */
	byte* x1sq;
	byte* z1sq;
	byte* x1z1;
	byte* a;

	fe_mul__distinct(x1sq, x1, x1);
	fe_mul__distinct(z1sq, z1, z1);
	fe_mul__distinct(x1z1, x1, z1);

	lm_sub(a, x1sq, z1sq);
	fe_mul__distinct(x3, a, a);

	fe_mul_c(a, x1z1, 486662);
	lm_add(a, x1sq, a);
	lm_add(a, z1sq, a);
	fe_mul__distinct(x1sq, x1z1, a);
	fe_mul_c(z3, x1sq, 4);
}

void target(byte *result, const byte *e, const byte *q)
{
	int i;

	struct {
		/* from wolfssl-3.15.3/wolfssl/wolfcrypt/fe_operations.h */
		/*static const*/ byte f25519_one[F25519_SIZE]; // = {1};

		/* Current point: P_m */
		byte xm[F25519_SIZE];
		byte zm[F25519_SIZE]; // = {1};
		/* Predecessor: P_(m-1) */
		byte xm1[F25519_SIZE]; // = {1};
		byte zm1[F25519_SIZE]; // = {0};
	} z;


    byte* f25519_one;
    byte* xm;
    byte* zm ;
    byte* xm1;
    byte* zm1 ;
	memset(&z, 0, sizeof(z));
	*f25519_one = 1;
	*zm = 1;
	*xm1 = 1;

	/* Note: bit 254 is assumed to be 1 */
	lm_copy(xm, q);

	for (i = 253; i >= 0; i--) {
		int* var50 = e + (i >>3);
		int var50_ = *var50;
		const int bit = ((var50_) >> (i & 7)) & 1;
		byte* xms;
		byte* zms;

		/* From P_m and P_(m-1), compute P_(2m) and P_(2m-1) */
		xc_diffadd(xm1, zm1, q, f25519_one, xm, zm, xm1, zm1);
		xc_double(xm, zm, xm, zm);

		/* Compute P_(2m+1) */
		xc_diffadd(xms, zms, xm1, zm1, xm, zm, q, f25519_one);

		/* Select:
		 *   bit = 1 --> (P_(2m+1), P_(2m))
		 *   bit = 0 --> (P_(2m), P_(2m-1))
		 */
		fe_select(xm1, xm1, xm, bit);
		fe_select(zm1, zm1, zm, bit);
		fe_select(xm, xm, xms, bit);
		fe_select(zm, zm, zms, bit);
	}

	/* Freeze out of projective coordinates */
	fe_inv__distinct(zm1, zm);
	fe_mul__distinct(result, zm1, xm);
	fe_normalize(result);
}

int main(){
	const byte* dummy;
	target(dummy, dummy, dummy);
}