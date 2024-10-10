#include <stdint.h>
#include <bits/stdc++.h>
#include <gmp.h>
#include <unistd.h>
using namespace std;

//---------------------------------------------------------FOR HASHING(SHA3)--------------------------------------------------------------
#define SHA3_KECCAK_SPONGE_WORDS \
	(((1600)/8/*bits to byte*/)/sizeof(uint64_t))
typedef struct sha3_context_ {
    uint64_t saved;             /* the portion of the input message that we
                                 * didn't consume yet */
    union {                     /* Keccak's state */
        uint64_t s[SHA3_KECCAK_SPONGE_WORDS];
        uint8_t sb[SHA3_KECCAK_SPONGE_WORDS * 8];
    } u;
    unsigned byteIndex;         /* 0..7--the next byte after the set one
                                 * (starts from 0; 0--none are buffered) */
    unsigned wordIndex;         /* 0..24--the next word to integrate input
                                 * (starts from 0) */
    unsigned capacityWords;     /* the double size of the hash output in
                                 * words (e.g. 16 for Keccak 512) */
} sha3_context;

enum SHA3_FLAGS {
    SHA3_FLAGS_NONE,
    SHA3_FLAGS_KECCAK,
};

enum SHA3_RETURN {
    SHA3_RETURN_OK,
    SHA3_RETURN_BAD_PARAMS,
};
typedef enum SHA3_RETURN sha3_return_t;

/* For Init or Reset call these: */
sha3_return_t sha3_Init(void *priv, unsigned bitSize);

void sha3_Init256(void *priv);
void sha3_Init384(void *priv);
void sha3_Init512(void *priv);

enum SHA3_FLAGS sha3_SetFlags(void *priv, enum SHA3_FLAGS);

void sha3_Update(void *priv, void const *bufIn, size_t len);

void const *sha3_Finalize(void *priv);

/* Single-call hashing */
sha3_return_t sha3_HashBuffer( 
    unsigned bitSize,   /* 256, 384, 512 */
    enum SHA3_FLAGS flags, /* SHA3_FLAGS_NONE or SHA3_FLAGS_KECCAK */
    const void *in, unsigned inBytes, 
    void *out, unsigned outBytes );     /* up to bitSize/8; truncation OK */

#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define SHA3_ASSERT( x )
#define SHA3_TRACE( format, ...)
#define SHA3_TRACE_BUF(format, buf, l)

/* 
 * This flag is used to configure "pure" Keccak, as opposed to NIST SHA3.
 */
#define SHA3_USE_KECCAK_FLAG 0x80000000
#define SHA3_CW(x) ((x) & (~SHA3_USE_KECCAK_FLAG))


#if defined(_MSC_VER)
#define SHA3_CONST(x) x
#else
#define SHA3_CONST(x) x##L
#endif

#ifndef SHA3_ROTL64
#define SHA3_ROTL64(x, y) \
	(((x) << (y)) | ((x) >> ((sizeof(uint64_t)*8) - (y))))
#endif


#ifndef SHA3_ROTL64
#define SHA3_ROTL64(x, y) \
	(((x) << (y)) | ((x) >> ((sizeof(uint64_t)*8) - (y))))
#endif

static const uint64_t keccakf_rndc[24] = {
    SHA3_CONST(0x0000000000000001UL), SHA3_CONST(0x0000000000008082UL),
    SHA3_CONST(0x800000000000808aUL), SHA3_CONST(0x8000000080008000UL),
    SHA3_CONST(0x000000000000808bUL), SHA3_CONST(0x0000000080000001UL),
    SHA3_CONST(0x8000000080008081UL), SHA3_CONST(0x8000000000008009UL),
    SHA3_CONST(0x000000000000008aUL), SHA3_CONST(0x0000000000000088UL),
    SHA3_CONST(0x0000000080008009UL), SHA3_CONST(0x000000008000000aUL),
    SHA3_CONST(0x000000008000808bUL), SHA3_CONST(0x800000000000008bUL),
    SHA3_CONST(0x8000000000008089UL), SHA3_CONST(0x8000000000008003UL),
    SHA3_CONST(0x8000000000008002UL), SHA3_CONST(0x8000000000000080UL),
    SHA3_CONST(0x000000000000800aUL), SHA3_CONST(0x800000008000000aUL),
    SHA3_CONST(0x8000000080008081UL), SHA3_CONST(0x8000000000008080UL),
    SHA3_CONST(0x0000000080000001UL), SHA3_CONST(0x8000000080008008UL)
};

static const unsigned keccakf_rotc[24] = {
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62,
    18, 39, 61, 20, 44
};

static const unsigned keccakf_piln[24] = {
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20,
    14, 22, 9, 6, 1
};

/* generally called after SHA3_KECCAK_SPONGE_WORDS-ctx->capacityWords words 
 * are XORed into the state s 
 */
static void
keccakf(uint64_t s[25])
{
    int i, j, round;
    uint64_t t, bc[5];
#define KECCAK_ROUNDS 24

    for(round = 0; round < KECCAK_ROUNDS; round++) {

        /* Theta */
        for(i = 0; i < 5; i++)
            bc[i] = s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20];

        for(i = 0; i < 5; i++) {
            t = bc[(i + 4) % 5] ^ SHA3_ROTL64(bc[(i + 1) % 5], 1);
            for(j = 0; j < 25; j += 5)
                s[j + i] ^= t;
        }

        /* Rho Pi */
        t = s[1];
        for(i = 0; i < 24; i++) {
            j = keccakf_piln[i];
            bc[0] = s[j];
            s[j] = SHA3_ROTL64(t, keccakf_rotc[i]);
            t = bc[0];
        }

        /* Chi */
        for(j = 0; j < 25; j += 5) {
            for(i = 0; i < 5; i++)
                bc[i] = s[j + i];
            for(i = 0; i < 5; i++)
                s[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
        }

        /* Iota */
        s[0] ^= keccakf_rndc[round];
    }
}

/* *************************** Public Inteface ************************ */

/* For Init or Reset call these: */
sha3_return_t
sha3_Init(void *priv, unsigned bitSize) {
    sha3_context *ctx = (sha3_context *) priv;
    if( bitSize != 256 && bitSize != 384 && bitSize != 512 )
        return SHA3_RETURN_BAD_PARAMS;
    memset(ctx, 0, sizeof(*ctx));
    ctx->capacityWords = 2 * bitSize / (8 * sizeof(uint64_t));
    return SHA3_RETURN_OK;
}

void
sha3_Init256(void *priv)
{
    sha3_Init(priv, 256);
}

void
sha3_Init384(void *priv)
{
    sha3_Init(priv, 384);
}

void
sha3_Init512(void *priv)
{
    sha3_Init(priv, 512);
}

enum SHA3_FLAGS
sha3_SetFlags(void *priv, enum SHA3_FLAGS flags1)
{
    sha3_context *ctx = (sha3_context *) priv;
    flags1 =  SHA3_FLAGS_KECCAK;
    ctx->capacityWords |= (flags1 == SHA3_FLAGS_KECCAK ? SHA3_USE_KECCAK_FLAG : 0);
    return flags1;
}


void
sha3_Update(void *priv, void const *bufIn, size_t len)
{
    sha3_context *ctx = (sha3_context *) priv;

    /* 0...7 -- how much is needed to have a word */
    unsigned old_tail = (8 - ctx->byteIndex) & 7;

    size_t words;
    unsigned tail;
    size_t i;

    const uint8_t *buf = (uint8_t*)bufIn;

    SHA3_TRACE_BUF("called to update with:", buf, len);

    SHA3_ASSERT(ctx->byteIndex < 8);
    SHA3_ASSERT(ctx->wordIndex < sizeof(ctx->u.s) / sizeof(ctx->u.s[0]));

    if(len < old_tail) {        /* have no complete word or haven't started 
                                 * the word yet */
        SHA3_TRACE("because %d<%d, store it and return", (unsigned)len,
                (unsigned)old_tail);
        /* endian-independent code follows: */
        while (len--)
            ctx->saved |= (uint64_t) (*(buf++)) << ((ctx->byteIndex++) * 8);
        SHA3_ASSERT(ctx->byteIndex < 8);
        return;
    }

    if(old_tail) {              /* will have one word to process */
        SHA3_TRACE("completing one word with %d bytes", (unsigned)old_tail);
        /* endian-independent code follows: */
        len -= old_tail;
        while (old_tail--)
            ctx->saved |= (uint64_t) (*(buf++)) << ((ctx->byteIndex++) * 8);

        /* now ready to add saved to the sponge */
        ctx->u.s[ctx->wordIndex] ^= ctx->saved;
        SHA3_ASSERT(ctx->byteIndex == 8);
        ctx->byteIndex = 0;
        ctx->saved = 0;
        if(++ctx->wordIndex ==
                (SHA3_KECCAK_SPONGE_WORDS - SHA3_CW(ctx->capacityWords))) {
            keccakf(ctx->u.s);
            ctx->wordIndex = 0;
        }
    }

    /* now work in full words directly from input */

    SHA3_ASSERT(ctx->byteIndex == 0);

    words = len / sizeof(uint64_t);
    tail = len - words * sizeof(uint64_t);

    SHA3_TRACE("have %d full words to process", (unsigned)words);

    for(i = 0; i < words; i++, buf += sizeof(uint64_t)) {
        const uint64_t t = (uint64_t) (buf[0]) |
                ((uint64_t) (buf[1]) << 8 * 1) |
                ((uint64_t) (buf[2]) << 8 * 2) |
                ((uint64_t) (buf[3]) << 8 * 3) |
                ((uint64_t) (buf[4]) << 8 * 4) |
                ((uint64_t) (buf[5]) << 8 * 5) |
                ((uint64_t) (buf[6]) << 8 * 6) |
                ((uint64_t) (buf[7]) << 8 * 7);
#if defined(__x86_64__ ) || defined(__i386__)
        SHA3_ASSERT(memcmp(&t, buf, 8) == 0);
#endif
        ctx->u.s[ctx->wordIndex] ^= t;
        if(++ctx->wordIndex ==
                (SHA3_KECCAK_SPONGE_WORDS - SHA3_CW(ctx->capacityWords))) {
            keccakf(ctx->u.s);
            ctx->wordIndex = 0;
        }
    }

    SHA3_TRACE("have %d bytes left to process, save them", (unsigned)tail);

    /* finally, save the partial word */
    SHA3_ASSERT(ctx->byteIndex == 0 && tail < 8);
    while (tail--) {
        SHA3_TRACE("Store byte %02x '%c'", *buf, *buf);
        ctx->saved |= (uint64_t) (*(buf++)) << ((ctx->byteIndex++) * 8);
    }
    SHA3_ASSERT(ctx->byteIndex < 8);
    SHA3_TRACE("Have saved=0x%016" PRIx64 " at the end", ctx->saved);
}

/* This is simply the 'update' with the padding block.
 * The padding block is 0x01 || 0x00* || 0x80. First 0x01 and last 0x80 
 * bytes are always present, but they can be the same byte.
 */
void const *
sha3_Finalize(sha3_context *priv)
{
    sha3_context *ctx = (sha3_context *) priv;

    SHA3_TRACE("called with %d bytes in the buffer", ctx->byteIndex);

    /* Append 2-bit suffix 01, per SHA-3 spec. Instead of 1 for padding we
     * use 1<<2 below. The 0x02 below corresponds to the suffix 01.
     * Overall, we feed 0, then 1, and finally 1 to start padding. Without
     * M || 01, we would simply use 1 to start padding. */

    uint64_t t;

    if( ctx->capacityWords & SHA3_USE_KECCAK_FLAG ) {
        /* Keccak version */
        t = (uint64_t)(((uint64_t) 1) << (ctx->byteIndex * 8));
    }
    else {
        /* SHA3 version */
        t = (uint64_t)(((uint64_t)(0x02 | (1 << 2))) << ((ctx->byteIndex) * 8));
    }

    ctx->u.s[ctx->wordIndex] ^= ctx->saved ^ t;

    ctx->u.s[SHA3_KECCAK_SPONGE_WORDS - SHA3_CW(ctx->capacityWords) - 1] ^=
            SHA3_CONST(0x8000000000000000UL);
    keccakf(ctx->u.s);

    /* Return first bytes of the ctx->s. This conversion is not needed for
     * little-endian platforms e.g. wrap with #if !defined(__BYTE_ORDER__)
     * || !defined(__ORDER_LITTLE_ENDIAN__) || __BYTE_ORDER__!=__ORDER_LITTLE_ENDIAN__ 
     *    ... the conversion below ...
     * #endif */
    {
        unsigned i;
        for(i = 0; i < SHA3_KECCAK_SPONGE_WORDS; i++) {
            const unsigned t1 = (uint32_t) ctx->u.s[i];
            const unsigned t2 = (uint32_t) ((ctx->u.s[i] >> 16) >> 16);
            ctx->u.sb[i * 8 + 0] = (uint8_t) (t1);
            ctx->u.sb[i * 8 + 1] = (uint8_t) (t1 >> 8);
            ctx->u.sb[i * 8 + 2] = (uint8_t) (t1 >> 16);
            ctx->u.sb[i * 8 + 3] = (uint8_t) (t1 >> 24);
            ctx->u.sb[i * 8 + 4] = (uint8_t) (t2);
            ctx->u.sb[i * 8 + 5] = (uint8_t) (t2 >> 8);
            ctx->u.sb[i * 8 + 6] = (uint8_t) (t2 >> 16);
            ctx->u.sb[i * 8 + 7] = (uint8_t) (t2 >> 24);
        }
    }

    SHA3_TRACE_BUF("Hash: (first 32 bytes)", ctx->u.sb, 256 / 8);

    return (ctx->u.sb);
}

sha3_return_t sha3_HashBuffer( unsigned bitSize, enum SHA3_FLAGS flags, const void *in, unsigned inBytes, void *out, unsigned outBytes ) {
    sha3_return_t err;
    sha3_context c;

    err = sha3_Init(&c, bitSize);
    if( err != SHA3_RETURN_OK )
        return err;
    if( sha3_SetFlags(&c, flags) != flags ) {
        return SHA3_RETURN_BAD_PARAMS;
    }
    sha3_Update(&c, in, inBytes);
    const void *h = sha3_Finalize(&c);

    if(outBytes > bitSize/8)
        outBytes = bitSize/8;
    memcpy(out, h, outBytes);
    return SHA3_RETURN_OK;
}
//-------------------------------------------------------------------END_OF_HASHING(SHA3)------------------------------------------------

void signing_algo(mpz_t p,mpz_t q,mpz_t g,mpz_t x,mpz_t y,char message[],mpz_t *r,mpz_t *s)
{
	cout<<"\n---------------------------------------------SIGNING---------------------------------------------------\n";
    uint8_t buf[32];

	mpz_t k,kinv,temp,one,Hm;
	gmp_randstate_t k_state;
	mpz_inits(k,kinv,temp,one,Hm, NULL);
    mpz_set_str(one,"1", 10);

    // Calling SHA3-224
    sha3_HashBuffer(256, SHA3_FLAGS_KECCAK, (void*)message, 3, buf, sizeof(buf));

    // converting integer array into mpz format 
    char temp_buf[32];
    char ch[32];
    strcpy(ch,"");
    for(int i=0;i<32;i++)
    {
    	char buffer[10];
    	int t = buf[i];
   		itoa(t,buffer,10);
    	strcat(ch, buffer);
	}
    mpz_set_str(Hm,ch,10);
    gmp_printf("\n H(m) for message (%s) : %Zd", message, Hm);
    
    // Generating random k < q-1
	gmp_randinit_mt(k_state);
	int count=0;
	// Checking if generated k is less than q-1
	while(1)
	{
	    srand(time(0));
	    int seed = rand() + count++;
	    gmp_randseed_ui(k_state, seed);
	    mpz_urandomb(k, k_state, 100);
	    mpz_sub(temp,q,one);
	    if (mpz_cmp(temp,k) >= 1) break;
	}
	
	// Calculating r = (g^k mod p)mod q
	mpz_powm(*r,g,k,p);
	mpz_mod(*r,*r,q);
	
	//Finding k inverse mod p
	mpz_invert(kinv,k,q);
	gmp_printf("\n k :%Zd", k);
	gmp_printf("\n k inverse:%Zd", kinv);
	
	// Calculating s = (k_inv(H(m) + x*r))mod q
	mpz_mul(temp,x,*r);
	mpz_add(temp,Hm,temp);
	mpz_mul(temp,temp,kinv);
	mpz_mod(*s,temp,q);
}

void verification_algo(mpz_t p,mpz_t q ,mpz_t g,mpz_t y,char message[],mpz_t r,mpz_t s)
{
	cout<<"\n---------------------------------------------VERIFICATION---------------------------------------------------\n";
	uint8_t buf[32];
	mpz_t w,u1,u2,v,Hm,temp1,temp2,temp3;
	mpz_inits(w, u1,u2,v,Hm,temp1,temp2,temp3, NULL);

    // Calling SHA3-224
    sha3_HashBuffer(256, SHA3_FLAGS_KECCAK, (void*)message, 3, buf, sizeof(buf));

    // converting integer array into mpz format 
    char temp_buf[32];
    char ch[32];
    strcpy(ch,"");
    for(int i=0;i<32;i++)
    {
    	char buffer[10];
    	int t = buf[i];
   		itoa(t,buffer,10);
    	strcat(ch, buffer);
	}
    mpz_set_str(Hm,ch,10);
    gmp_printf("\n H(m) for message(%s) : %Zd", message, Hm);

	// calculating s_inv mod q
	mpz_invert(w,s,q);

    // calculating u1 = w*H(m) mod q
	mpz_mul(u1,w,Hm);
	mpz_mod(u1,u1,q);
	
	// calculating u2 = w*r mod q
	mpz_mul(u2,w,r);
	mpz_mod(u2,u2,q);

    // calculating v = ((g^u1)*(y^u2)modp)modq
	mpz_powm(temp1,g,u1,p);
	mpz_powm(temp2,y,u2,p);
	mpz_mul(temp1,temp1,temp2);
	mpz_mod(temp1,temp1,p);
	mpz_mod(v,temp1,q);

	gmp_printf("\n v:%Zd", v);
	if (mpz_cmp(v,r) == 0)
	{
		gmp_printf("\n \n SIGNATURE ACCEPTED!!");
	}
	else
	{
		gmp_printf("\n SIGNATURE REJECTED!!");
	}
}
int main()
{
    char message[100000];
    
    mpz_t p,q,g,x,y,h;
    gmp_randstate_t p_state,q_state,q_temp_state,x_state;
    
	mpz_inits(p,q,g,x,y,h, NULL);

	mpz_t temp,temp1,one,zero,q_temp;
	mpz_inits(temp,temp1,one,zero,q_temp, NULL);
	mpz_set_str(one,"1",10);mpz_set_str(zero,"0",10);

    //------------------------------------------gegerating p,q g randomly-------------------------------------------------
	// generating prime q randomly
	gmp_randinit_mt(q_state);
	srand(time(0));
	int seed = rand();
	gmp_randseed_ui(q_state, seed);
	mpz_urandomb(q, q_state, 100);
	mpz_nextprime(q,q);
	
	gmp_randinit_mt(q_temp_state);
	srand(time(0));
	seed = rand();
	gmp_randseed_ui(q_temp_state, seed);
	mpz_urandomb(q_temp, q_temp_state, 1000);
	mpz_nextprime(q_temp,q_temp);
	
	// generating prime p randomly such that q|(p-1)
	while(1)
	{
		mpz_mul(p,q,q_temp);
		mpz_add(p,p,one);
		if (mpz_probab_prime_p(p, 25)==1) break;
		mpz_add(q_temp,q_temp,one);
	}

    // finding generator h of p such that pow(h,p-1) ~ 1modp
    mpz_div(h,p,q);mpz_div(h,h,q);
    mpz_sub(temp1,p,one);
    while(1)
    {
    	// (h^p-1)modp
    	mpz_powm(temp,h,temp1,p);
    	
    	// break if (h^p-1)modp =1
    	if (mpz_cmp(temp,one) == 0) break;
    	mpz_sub(g,g,one);
	}
	
	// calculating (p-1)/q
	mpz_div(temp1,temp1,q);
	// calculating g = h^((p-1)/q) mod p
	mpz_powm(g,h,temp1,p);
    //------------------------------------------End-of-gegerating p,q g randomly-------------------------------------------------

    // Generatinf private key x randomly
	gmp_randinit_mt(x_state);
	srand(time(0));
	seed = rand();
	gmp_randseed_ui(x_state, seed);
	mpz_urandomb(x, x_state, 10);

    // Calculating public key y = g^x mod p
	mpz_powm(y,g,x,p);
    cout<<"\n-----------------------------------------------------------------------------------------------------------\n";
    gmp_printf("\n Public key (p,q,g,y): (\np : %Zd,\nq : %Zd,\ng : %Zd,\ny : %Zd\n)", p,q,g,y);
    gmp_printf("\n \n Private key x : %Zd",x);
    cout<<"\n-----------------------------------------------------------------------------------------------------------\n";
	mpz_t r,s;mpz_inits(r,s,NULL);

    cout<<"enter message to be signed: ";cin.getline(message,10000);
    cout<<"\n-----------------------------------------------------------------------------------------------------------\n";
    signing_algo(p,q,g,x,y,message,&r,&s);
    gmp_printf("\nGenerated (r,s) pair : (%Zd , %Zd)", r , s);
    cout<<"\n-----------------------------------------------------------------------------------------------------------\n";
    verification_algo(p,q,g,y,message,r,s);
    return 0;
}
