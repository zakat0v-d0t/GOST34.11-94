#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdint.h>
#include <string.h>

#define ROL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))
#define ROL32(x, n) (((x) << (n)) | ((x) >> (32 - (n))))

static const uint8_t SBOX_D_A[8][16] = {
    {10, 4, 5, 6, 8, 1, 3, 7, 13, 12, 14, 0, 9, 2, 11, 15},
    {5, 15, 4, 0, 2, 13, 11, 9, 1, 7, 6, 3, 12, 14, 10, 8},
    {7, 15, 12, 14, 9, 4, 1, 0, 3, 11, 5, 2, 6, 10, 8, 13},
    {4, 10, 7, 12, 0, 15, 2, 8, 14, 1, 6, 5, 13, 11, 9, 3},
    {7, 6, 4, 11, 9, 12, 2, 10, 1, 8, 0, 14, 15, 13, 3, 5},
    {7, 6, 2, 4, 13, 9, 15, 0, 10, 1, 5, 11, 8, 14, 12, 3},
    {13, 14, 4, 1, 7, 0, 5, 10, 3, 12, 8, 15, 6, 2, 9, 11},
    {1, 3, 10, 9, 5, 11, 4, 15, 8, 6, 7, 14, 13, 0, 2, 12}
};

static uint32_t T0[256], T1[256], T2[256], T3[256];
static int tables_initialized = 0;

static void init_tables(void) {
    if (tables_initialized) return;
    for (int b = 0; b < 256; b++) {
        uint32_t s0 = SBOX_D_A[0][b & 0xF] | (SBOX_D_A[1][b >> 4] << 4);
        uint32_t s1 = SBOX_D_A[2][b & 0xF] | (SBOX_D_A[3][b >> 4] << 4);
        uint32_t s2 = SBOX_D_A[4][b & 0xF] | (SBOX_D_A[5][b >> 4] << 4);
        uint32_t s3 = SBOX_D_A[6][b & 0xF] | (SBOX_D_A[7][b >> 4] << 4);
        T0[b] = ROL32(s0, 11);
        T1[b] = ROL32(s1 << 8, 11);
        T2[b] = ROL32(s2 << 16, 11);
        T3[b] = ROL32(s3 << 24, 11);
    }
    tables_initialized = 1;
}

static inline void gost_encrypt_block(const uint8_t in[8], const uint32_t subkeys[8], uint8_t out[8]) {
    uint32_t n1, n2;
    memcpy(&n1, in, 4);
    memcpy(&n2, in + 4, 4);

    for (int cycle = 0; cycle < 3; cycle++) {
        for (int k = 0; k < 8; k++) {
            uint32_t v = n1 + subkeys[k];
            uint32_t f = T0[v & 0xFF] ^ T1[(v >> 8) & 0xFF] ^ T2[(v >> 16) & 0xFF] ^ T3[(v >> 24) & 0xFF];
            uint32_t tmp = n2 ^ f;
            n2 = n1;
            n1 = tmp;
        }
    }
    for (int k = 7; k >= 1; k--) {
        uint32_t v = n1 + subkeys[k];
        uint32_t f = T0[v & 0xFF] ^ T1[(v >> 8) & 0xFF] ^ T2[(v >> 16) & 0xFF] ^ T3[(v >> 24) & 0xFF];
        uint32_t tmp = n2 ^ f;
        n2 = n1;
        n1 = tmp;
    }
    uint32_t v = n1 + subkeys[0];
    uint32_t f = T0[v & 0xFF] ^ T1[(v >> 8) & 0xFF] ^ T2[(v >> 16) & 0xFF] ^ T3[(v >> 24) & 0xFF];
    n2 ^= f;

    memcpy(out, &n1, 4);
    memcpy(out + 4, &n2, 4);
}

static const uint8_t C2[32] = {
    0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
    0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00,
    0x00, 0xFF, 0xFF, 0x00, 0xFF, 0x00, 0x00, 0xFF,
    0xFF, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0x00, 0xFF
};

static inline void transform_P(const uint8_t Y[32], uint8_t K[32]) {
    for (int k = 0; k < 8; k++) {
        K[4 * k + 0] = Y[k];
        K[4 * k + 1] = Y[8 + k];
        K[4 * k + 2] = Y[16 + k];
        K[4 * k + 3] = Y[24 + k];
    }
}

static inline void transform_A(uint8_t Y[32]) {
    uint8_t a[8];
    for (int i = 0; i < 8; i++) a[i] = Y[i] ^ Y[8 + i];
    memmove(Y, Y + 8, 24);
    memcpy(Y + 24, a, 8);
}

static inline void fw_multi(uint8_t S[32], int n) {
    uint16_t w[16 + 64];
    memcpy(w, S, 32);
    for (int i = 0; i < n; i++) {
        w[16 + i] = (uint16_t)(w[i] ^ w[i + 1] ^ w[i + 2] ^ w[i + 3] ^ w[i + 12] ^ w[i + 15]);
    }
    memcpy(S, &w[n], 32);
}

static void gost3411_compress(uint8_t H[32], const uint8_t M[32]) {
    init_tables();
    uint8_t U[32], V[32], W[32], K[32], S[32];
    memcpy(U, H, 32);
    memcpy(V, M, 32);
    for (int i = 0; i < 32; i++) W[i] = U[i] ^ V[i];
    transform_P(W, K);

    uint32_t subkeys[8];
    memcpy(subkeys, K, 32);
    gost_encrypt_block(H, subkeys, S);

    for (int i = 1; i < 4; i++) {
        transform_A(U);
        if (i == 2) {
            for (int j = 0; j < 32; j++) U[j] ^= C2[j];
        }
        transform_A(V);
        transform_A(V);
        for (int j = 0; j < 32; j++) W[j] = U[j] ^ V[j];
        transform_P(W, K);
        memcpy(subkeys, K, 32);
        gost_encrypt_block(H + i * 8, subkeys, S + i * 8);
    }

    fw_multi(S, 12);
    for (int i = 0; i < 32; i++) S[i] ^= M[i];
    fw_multi(S, 1);
    for (int i = 0; i < 32; i++) S[i] ^= H[i];
    fw_multi(S, 61);
    memcpy(H, S, 32);
}

typedef struct {
    uint8_t H[32];
    uint8_t Sum[32];
    uint8_t buf[32];
    size_t buf_len;
    uint64_t bit_count;
} gost3411_ctx;

void gost3411_init(gost3411_ctx *ctx) {
    memset(ctx, 0, sizeof(*ctx));
    init_tables();
}

void gost3411_update(gost3411_ctx *ctx, const uint8_t *data, size_t len) {
    ctx->bit_count += (uint64_t)len * 8;
    if (ctx->buf_len > 0) {
        size_t needed = 32 - ctx->buf_len;
        if (len < needed) {
            memcpy(ctx->buf + ctx->buf_len, data, len);
            ctx->buf_len += len;
            return;
        }
        memcpy(ctx->buf + ctx->buf_len, data, needed);
        data += needed;
        len -= needed;
        ctx->buf_len = 0;

        uint32_t carry = 0;
        for (int i = 0; i < 32; i++) {
            uint32_t val = (uint32_t)ctx->Sum[i] + ctx->buf[i] + carry;
            ctx->Sum[i] = (uint8_t)val;
            carry = val >> 8;
        }
        gost3411_compress(ctx->H, ctx->buf);
    }

    while (len >= 32) {
        uint32_t carry = 0;
        for (int i = 0; i < 32; i++) {
            uint32_t val = (uint32_t)ctx->Sum[i] + data[i] + carry;
            ctx->Sum[i] = (uint8_t)val;
            carry = val >> 8;
        }
        gost3411_compress(ctx->H, data);
        data += 32;
        len -= 32;
    }

    if (len > 0) {
        memcpy(ctx->buf, data, len);
        ctx->buf_len = len;
    }
}

void gost3411_final(gost3411_ctx *ctx, uint8_t digest[32]) {
    if (ctx->buf_len > 0) {
        memset(ctx->buf + ctx->buf_len, 0, 32 - ctx->buf_len);
        uint32_t carry = 0;
        for (int i = 0; i < 32; i++) {
            uint32_t val = (uint32_t)ctx->Sum[i] + ctx->buf[i] + carry;
            ctx->Sum[i] = (uint8_t)val;
            carry = val >> 8;
        }
        gost3411_compress(ctx->H, ctx->buf);
    }

    uint8_t L[32];
    memset(L, 0, 32);
    memcpy(L, &ctx->bit_count, 8);
    gost3411_compress(ctx->H, L);
    gost3411_compress(ctx->H, ctx->Sum);
    memcpy(digest, ctx->H, 32);
}

/* RIPEMD-128 */
typedef struct {
    uint32_t H[4];
    uint8_t buf[64];
    size_t buf_len;
    uint64_t bit_count;
} ripemd128_ctx;

void ripemd128_init(ripemd128_ctx *ctx) {
    ctx->H[0] = 0x67452301U; ctx->H[1] = 0xefcdab89U;
    ctx->H[2] = 0x98badcfeU; ctx->H[3] = 0x10325476U;
    ctx->buf_len = 0;
    ctx->bit_count = 0;
}

static void ripemd128_compress(uint32_t H[4], const uint8_t block[64]) {
    uint32_t X[16];
    memcpy(X, block, 64);
    uint32_t v[10] = {0, H[0], H[0], H[1], H[1], H[2], H[2], H[3], H[3], 0};
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[0], 11);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[1], 14);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[2], 15);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[3], 12);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[4], 5);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[5], 8);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[6], 7);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[7], 9);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[8], 11);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[9], 13);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[10], 14);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[11], 15);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[12], 6);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[13], 7);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[14], 9);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[15], 8);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[7] + 0x5a827999U, 7);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[4] + 0x5a827999U, 6);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[13] + 0x5a827999U, 8);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[1] + 0x5a827999U, 13);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[10] + 0x5a827999U, 11);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[6] + 0x5a827999U, 9);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[15] + 0x5a827999U, 7);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[3] + 0x5a827999U, 15);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[12] + 0x5a827999U, 7);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[0] + 0x5a827999U, 12);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[9] + 0x5a827999U, 15);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[5] + 0x5a827999U, 9);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[2] + 0x5a827999U, 11);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[14] + 0x5a827999U, 7);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[11] + 0x5a827999U, 13);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[8] + 0x5a827999U, 12);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[3] + 0x6ed9eba1U, 11);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[10] + 0x6ed9eba1U, 13);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[14] + 0x6ed9eba1U, 6);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[4] + 0x6ed9eba1U, 7);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[9] + 0x6ed9eba1U, 14);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[15] + 0x6ed9eba1U, 9);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[8] + 0x6ed9eba1U, 13);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[1] + 0x6ed9eba1U, 15);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[2] + 0x6ed9eba1U, 14);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[7] + 0x6ed9eba1U, 8);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[0] + 0x6ed9eba1U, 13);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[6] + 0x6ed9eba1U, 6);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[13] + 0x6ed9eba1U, 5);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[11] + 0x6ed9eba1U, 12);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[5] + 0x6ed9eba1U, 7);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[12] + 0x6ed9eba1U, 5);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[1] + 0x8f1bbcdcU, 11);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[9] + 0x8f1bbcdcU, 12);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[11] + 0x8f1bbcdcU, 14);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[10] + 0x8f1bbcdcU, 15);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[0] + 0x8f1bbcdcU, 14);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[8] + 0x8f1bbcdcU, 15);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[12] + 0x8f1bbcdcU, 9);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[4] + 0x8f1bbcdcU, 8);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[13] + 0x8f1bbcdcU, 9);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[3] + 0x8f1bbcdcU, 14);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[7] + 0x8f1bbcdcU, 5);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[15] + 0x8f1bbcdcU, 6);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[14] + 0x8f1bbcdcU, 8);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[5] + 0x8f1bbcdcU, 6);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[6] + 0x8f1bbcdcU, 5);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[2] + 0x8f1bbcdcU, 12);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[5] + 0x50a28be6U, 8);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[14] + 0x50a28be6U, 9);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[7] + 0x50a28be6U, 9);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[0] + 0x50a28be6U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[9] + 0x50a28be6U, 13);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[2] + 0x50a28be6U, 15);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[11] + 0x50a28be6U, 15);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[4] + 0x50a28be6U, 5);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[13] + 0x50a28be6U, 7);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[6] + 0x50a28be6U, 7);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[15] + 0x50a28be6U, 8);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[8] + 0x50a28be6U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[1] + 0x50a28be6U, 14);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[10] + 0x50a28be6U, 14);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[3] + 0x50a28be6U, 12);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[12] + 0x50a28be6U, 6);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[6] + 0x5c4dd124U, 9);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[11] + 0x5c4dd124U, 13);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[3] + 0x5c4dd124U, 15);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[7] + 0x5c4dd124U, 7);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[0] + 0x5c4dd124U, 12);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[13] + 0x5c4dd124U, 8);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[5] + 0x5c4dd124U, 9);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[10] + 0x5c4dd124U, 11);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[14] + 0x5c4dd124U, 7);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[15] + 0x5c4dd124U, 7);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[8] + 0x5c4dd124U, 12);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[12] + 0x5c4dd124U, 7);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[4] + 0x5c4dd124U, 6);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[9] + 0x5c4dd124U, 15);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[1] + 0x5c4dd124U, 13);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[2] + 0x5c4dd124U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[15] + 0x6d703ef3U, 9);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[5] + 0x6d703ef3U, 7);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[1] + 0x6d703ef3U, 15);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[3] + 0x6d703ef3U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[7] + 0x6d703ef3U, 8);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[14] + 0x6d703ef3U, 6);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[6] + 0x6d703ef3U, 6);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[9] + 0x6d703ef3U, 14);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[11] + 0x6d703ef3U, 12);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[8] + 0x6d703ef3U, 13);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[12] + 0x6d703ef3U, 5);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[2] + 0x6d703ef3U, 14);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[10] + 0x6d703ef3U, 13);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[0] + 0x6d703ef3U, 13);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[4] + 0x6d703ef3U, 7);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[13] + 0x6d703ef3U, 5);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[8], 15);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[6], 5);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[4], 8);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[1], 11);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[3], 14);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[11], 14);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[15], 6);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[0], 14);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[5], 6);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[12], 9);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[2], 12);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[13], 9);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[9], 12);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[7], 5);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[10], 15);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[14], 8);

    uint32_t ddd = H[1] + v[5] + v[8];
    H[1] = H[2] + v[7] + v[2];
    H[2] = H[3] + v[1] + v[4];
    H[3] = H[0] + v[3] + v[6];
    H[0] = ddd;
}

void ripemd128_update(ripemd128_ctx *ctx, const uint8_t *data, size_t len) {
    ctx->bit_count += (uint64_t)len * 8;
    if (ctx->buf_len > 0) {
        size_t needed = 64 - ctx->buf_len;
        if (len < needed) {
            memcpy(ctx->buf + ctx->buf_len, data, len);
            ctx->buf_len += len;
            return;
        }
        memcpy(ctx->buf + ctx->buf_len, data, needed);
        data += needed; len -= needed; ctx->buf_len = 0;
        ripemd128_compress(ctx->H, ctx->buf);
    }
    while (len >= 64) {
        ripemd128_compress(ctx->H, data);
        data += 64; len -= 64;
    }
    if (len > 0) {
        memcpy(ctx->buf, data, len);
        ctx->buf_len = len;
    }
}

void ripemd128_final(ripemd128_ctx *ctx, uint8_t digest[16]) {
    uint8_t pad[128];
    memset(pad, 0, sizeof(pad));
    memcpy(pad, ctx->buf, ctx->buf_len);
    pad[ctx->buf_len] = 0x80;
    size_t pad_len = (ctx->buf_len < 56) ? 64 : 128;
    memcpy(pad + pad_len - 8, &ctx->bit_count, 8);
    ripemd128_compress(ctx->H, pad);
    if (pad_len == 128) ripemd128_compress(ctx->H, pad + 64);
    memcpy(digest, ctx->H, 16);
}

/* RIPEMD-256 */
typedef struct {
    uint32_t H[8];
    uint8_t buf[64];
    size_t buf_len;
    uint64_t bit_count;
} ripemd256_ctx;

void ripemd256_init(ripemd256_ctx *ctx) {
    ctx->H[0] = 0x67452301U; ctx->H[1] = 0xefcdab89U;
    ctx->H[2] = 0x98badcfeU; ctx->H[3] = 0x10325476U;
    ctx->H[4] = 0x76543210U; ctx->H[5] = 0xFEDCBA98U;
    ctx->H[6] = 0x89ABCDEFU; ctx->H[7] = 0x01234567U;
    ctx->buf_len = 0;
    ctx->bit_count = 0;
}

static void ripemd256_compress(uint32_t H[8], const uint8_t block[64]) {
    uint32_t X[16];
    memcpy(X, block, 64);
    uint32_t v[10] = {0, H[0], H[4], H[1], H[5], H[2], H[6], H[3], H[7], 0};
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[0], 11);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[1], 14);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[2], 15);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[3], 12);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[4], 5);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[5], 8);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[6], 7);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[7], 9);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[8], 11);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[9], 13);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[10], 14);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[11], 15);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[12], 6);
    v[7] = ROL(v[7] + (v[1] ^ v[3] ^ v[5]) + X[13], 7);
    v[5] = ROL(v[5] + (v[7] ^ v[1] ^ v[3]) + X[14], 9);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[1]) + X[15], 8);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[5] + 0x50a28be6U, 8);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[14] + 0x50a28be6U, 9);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[7] + 0x50a28be6U, 9);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[0] + 0x50a28be6U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[9] + 0x50a28be6U, 13);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[2] + 0x50a28be6U, 15);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[11] + 0x50a28be6U, 15);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[4] + 0x50a28be6U, 5);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[13] + 0x50a28be6U, 7);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[6] + 0x50a28be6U, 7);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[15] + 0x50a28be6U, 8);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[8] + 0x50a28be6U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[1] + 0x50a28be6U, 14);
    v[8] = ROL(v[8] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[10] + 0x50a28be6U, 14);
    v[6] = ROL(v[6] + ((v[8] & v[4]) | (v[2] & ~v[4])) + X[3] + 0x50a28be6U, 12);
    v[4] = ROL(v[4] + ((v[6] & v[2]) | (v[8] & ~v[2])) + X[12] + 0x50a28be6U, 6);
    { uint32_t t = v[1]; v[1] = v[2]; v[2] = t; }
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[7] + 0x5a827999U, 7);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[4] + 0x5a827999U, 6);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[13] + 0x5a827999U, 8);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[1] + 0x5a827999U, 13);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[10] + 0x5a827999U, 11);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[6] + 0x5a827999U, 9);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[15] + 0x5a827999U, 7);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[3] + 0x5a827999U, 15);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[12] + 0x5a827999U, 7);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[0] + 0x5a827999U, 12);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[9] + 0x5a827999U, 15);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[5] + 0x5a827999U, 9);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[2] + 0x5a827999U, 11);
    v[7] = ROL(v[7] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[14] + 0x5a827999U, 7);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (~v[7] & v[3])) + X[11] + 0x5a827999U, 13);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[1])) + X[8] + 0x5a827999U, 12);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[6] + 0x5c4dd124U, 9);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[11] + 0x5c4dd124U, 13);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[3] + 0x5c4dd124U, 15);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[7] + 0x5c4dd124U, 7);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[0] + 0x5c4dd124U, 12);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[13] + 0x5c4dd124U, 8);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[5] + 0x5c4dd124U, 9);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[10] + 0x5c4dd124U, 11);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[14] + 0x5c4dd124U, 7);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[15] + 0x5c4dd124U, 7);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[8] + 0x5c4dd124U, 12);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[12] + 0x5c4dd124U, 7);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[4] + 0x5c4dd124U, 6);
    v[8] = ROL(v[8] + ((v[2] | ~v[4]) ^ v[6]) + X[9] + 0x5c4dd124U, 15);
    v[6] = ROL(v[6] + ((v[8] | ~v[2]) ^ v[4]) + X[1] + 0x5c4dd124U, 13);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[2]) + X[2] + 0x5c4dd124U, 11);
    { uint32_t t = v[3]; v[3] = v[4]; v[4] = t; }
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[3] + 0x6ed9eba1U, 11);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[10] + 0x6ed9eba1U, 13);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[14] + 0x6ed9eba1U, 6);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[4] + 0x6ed9eba1U, 7);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[9] + 0x6ed9eba1U, 14);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[15] + 0x6ed9eba1U, 9);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[8] + 0x6ed9eba1U, 13);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[1] + 0x6ed9eba1U, 15);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[2] + 0x6ed9eba1U, 14);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[7] + 0x6ed9eba1U, 8);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[0] + 0x6ed9eba1U, 13);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[6] + 0x6ed9eba1U, 6);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[13] + 0x6ed9eba1U, 5);
    v[7] = ROL(v[7] + ((v[1] | ~v[3]) ^ v[5]) + X[11] + 0x6ed9eba1U, 12);
    v[5] = ROL(v[5] + ((v[7] | ~v[1]) ^ v[3]) + X[5] + 0x6ed9eba1U, 7);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[1]) + X[12] + 0x6ed9eba1U, 5);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[15] + 0x6d703ef3U, 9);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[5] + 0x6d703ef3U, 7);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[1] + 0x6d703ef3U, 15);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[3] + 0x6d703ef3U, 11);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[7] + 0x6d703ef3U, 8);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[14] + 0x6d703ef3U, 6);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[6] + 0x6d703ef3U, 6);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[9] + 0x6d703ef3U, 14);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[11] + 0x6d703ef3U, 12);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[8] + 0x6d703ef3U, 13);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[12] + 0x6d703ef3U, 5);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[2] + 0x6d703ef3U, 14);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[10] + 0x6d703ef3U, 13);
    v[8] = ROL(v[8] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[0] + 0x6d703ef3U, 13);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (~v[8] & v[4])) + X[4] + 0x6d703ef3U, 7);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[2])) + X[13] + 0x6d703ef3U, 5);
    { uint32_t t = v[5]; v[5] = v[6]; v[6] = t; }
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[1] + 0x8f1bbcdcU, 11);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[9] + 0x8f1bbcdcU, 12);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[11] + 0x8f1bbcdcU, 14);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[10] + 0x8f1bbcdcU, 15);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[0] + 0x8f1bbcdcU, 14);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[8] + 0x8f1bbcdcU, 15);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[12] + 0x8f1bbcdcU, 9);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[4] + 0x8f1bbcdcU, 8);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[13] + 0x8f1bbcdcU, 9);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[3] + 0x8f1bbcdcU, 14);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[7] + 0x8f1bbcdcU, 5);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[15] + 0x8f1bbcdcU, 6);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[14] + 0x8f1bbcdcU, 8);
    v[7] = ROL(v[7] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[5] + 0x8f1bbcdcU, 6);
    v[5] = ROL(v[5] + ((v[7] & v[3]) | (v[1] & ~v[3])) + X[6] + 0x8f1bbcdcU, 5);
    v[3] = ROL(v[3] + ((v[5] & v[1]) | (v[7] & ~v[1])) + X[2] + 0x8f1bbcdcU, 12);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[8], 15);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[6], 5);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[4], 8);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[1], 11);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[3], 14);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[11], 14);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[15], 6);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[0], 14);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[5], 6);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[12], 9);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[2], 12);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[13], 9);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[9], 12);
    v[8] = ROL(v[8] + (v[2] ^ v[4] ^ v[6]) + X[7], 5);
    v[6] = ROL(v[6] + (v[8] ^ v[2] ^ v[4]) + X[10], 15);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[2]) + X[14], 8);
    { uint32_t t = v[7]; v[7] = v[8]; v[8] = t; }

    H[0] += v[1]; H[1] += v[3]; H[2] += v[5]; H[3] += v[7];
    H[4] += v[2]; H[5] += v[4]; H[6] += v[6]; H[7] += v[8];
}

void ripemd256_update(ripemd256_ctx *ctx, const uint8_t *data, size_t len) {
    ctx->bit_count += (uint64_t)len * 8;
    if (ctx->buf_len > 0) {
        size_t needed = 64 - ctx->buf_len;
        if (len < needed) {
            memcpy(ctx->buf + ctx->buf_len, data, len);
            ctx->buf_len += len;
            return;
        }
        memcpy(ctx->buf + ctx->buf_len, data, needed);
        data += needed; len -= needed; ctx->buf_len = 0;
        ripemd256_compress(ctx->H, ctx->buf);
    }
    while (len >= 64) {
        ripemd256_compress(ctx->H, data);
        data += 64; len -= 64;
    }
    if (len > 0) {
        memcpy(ctx->buf, data, len);
        ctx->buf_len = len;
    }
}

void ripemd256_final(ripemd256_ctx *ctx, uint8_t digest[32]) {
    uint8_t pad[128];
    memset(pad, 0, sizeof(pad));
    memcpy(pad, ctx->buf, ctx->buf_len);
    pad[ctx->buf_len] = 0x80;
    size_t pad_len = (ctx->buf_len < 56) ? 64 : 128;
    memcpy(pad + pad_len - 8, &ctx->bit_count, 8);
    ripemd256_compress(ctx->H, pad);
    if (pad_len == 128) ripemd256_compress(ctx->H, pad + 64);
    memcpy(digest, ctx->H, 32);
}

/* RIPEMD-320 */
typedef struct {
    uint32_t H[10];
    uint8_t buf[64];
    size_t buf_len;
    uint64_t bit_count;
} ripemd320_ctx;

void ripemd320_init(ripemd320_ctx *ctx) {
    ctx->H[0] = 0x67452301U; ctx->H[1] = 0xefcdab89U;
    ctx->H[2] = 0x98badcfeU; ctx->H[3] = 0x10325476U; ctx->H[4] = 0xc3d2e1f0U;
    ctx->H[5] = 0x76543210U; ctx->H[6] = 0xFEDCBA98U;
    ctx->H[7] = 0x89ABCDEFU; ctx->H[8] = 0x01234567U; ctx->H[9] = 0x3C2D1E0FU;
    ctx->buf_len = 0;
    ctx->bit_count = 0;
}

static void ripemd320_compress(uint32_t H[10], const uint8_t block[64]) {
    uint32_t X[16];
    memcpy(X, block, 64);
    uint32_t v[12] = {0, H[0], H[5], H[1], H[6], H[2], H[7], H[3], H[8], H[4], H[9], 0};
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[0], 11) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + (v[1] ^ v[3] ^ v[5]) + X[1], 14) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + (v[9] ^ v[1] ^ v[3]) + X[2], 15) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + (v[7] ^ v[9] ^ v[1]) + X[3], 12) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[9]) + X[4], 5) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[5], 8) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + (v[1] ^ v[3] ^ v[5]) + X[6], 7) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + (v[9] ^ v[1] ^ v[3]) + X[7], 9) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + (v[7] ^ v[9] ^ v[1]) + X[8], 11) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[9]) + X[9], 13) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[10], 14) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + (v[1] ^ v[3] ^ v[5]) + X[11], 15) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + (v[9] ^ v[1] ^ v[3]) + X[12], 6) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + (v[7] ^ v[9] ^ v[1]) + X[13], 7) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + (v[5] ^ v[7] ^ v[9]) + X[14], 9) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + (v[3] ^ v[5] ^ v[7]) + X[15], 8) + v[9];
    v[5] = ROL(v[5], 10);
    v[2] = ROL(v[2] + (v[4] ^ (v[6] | ~v[8])) + X[5] + 0x50a28be6U, 8) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + (v[2] ^ (v[4] | ~v[6])) + X[14] + 0x50a28be6U, 9) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + (v[10] ^ (v[2] | ~v[4])) + X[7] + 0x50a28be6U, 9) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + (v[8] ^ (v[10] | ~v[2])) + X[0] + 0x50a28be6U, 11) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + (v[6] ^ (v[8] | ~v[10])) + X[9] + 0x50a28be6U, 13) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + (v[4] ^ (v[6] | ~v[8])) + X[2] + 0x50a28be6U, 15) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + (v[2] ^ (v[4] | ~v[6])) + X[11] + 0x50a28be6U, 15) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + (v[10] ^ (v[2] | ~v[4])) + X[4] + 0x50a28be6U, 5) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + (v[8] ^ (v[10] | ~v[2])) + X[13] + 0x50a28be6U, 7) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + (v[6] ^ (v[8] | ~v[10])) + X[6] + 0x50a28be6U, 7) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + (v[4] ^ (v[6] | ~v[8])) + X[15] + 0x50a28be6U, 8) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + (v[2] ^ (v[4] | ~v[6])) + X[8] + 0x50a28be6U, 11) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + (v[10] ^ (v[2] | ~v[4])) + X[1] + 0x50a28be6U, 14) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + (v[8] ^ (v[10] | ~v[2])) + X[10] + 0x50a28be6U, 14) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + (v[6] ^ (v[8] | ~v[10])) + X[3] + 0x50a28be6U, 12) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + (v[4] ^ (v[6] | ~v[8])) + X[12] + 0x50a28be6U, 6) + v[10];
    v[6] = ROL(v[6], 10);
    { uint32_t t = v[1]; v[1] = v[2]; v[2] = t; }
    v[9] = ROL(v[9] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[7] + 0x5a827999U, 7) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] & v[1]) | (~v[9] & v[3])) + X[4] + 0x5a827999U, 6) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] & v[9]) | (~v[7] & v[1])) + X[13] + 0x5a827999U, 8) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[9])) + X[1] + 0x5a827999U, 13) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[10] + 0x5a827999U, 11) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[6] + 0x5a827999U, 9) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] & v[1]) | (~v[9] & v[3])) + X[15] + 0x5a827999U, 7) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] & v[9]) | (~v[7] & v[1])) + X[3] + 0x5a827999U, 15) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[9])) + X[12] + 0x5a827999U, 7) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[0] + 0x5a827999U, 12) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[9] + 0x5a827999U, 15) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] & v[1]) | (~v[9] & v[3])) + X[5] + 0x5a827999U, 9) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] & v[9]) | (~v[7] & v[1])) + X[2] + 0x5a827999U, 11) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] & v[7]) | (~v[5] & v[9])) + X[14] + 0x5a827999U, 7) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] & v[5]) | (~v[3] & v[7])) + X[11] + 0x5a827999U, 13) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] & v[3]) | (~v[1] & v[5])) + X[8] + 0x5a827999U, 12) + v[7];
    v[3] = ROL(v[3], 10);
    v[10] = ROL(v[10] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[6] + 0x5c4dd124U, 9) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] & v[4]) | (v[2] & ~v[4])) + X[11] + 0x5c4dd124U, 13) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (v[10] & ~v[2])) + X[3] + 0x5c4dd124U, 15) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] & v[10]) | (v[8] & ~v[10])) + X[7] + 0x5c4dd124U, 7) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[0] + 0x5c4dd124U, 12) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[13] + 0x5c4dd124U, 8) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] & v[4]) | (v[2] & ~v[4])) + X[5] + 0x5c4dd124U, 9) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (v[10] & ~v[2])) + X[10] + 0x5c4dd124U, 11) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] & v[10]) | (v[8] & ~v[10])) + X[14] + 0x5c4dd124U, 7) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[15] + 0x5c4dd124U, 7) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[8] + 0x5c4dd124U, 12) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] & v[4]) | (v[2] & ~v[4])) + X[12] + 0x5c4dd124U, 7) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] & v[2]) | (v[10] & ~v[2])) + X[4] + 0x5c4dd124U, 6) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] & v[10]) | (v[8] & ~v[10])) + X[9] + 0x5c4dd124U, 15) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] & v[8]) | (v[6] & ~v[8])) + X[1] + 0x5c4dd124U, 13) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] & v[6]) | (v[4] & ~v[6])) + X[2] + 0x5c4dd124U, 11) + v[8];
    v[4] = ROL(v[4], 10);
    { uint32_t t = v[3]; v[3] = v[4]; v[4] = t; }
    v[7] = ROL(v[7] + ((v[9] | ~v[1]) ^ v[3]) + X[3] + 0x6ed9eba1U, 11) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] | ~v[9]) ^ v[1]) + X[10] + 0x6ed9eba1U, 13) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[9]) + X[14] + 0x6ed9eba1U, 6) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[4] + 0x6ed9eba1U, 7) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] | ~v[3]) ^ v[5]) + X[9] + 0x6ed9eba1U, 14) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] | ~v[1]) ^ v[3]) + X[15] + 0x6ed9eba1U, 9) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] | ~v[9]) ^ v[1]) + X[8] + 0x6ed9eba1U, 13) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[9]) + X[1] + 0x6ed9eba1U, 15) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[2] + 0x6ed9eba1U, 14) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] | ~v[3]) ^ v[5]) + X[7] + 0x6ed9eba1U, 8) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] | ~v[1]) ^ v[3]) + X[0] + 0x6ed9eba1U, 13) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] | ~v[9]) ^ v[1]) + X[6] + 0x6ed9eba1U, 6) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] | ~v[7]) ^ v[9]) + X[13] + 0x6ed9eba1U, 5) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] | ~v[5]) ^ v[7]) + X[11] + 0x6ed9eba1U, 12) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] | ~v[3]) ^ v[5]) + X[5] + 0x6ed9eba1U, 7) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] | ~v[1]) ^ v[3]) + X[12] + 0x6ed9eba1U, 5) + v[5];
    v[1] = ROL(v[1], 10);
    v[8] = ROL(v[8] + ((v[10] | ~v[2]) ^ v[4]) + X[15] + 0x6d703ef3U, 9) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] | ~v[10]) ^ v[2]) + X[5] + 0x6d703ef3U, 7) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[10]) + X[1] + 0x6d703ef3U, 15) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[3] + 0x6d703ef3U, 11) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] | ~v[4]) ^ v[6]) + X[7] + 0x6d703ef3U, 8) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] | ~v[2]) ^ v[4]) + X[14] + 0x6d703ef3U, 6) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] | ~v[10]) ^ v[2]) + X[6] + 0x6d703ef3U, 6) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[10]) + X[9] + 0x6d703ef3U, 14) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[11] + 0x6d703ef3U, 12) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] | ~v[4]) ^ v[6]) + X[8] + 0x6d703ef3U, 13) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] | ~v[2]) ^ v[4]) + X[12] + 0x6d703ef3U, 5) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] | ~v[10]) ^ v[2]) + X[2] + 0x6d703ef3U, 14) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] | ~v[8]) ^ v[10]) + X[10] + 0x6d703ef3U, 13) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] | ~v[6]) ^ v[8]) + X[0] + 0x6d703ef3U, 13) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] | ~v[4]) ^ v[6]) + X[4] + 0x6d703ef3U, 7) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] | ~v[2]) ^ v[4]) + X[13] + 0x6d703ef3U, 5) + v[6];
    v[2] = ROL(v[2], 10);
    { uint32_t t = v[5]; v[5] = v[6]; v[6] = t; }
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (v[9] & ~v[1])) + X[1] + 0x8f1bbcdcU, 11) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] & v[9]) | (v[7] & ~v[9])) + X[9] + 0x8f1bbcdcU, 12) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[11] + 0x8f1bbcdcU, 14) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[10] + 0x8f1bbcdcU, 15) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] & v[3]) | (v[1] & ~v[3])) + X[0] + 0x8f1bbcdcU, 14) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (v[9] & ~v[1])) + X[8] + 0x8f1bbcdcU, 15) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] & v[9]) | (v[7] & ~v[9])) + X[12] + 0x8f1bbcdcU, 9) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[4] + 0x8f1bbcdcU, 8) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[13] + 0x8f1bbcdcU, 9) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] & v[3]) | (v[1] & ~v[3])) + X[3] + 0x8f1bbcdcU, 14) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (v[9] & ~v[1])) + X[7] + 0x8f1bbcdcU, 5) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + ((v[5] & v[9]) | (v[7] & ~v[9])) + X[15] + 0x8f1bbcdcU, 6) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + ((v[3] & v[7]) | (v[5] & ~v[7])) + X[14] + 0x8f1bbcdcU, 8) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + ((v[1] & v[5]) | (v[3] & ~v[5])) + X[5] + 0x8f1bbcdcU, 6) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + ((v[9] & v[3]) | (v[1] & ~v[3])) + X[6] + 0x8f1bbcdcU, 5) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + ((v[7] & v[1]) | (v[9] & ~v[1])) + X[2] + 0x8f1bbcdcU, 12) + v[3];
    v[9] = ROL(v[9], 10);
    v[6] = ROL(v[6] + ((v[8] & v[10]) | (~v[8] & v[2])) + X[8] + 0x7a6d76e9U, 15) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[10])) + X[6] + 0x7a6d76e9U, 5) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[4] + 0x7a6d76e9U, 8) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[1] + 0x7a6d76e9U, 11) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] & v[2]) | (~v[10] & v[4])) + X[3] + 0x7a6d76e9U, 14) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] & v[10]) | (~v[8] & v[2])) + X[11] + 0x7a6d76e9U, 14) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[10])) + X[15] + 0x7a6d76e9U, 6) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[0] + 0x7a6d76e9U, 14) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[5] + 0x7a6d76e9U, 6) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] & v[2]) | (~v[10] & v[4])) + X[12] + 0x7a6d76e9U, 9) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] & v[10]) | (~v[8] & v[2])) + X[2] + 0x7a6d76e9U, 12) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + ((v[6] & v[8]) | (~v[6] & v[10])) + X[13] + 0x7a6d76e9U, 9) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + ((v[4] & v[6]) | (~v[4] & v[8])) + X[9] + 0x7a6d76e9U, 12) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + ((v[2] & v[4]) | (~v[2] & v[6])) + X[7] + 0x7a6d76e9U, 5) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + ((v[10] & v[2]) | (~v[10] & v[4])) + X[10] + 0x7a6d76e9U, 15) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + ((v[8] & v[10]) | (~v[8] & v[2])) + X[14] + 0x7a6d76e9U, 8) + v[4];
    v[10] = ROL(v[10], 10);
    { uint32_t t = v[7]; v[7] = v[8]; v[8] = t; }
    v[3] = ROL(v[3] + (v[5] ^ (v[7] | ~v[9])) + X[4] + 0xa953fd4eU, 9) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + (v[3] ^ (v[5] | ~v[7])) + X[0] + 0xa953fd4eU, 15) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + (v[1] ^ (v[3] | ~v[5])) + X[5] + 0xa953fd4eU, 5) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + (v[9] ^ (v[1] | ~v[3])) + X[9] + 0xa953fd4eU, 11) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + (v[7] ^ (v[9] | ~v[1])) + X[7] + 0xa953fd4eU, 6) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + (v[5] ^ (v[7] | ~v[9])) + X[12] + 0xa953fd4eU, 8) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + (v[3] ^ (v[5] | ~v[7])) + X[2] + 0xa953fd4eU, 13) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + (v[1] ^ (v[3] | ~v[5])) + X[10] + 0xa953fd4eU, 12) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + (v[9] ^ (v[1] | ~v[3])) + X[14] + 0xa953fd4eU, 5) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + (v[7] ^ (v[9] | ~v[1])) + X[1] + 0xa953fd4eU, 12) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + (v[5] ^ (v[7] | ~v[9])) + X[3] + 0xa953fd4eU, 13) + v[1];
    v[7] = ROL(v[7], 10);
    v[1] = ROL(v[1] + (v[3] ^ (v[5] | ~v[7])) + X[8] + 0xa953fd4eU, 14) + v[9];
    v[5] = ROL(v[5], 10);
    v[9] = ROL(v[9] + (v[1] ^ (v[3] | ~v[5])) + X[11] + 0xa953fd4eU, 11) + v[7];
    v[3] = ROL(v[3], 10);
    v[7] = ROL(v[7] + (v[9] ^ (v[1] | ~v[3])) + X[6] + 0xa953fd4eU, 8) + v[5];
    v[1] = ROL(v[1], 10);
    v[5] = ROL(v[5] + (v[7] ^ (v[9] | ~v[1])) + X[15] + 0xa953fd4eU, 5) + v[3];
    v[9] = ROL(v[9], 10);
    v[3] = ROL(v[3] + (v[5] ^ (v[7] | ~v[9])) + X[13] + 0xa953fd4eU, 6) + v[1];
    v[7] = ROL(v[7], 10);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[10]) + X[12], 8) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[15], 5) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + (v[2] ^ v[4] ^ v[6]) + X[10], 12) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + (v[10] ^ v[2] ^ v[4]) + X[4], 9) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + (v[8] ^ v[10] ^ v[2]) + X[1], 12) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[10]) + X[5], 5) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[8], 14) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + (v[2] ^ v[4] ^ v[6]) + X[7], 6) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + (v[10] ^ v[2] ^ v[4]) + X[6], 8) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + (v[8] ^ v[10] ^ v[2]) + X[2], 13) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[10]) + X[13], 6) + v[2];
    v[8] = ROL(v[8], 10);
    v[2] = ROL(v[2] + (v[4] ^ v[6] ^ v[8]) + X[14], 5) + v[10];
    v[6] = ROL(v[6], 10);
    v[10] = ROL(v[10] + (v[2] ^ v[4] ^ v[6]) + X[0], 15) + v[8];
    v[4] = ROL(v[4], 10);
    v[8] = ROL(v[8] + (v[10] ^ v[2] ^ v[4]) + X[3], 13) + v[6];
    v[2] = ROL(v[2], 10);
    v[6] = ROL(v[6] + (v[8] ^ v[10] ^ v[2]) + X[9], 11) + v[4];
    v[10] = ROL(v[10], 10);
    v[4] = ROL(v[4] + (v[6] ^ v[8] ^ v[10]) + X[11], 11) + v[2];
    v[8] = ROL(v[8], 10);

    H[0] += v[1]; H[1] += v[3]; H[2] += v[5]; H[3] += v[7]; H[4] += v[10];
    H[5] += v[2]; H[6] += v[4]; H[7] += v[6]; H[8] += v[8]; H[9] += v[9];
}

void ripemd320_update(ripemd320_ctx *ctx, const uint8_t *data, size_t len) {
    ctx->bit_count += (uint64_t)len * 8;
    if (ctx->buf_len > 0) {
        size_t needed = 64 - ctx->buf_len;
        if (len < needed) {
            memcpy(ctx->buf + ctx->buf_len, data, len);
            ctx->buf_len += len;
            return;
        }
        memcpy(ctx->buf + ctx->buf_len, data, needed);
        data += needed; len -= needed; ctx->buf_len = 0;
        ripemd320_compress(ctx->H, ctx->buf);
    }
    while (len >= 64) {
        ripemd320_compress(ctx->H, data);
        data += 64; len -= 64;
    }
    if (len > 0) {
        memcpy(ctx->buf, data, len);
        ctx->buf_len = len;
    }
}

void ripemd320_final(ripemd320_ctx *ctx, uint8_t digest[40]) {
    uint8_t pad[128];
    memset(pad, 0, sizeof(pad));
    memcpy(pad, ctx->buf, ctx->buf_len);
    pad[ctx->buf_len] = 0x80;
    size_t pad_len = (ctx->buf_len < 56) ? 64 : 128;
    memcpy(pad + pad_len - 8, &ctx->bit_count, 8);
    ripemd320_compress(ctx->H, pad);
    if (pad_len == 128) ripemd320_compress(ctx->H, pad + 64);
    memcpy(digest, ctx->H, 40);
}





static PyObject* bytes_to_hex(const uint8_t *digest, size_t len) {
    static const char hex_chars[] = "0123456789abcdef";
    char hex_str[128];
    for (size_t i = 0; i < len; i++) {
        hex_str[2 * i]     = hex_chars[(digest[i] >> 4) & 0x0F];
        hex_str[2 * i + 1] = hex_chars[digest[i] & 0x0F];
    }
    return PyUnicode_FromStringAndSize(hex_str, (Py_ssize_t)(len * 2));
}

/* GOST 34.11-94 */
typedef struct {
    PyObject_HEAD
    gost3411_ctx ctx;
} Gost3411Object;

static PyTypeObject Gost3411Type;

static PyObject* Gost3411_new(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    Gost3411Object *self = (Gost3411Object *)type->tp_alloc(type, 0);
    if (self != NULL) {
        gost3411_init(&self->ctx);
    }
    return (PyObject *)self;
}

static int Gost3411_init(Gost3411Object *self, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"data", NULL};
    Py_buffer buf = {NULL, NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|y*", kwlist, &buf)) {
        return -1;
    }
    gost3411_init(&self->ctx);
    if (buf.buf != NULL) {
        Py_BEGIN_ALLOW_THREADS
        gost3411_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
        Py_END_ALLOW_THREADS
        PyBuffer_Release(&buf);
    }
    return 0;
}

static PyObject* Gost3411_update(Gost3411Object *self, PyObject *args) {
    Py_buffer buf;
    if (!PyArg_ParseTuple(args, "y*", &buf)) {
        return NULL;
    }
    Py_BEGIN_ALLOW_THREADS
    gost3411_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&buf);
    Py_RETURN_NONE;
}

static PyObject* Gost3411_digest(Gost3411Object *self, PyObject *Py_UNUSED(ignored)) {
    gost3411_ctx copy = self->ctx;
    uint8_t out[32];
    Py_BEGIN_ALLOW_THREADS
    gost3411_final(&copy, out);
    Py_END_ALLOW_THREADS
    return PyBytes_FromStringAndSize((const char *)out, 32);
}

static PyObject* Gost3411_hexdigest(Gost3411Object *self, PyObject *Py_UNUSED(ignored)) {
    gost3411_ctx copy = self->ctx;
    uint8_t out[32];
    Py_BEGIN_ALLOW_THREADS
    gost3411_final(&copy, out);
    Py_END_ALLOW_THREADS
    return bytes_to_hex(out, 32);
}

static PyObject* Gost3411_copy(Gost3411Object *self, PyObject *Py_UNUSED(ignored)) {
    Gost3411Object *clone = (Gost3411Object *)Gost3411Type.tp_alloc(&Gost3411Type, 0);
    if (clone != NULL) {
        clone->ctx = self->ctx;
    }
    return (PyObject *)clone;
}

static PyObject* Gost3411_get_digest_size(Gost3411Object *self, void *closure) { return PyLong_FromLong(32); }
static PyObject* Gost3411_get_block_size(Gost3411Object *self, void *closure) { return PyLong_FromLong(32); }
static PyObject* Gost3411_get_name(Gost3411Object *self, void *closure) { return PyUnicode_FromString("gost3411"); }

static PyGetSetDef Gost3411_getseters[] = {
    {"digest_size", (getter)Gost3411_get_digest_size, NULL, "Digest size in bytes", NULL},
    {"block_size", (getter)Gost3411_get_block_size, NULL, "Block size in bytes", NULL},
    {"name", (getter)Gost3411_get_name, NULL, "Algorithm name", NULL},
    {NULL}
};

static PyMethodDef Gost3411_methods[] = {
    {"update", (PyCFunction)Gost3411_update, METH_VARARGS, "Update the hash with data."},
    {"digest", (PyCFunction)Gost3411_digest, METH_NOARGS, "Return the digest as bytes."},
    {"hexdigest", (PyCFunction)Gost3411_hexdigest, METH_NOARGS, "Return the digest as hex string."},
    {"copy", (PyCFunction)Gost3411_copy, METH_NOARGS, "Return a copy of the hash object."},
    {NULL}
};

static PyTypeObject Gost3411Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "cryptolib.gost3411",
    .tp_doc = PyDoc_STR("GOST R 34.11-94 hash object"),
    .tp_basicsize = sizeof(Gost3411Object),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_new = Gost3411_new,
    .tp_init = (initproc)Gost3411_init,
    .tp_methods = Gost3411_methods,
    .tp_getset = Gost3411_getseters,
};

/* RIPEMD-128 */
typedef struct {
    PyObject_HEAD
    ripemd128_ctx ctx;
} Ripemd128Object;

static PyTypeObject Ripemd128Type;

static PyObject* Ripemd128_new(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    Ripemd128Object *self = (Ripemd128Object *)type->tp_alloc(type, 0);
    if (self != NULL) ripemd128_init(&self->ctx);
    return (PyObject *)self;
}

static int Ripemd128_init(Ripemd128Object *self, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"data", NULL};
    Py_buffer buf = {NULL, NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|y*", kwlist, &buf)) return -1;
    ripemd128_init(&self->ctx);
    if (buf.buf != NULL) {
        Py_BEGIN_ALLOW_THREADS
        ripemd128_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
        Py_END_ALLOW_THREADS
        PyBuffer_Release(&buf);
    }
    return 0;
}

static PyObject* Ripemd128_update(Ripemd128Object *self, PyObject *args) {
    Py_buffer buf;
    if (!PyArg_ParseTuple(args, "y*", &buf)) return NULL;
    Py_BEGIN_ALLOW_THREADS
    ripemd128_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&buf);
    Py_RETURN_NONE;
}

static PyObject* Ripemd128_digest(Ripemd128Object *self, PyObject *Py_UNUSED(ignored)) {
    ripemd128_ctx copy = self->ctx;
    uint8_t out[16];
    Py_BEGIN_ALLOW_THREADS
    ripemd128_final(&copy, out);
    Py_END_ALLOW_THREADS
    return PyBytes_FromStringAndSize((const char *)out, 16);
}

static PyObject* Ripemd128_hexdigest(Ripemd128Object *self, PyObject *Py_UNUSED(ignored)) {
    ripemd128_ctx copy = self->ctx;
    uint8_t out[16];
    Py_BEGIN_ALLOW_THREADS
    ripemd128_final(&copy, out);
    Py_END_ALLOW_THREADS
    return bytes_to_hex(out, 16);
}

static PyObject* Ripemd128_copy(Ripemd128Object *self, PyObject *Py_UNUSED(ignored)) {
    Ripemd128Object *clone = (Ripemd128Object *)Ripemd128Type.tp_alloc(&Ripemd128Type, 0);
    if (clone != NULL) clone->ctx = self->ctx;
    return (PyObject *)clone;
}

static PyObject* Ripemd128_get_digest_size(Ripemd128Object *self, void *closure) { return PyLong_FromLong(16); }
static PyObject* Ripemd128_get_block_size(Ripemd128Object *self, void *closure) { return PyLong_FromLong(64); }
static PyObject* Ripemd128_get_name(Ripemd128Object *self, void *closure) { return PyUnicode_FromString("ripemd128"); }

static PyGetSetDef Ripemd128_getseters[] = {
    {"digest_size", (getter)Ripemd128_get_digest_size, NULL, "Digest size in bytes", NULL},
    {"block_size", (getter)Ripemd128_get_block_size, NULL, "Block size in bytes", NULL},
    {"name", (getter)Ripemd128_get_name, NULL, "Algorithm name", NULL},
    {NULL}
};

static PyMethodDef Ripemd128_methods[] = {
    {"update", (PyCFunction)Ripemd128_update, METH_VARARGS, "Update the hash."},
    {"digest", (PyCFunction)Ripemd128_digest, METH_NOARGS, "Return digest as bytes."},
    {"hexdigest", (PyCFunction)Ripemd128_hexdigest, METH_NOARGS, "Return digest as hex string."},
    {"copy", (PyCFunction)Ripemd128_copy, METH_NOARGS, "Return copy of hash object."},
    {NULL}
};

static PyTypeObject Ripemd128Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "cryptolib.ripemd128",
    .tp_doc = PyDoc_STR("RIPEMD-128 hash object"),
    .tp_basicsize = sizeof(Ripemd128Object),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_new = Ripemd128_new,
    .tp_init = (initproc)Ripemd128_init,
    .tp_methods = Ripemd128_methods,
    .tp_getset = Ripemd128_getseters,
};

/* RIPEMD-256 */
typedef struct {
    PyObject_HEAD
    ripemd256_ctx ctx;
} Ripemd256Object;

static PyTypeObject Ripemd256Type;

static PyObject* Ripemd256_new(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    Ripemd256Object *self = (Ripemd256Object *)type->tp_alloc(type, 0);
    if (self != NULL) ripemd256_init(&self->ctx);
    return (PyObject *)self;
}

static int Ripemd256_init(Ripemd256Object *self, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"data", NULL};
    Py_buffer buf = {NULL, NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|y*", kwlist, &buf)) return -1;
    ripemd256_init(&self->ctx);
    if (buf.buf != NULL) {
        Py_BEGIN_ALLOW_THREADS
        ripemd256_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
        Py_END_ALLOW_THREADS
        PyBuffer_Release(&buf);
    }
    return 0;
}

static PyObject* Ripemd256_update(Ripemd256Object *self, PyObject *args) {
    Py_buffer buf;
    if (!PyArg_ParseTuple(args, "y*", &buf)) return NULL;
    Py_BEGIN_ALLOW_THREADS
    ripemd256_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&buf);
    Py_RETURN_NONE;
}

static PyObject* Ripemd256_digest(Ripemd256Object *self, PyObject *Py_UNUSED(ignored)) {
    ripemd256_ctx copy = self->ctx;
    uint8_t out[32];
    Py_BEGIN_ALLOW_THREADS
    ripemd256_final(&copy, out);
    Py_END_ALLOW_THREADS
    return PyBytes_FromStringAndSize((const char *)out, 32);
}

static PyObject* Ripemd256_hexdigest(Ripemd256Object *self, PyObject *Py_UNUSED(ignored)) {
    ripemd256_ctx copy = self->ctx;
    uint8_t out[32];
    Py_BEGIN_ALLOW_THREADS
    ripemd256_final(&copy, out);
    Py_END_ALLOW_THREADS
    return bytes_to_hex(out, 32);
}

static PyObject* Ripemd256_copy(Ripemd256Object *self, PyObject *Py_UNUSED(ignored)) {
    Ripemd256Object *clone = (Ripemd256Object *)Ripemd256Type.tp_alloc(&Ripemd256Type, 0);
    if (clone != NULL) clone->ctx = self->ctx;
    return (PyObject *)clone;
}

static PyObject* Ripemd256_get_digest_size(Ripemd256Object *self, void *closure) { return PyLong_FromLong(32); }
static PyObject* Ripemd256_get_block_size(Ripemd256Object *self, void *closure) { return PyLong_FromLong(64); }
static PyObject* Ripemd256_get_name(Ripemd256Object *self, void *closure) { return PyUnicode_FromString("ripemd256"); }

static PyGetSetDef Ripemd256_getseters[] = {
    {"digest_size", (getter)Ripemd256_get_digest_size, NULL, "Digest size in bytes", NULL},
    {"block_size", (getter)Ripemd256_get_block_size, NULL, "Block size in bytes", NULL},
    {"name", (getter)Ripemd256_get_name, NULL, "Algorithm name", NULL},
    {NULL}
};

static PyMethodDef Ripemd256_methods[] = {
    {"update", (PyCFunction)Ripemd256_update, METH_VARARGS, "Update the hash."},
    {"digest", (PyCFunction)Ripemd256_digest, METH_NOARGS, "Return digest as bytes."},
    {"hexdigest", (PyCFunction)Ripemd256_hexdigest, METH_NOARGS, "Return digest as hex string."},
    {"copy", (PyCFunction)Ripemd256_copy, METH_NOARGS, "Return copy of hash object."},
    {NULL}
};

static PyTypeObject Ripemd256Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "cryptolib.ripemd256",
    .tp_doc = PyDoc_STR("RIPEMD-256 hash object"),
    .tp_basicsize = sizeof(Ripemd256Object),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_new = Ripemd256_new,
    .tp_init = (initproc)Ripemd256_init,
    .tp_methods = Ripemd256_methods,
    .tp_getset = Ripemd256_getseters,
};

/* RIPEMD-320 */
typedef struct {
    PyObject_HEAD
    ripemd320_ctx ctx;
} Ripemd320Object;

static PyTypeObject Ripemd320Type;

static PyObject* Ripemd320_new(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    Ripemd320Object *self = (Ripemd320Object *)type->tp_alloc(type, 0);
    if (self != NULL) ripemd320_init(&self->ctx);
    return (PyObject *)self;
}

static int Ripemd320_init(Ripemd320Object *self, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"data", NULL};
    Py_buffer buf = {NULL, NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|y*", kwlist, &buf)) return -1;
    ripemd320_init(&self->ctx);
    if (buf.buf != NULL) {
        Py_BEGIN_ALLOW_THREADS
        ripemd320_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
        Py_END_ALLOW_THREADS
        PyBuffer_Release(&buf);
    }
    return 0;
}

static PyObject* Ripemd320_update(Ripemd320Object *self, PyObject *args) {
    Py_buffer buf;
    if (!PyArg_ParseTuple(args, "y*", &buf)) return NULL;
    Py_BEGIN_ALLOW_THREADS
    ripemd320_update(&self->ctx, (const uint8_t *)buf.buf, (size_t)buf.len);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&buf);
    Py_RETURN_NONE;
}

static PyObject* Ripemd320_digest(Ripemd320Object *self, PyObject *Py_UNUSED(ignored)) {
    ripemd320_ctx copy = self->ctx;
    uint8_t out[40];
    Py_BEGIN_ALLOW_THREADS
    ripemd320_final(&copy, out);
    Py_END_ALLOW_THREADS
    return PyBytes_FromStringAndSize((const char *)out, 40);
}

static PyObject* Ripemd320_hexdigest(Ripemd320Object *self, PyObject *Py_UNUSED(ignored)) {
    ripemd320_ctx copy = self->ctx;
    uint8_t out[40];
    Py_BEGIN_ALLOW_THREADS
    ripemd320_final(&copy, out);
    Py_END_ALLOW_THREADS
    return bytes_to_hex(out, 40);
}

static PyObject* Ripemd320_copy(Ripemd320Object *self, PyObject *Py_UNUSED(ignored)) {
    Ripemd320Object *clone = (Ripemd320Object *)Ripemd320Type.tp_alloc(&Ripemd320Type, 0);
    if (clone != NULL) clone->ctx = self->ctx;
    return (PyObject *)clone;
}

static PyObject* Ripemd320_get_digest_size(Ripemd320Object *self, void *closure) { return PyLong_FromLong(40); }
static PyObject* Ripemd320_get_block_size(Ripemd320Object *self, void *closure) { return PyLong_FromLong(64); }
static PyObject* Ripemd320_get_name(Ripemd320Object *self, void *closure) { return PyUnicode_FromString("ripemd320"); }

static PyGetSetDef Ripemd320_getseters[] = {
    {"digest_size", (getter)Ripemd320_get_digest_size, NULL, "Digest size in bytes", NULL},
    {"block_size", (getter)Ripemd320_get_block_size, NULL, "Block size in bytes", NULL},
    {"name", (getter)Ripemd320_get_name, NULL, "Algorithm name", NULL},
    {NULL}
};

static PyMethodDef Ripemd320_methods[] = {
    {"update", (PyCFunction)Ripemd320_update, METH_VARARGS, "Update the hash."},
    {"digest", (PyCFunction)Ripemd320_digest, METH_NOARGS, "Return digest as bytes."},
    {"hexdigest", (PyCFunction)Ripemd320_hexdigest, METH_NOARGS, "Return digest as hex string."},
    {"copy", (PyCFunction)Ripemd320_copy, METH_NOARGS, "Return copy of hash object."},
    {NULL}
};

static PyTypeObject Ripemd320Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "cryptolib.ripemd320",
    .tp_doc = PyDoc_STR("RIPEMD-320 hash object"),
    .tp_basicsize = sizeof(Ripemd320Object),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_new = Ripemd320_new,
    .tp_init = (initproc)Ripemd320_init,
    .tp_methods = Ripemd320_methods,
    .tp_getset = Ripemd320_getseters,
};

/* Module definition */
static struct PyModuleDef cryptolibmodule = {
    PyModuleDef_HEAD_INIT,
    .m_name = "cryptolib",
    .m_doc = "Fast C cryptographic hash library (GOST 34.11-94, RIPEMD-128/256/320).",
    .m_size = -1,
};

PyMODINIT_FUNC PyInit_cryptolib(void) {
    PyObject *m;

    if (PyType_Ready(&Gost3411Type) < 0) return NULL;
    if (PyType_Ready(&Ripemd128Type) < 0) return NULL;
    if (PyType_Ready(&Ripemd256Type) < 0) return NULL;
    if (PyType_Ready(&Ripemd320Type) < 0) return NULL;

    m = PyModule_Create(&cryptolibmodule);
    if (m == NULL) return NULL;

    Py_INCREF(&Gost3411Type);
    PyModule_AddObject(m, "gost3411", (PyObject *)&Gost3411Type);

    Py_INCREF(&Ripemd128Type);
    PyModule_AddObject(m, "ripemd128", (PyObject *)&Ripemd128Type);

    Py_INCREF(&Ripemd256Type);
    PyModule_AddObject(m, "ripemd256", (PyObject *)&Ripemd256Type);

    Py_INCREF(&Ripemd320Type);
    PyModule_AddObject(m, "ripemd320", (PyObject *)&Ripemd320Type);

    return m;
}
