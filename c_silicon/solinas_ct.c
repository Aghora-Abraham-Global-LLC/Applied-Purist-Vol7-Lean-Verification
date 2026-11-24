#include <stdint.h>

#define SOLINAS_P64 0xffffffffffffffc5ULL /* 2^64 - 59 */
#define SOLINAS_C64 59ULL

uint64_t canon_sub_p64_ct(uint64_t s) {
  uint64_t ge = (uint64_t)(s >= SOLINAS_P64);
  uint64_t mask = (uint64_t)0 - ge;
  return s - (SOLINAS_P64 & mask);
}

uint64_t add_mod_p64_ct(uint64_t a, uint64_t b) {
  uint64_t s0 = a + b;
  uint64_t c0 = (uint64_t)(s0 < a);
  uint64_t s1 = s0 + c0 * SOLINAS_C64;
  uint64_t c1 = (uint64_t)(s1 < s0);
  uint64_t s2 = s1 + c1 * SOLINAS_C64;
  return canon_sub_p64_ct(s2);
}

uint64_t sub_mod_p64_ct(uint64_t a, uint64_t b) {
  uint64_t ca = canon_sub_p64_ct(a);
  uint64_t cb = canon_sub_p64_ct(b);
  uint64_t borrow = (uint64_t)(ca < cb);
  uint64_t diff = ca - cb;
  uint64_t mask = (uint64_t)0 - borrow;
  return diff + (SOLINAS_P64 & mask);
}

static inline void mul64_to_128(uint64_t a, uint64_t b, uint64_t *hi, uint64_t *lo) {
  uint64_t a0 = a & 0xffffffffULL, a1 = a >> 32;
  uint64_t b0 = b & 0xffffffffULL, b1 = b >> 32;
  uint64_t p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
  uint64_t mid = (p00 >> 32) + (p01 & 0xffffffffULL) + (p10 & 0xffffffffULL);
  *lo = (p00 & 0xffffffffULL) | (mid << 32);
  *hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
}

uint64_t mul_mod_p64_3pass_ct(uint64_t a, uint64_t b) {
  uint64_t z_hi, z_lo, p1_hi, p1_lo;
  mul64_to_128(a, b, &z_hi, &z_lo);
  mul64_to_128(z_hi, SOLINAS_C64, &p1_hi, &p1_lo);
  uint64_t s1_lo = z_lo + p1_lo;
  uint64_t s1_hi = p1_hi + (uint64_t)(s1_lo < z_lo);
  uint64_t s2_lo = s1_lo + s1_hi * SOLINAS_C64;
  uint64_t s2_hi = (uint64_t)(s2_lo < s1_lo);
  uint64_t s3 = s2_lo + s2_hi * SOLINAS_C64;
  return canon_sub_p64_ct(s3);
}

uint64_t rotl64_ct(uint64_t x, uint32_t k) {
  uint32_t s = k & 63u;
  return (x << s) | (x >> ((-s) & 63u));
}

uint64_t rotr64_ct(uint64_t x, uint32_t k) {
  uint32_t s = k & 63u;
  return (x >> s) | (x << ((-s) & 63u));
}

uint64_t pack_ntt46_ct(uint32_t c0, uint32_t c1) {
  return ((uint64_t)(c0 & 0x7fffffu)) | (((uint64_t)(c1 & 0x7fffffu)) << 23);
}

uint32_t unpack_ntt46_c0_ct(uint64_t w) { return (uint32_t)(w & 0x7fffffu); }
uint32_t unpack_ntt46_c1_ct(uint64_t w) { return (uint32_t)((w >> 23) & 0x7fffffu); }
uint32_t read_morton30_ftz_safe(uint32_t raw_f32_bits) { return raw_f32_bits & 0x3fffffffu; }

void sp800_88_wipe_u32(volatile uint32_t *ptr, uint32_t word_count) {
  for (uint32_t i = 0; i < word_count; ++i) ptr[i] = 0u;
}

void solinas_ivc64_step_batch(
  uint32_t *packets,
  const uint32_t *ingress_morton30_words,
  uint32_t node_count,
  uint32_t domain_tag,
  uint32_t zeroize_on
) {
  uint32_t zmask = (uint32_t)0 - (uint32_t)(zeroize_on != 1u);
  for (uint32_t i = 0; i < node_count; ++i) {
    uint32_t base = i * 16u;
    uint32_t m30 = (ingress_morton30_words[i] & 0x3fffffffu) | (packets[base + 14u] & 0x3fffffffu);
    uint64_t lo = ((uint64_t)packets[base]) | (((uint64_t)packets[base + 1u]) << 32);
    uint64_t canon = add_mod_p64_ct(lo, (uint64_t)(domain_tag ^ m30));
    packets[base] = ((uint32_t)(canon & 0xffffffffULL)) & zmask;
    packets[base + 1u] = ((uint32_t)(canon >> 32)) & zmask;
    packets[base + 2u] &= zmask;
    packets[base + 3u] &= zmask;
    for (uint32_t k = 4u; k < 12u; ++k) packets[base + k] &= zmask;
    packets[base + 12u] = (packets[base + 12u] ^ (uint32_t)(canon & 0xffffffffULL)) & zmask;
    packets[base + 13u] = (packets[base + 13u] ^ (uint32_t)(canon >> 32)) & zmask;
    packets[base + 14u] = m30;
    packets[base + 15u] = (zeroize_on == 1u) ? 0u : 1u;
  }
}
