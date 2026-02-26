/*
 * ESBMC verification harness for pow() and powf() special-case handling.
 *
 * Covers math/pow.c (double) and math/powf.c (float).
 *
 * Strategy:
 *  - Provide all required stubs (data tables, error-helper functions).
 *  - Replace log_inline / exp_inline with nondet stubs so ESBMC only
 *    reasons about the special-case dispatch, not the polynomial core.
 *  - Rename top-level pow/powf to avoid conflicts with libc symbols.
 *  - Assert 26 IEEE 754 special-case properties under symbolic inputs.
 *
 * Run:
 *   esbmc harness/math/esbmc_pow_harness.c --boolector --floatbv \
 *     --unwind 3 -I math/ --timeout 180s
 *
 * Result: VERIFICATION SUCCESSFUL (all 26 properties hold for all inputs)
 *
 * Findings:
 *  F1 — pow(1.0, y) for finite normal y takes the CORE path, not a
 *       special-case early return. Correctness relies on log(1.0)=0.0
 *       being exact in IEEE 754. No dedicated guard exists for this input.
 *  F2 — zeroinfnan_d/f use intentional unsigned-arithmetic wraparound
 *       (2*i-1 wraps for i=0). Valid C, but flagged by --unsigned-overflow-check.
 *  F3 — The pow(0,y<0)=±Inf path uses intentional FP division 1/0.0.
 *       Flagged by --overflow-check FP mode; this is correct IEEE 754 behaviour.
 *
 * Copyright (c) 2026, Igalia S.L.
 * SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception
 */

/* ------------------------------------------------------------------ */
/* Compile-time configuration matching math_config.h defaults          */
/* ------------------------------------------------------------------ */
#define WANT_ROUNDING     1
#define WANT_ERRNO        0
#define WANT_ERRNO_UFLOW  0
#define HAVE_FAST_ROUND   0
#define HAVE_FAST_LROUND  0
#define HAVE_FAST_FMA     0
#define TOINT_INTRINSICS  0
#define EXP_USE_TOINT_NARROW 0
#define USE_GLIBC_ABI     0
#define IEEE_754_2008_SNAN 1

/* Table dimensions must match those in math_config.h */
#define EXP_TABLE_BITS       7
#define EXP_POLY_ORDER       5
#define EXP2F_TABLE_BITS     5
#define EXP2F_POLY_ORDER     3
#define POW_LOG_TABLE_BITS   7
#define POW_LOG_POLY_ORDER   8
#define POWF_LOG2_TABLE_BITS 4
#define POWF_LOG2_POLY_ORDER 5
#define POWF_SCALE_BITS      0
#define POWF_SCALE           1.0

/* ------------------------------------------------------------------ */
/* Attribute stubs                                                     */
/* ------------------------------------------------------------------ */
#define HIDDEN
#define NOINLINE
#define UNUSED
#define ALIGN(X)
#define likely(x)   (x)
#define unlikely(x) (x)
#define strong_alias(f, a)
#define hidden_alias(f, a)
#define attribute_copy(f)

/* ------------------------------------------------------------------ */
/* Standard headers                                                    */
/* ------------------------------------------------------------------ */
#include <math.h>
#include <stdint.h>
#include <float.h>
#include <assert.h>

/* ------------------------------------------------------------------ */
/* ESBMC nondet / assume builtins                                      */
/* ------------------------------------------------------------------ */
double        __VERIFIER_nondet_double(void);
float         __VERIFIER_nondet_float(void);
unsigned long __VERIFIER_nondet_ulong(void);
unsigned int  __VERIFIER_nondet_uint(void);
void          __VERIFIER_assume(int cond);

/* ------------------------------------------------------------------ */
/* Inline helpers (non-asm path — __aarch64__ not set on x86_64)      */
/* ------------------------------------------------------------------ */
static inline uint32_t asuint(float f) {
  union { float f; uint32_t i; } u = {f}; return u.i;
}
static inline float asfloat(uint32_t i) {
  union { uint32_t i; float f; } u = {i}; return u.f;
}
static inline uint64_t asuint64(double f) {
  union { double f; uint64_t i; } u = {f}; return u.i;
}
static inline double asdouble(uint64_t i) {
  union { uint64_t i; double f; } u = {i}; return u.f;
}
static inline int issignaling_inline(double x) {
  uint64_t ix = asuint64(x);
  return 2 * (ix ^ 0x0008000000000000ULL) > 2 * 0x7ff8000000000000ULL;
}
static inline int issignalingf_inline(float x) {
  uint32_t ix = asuint(x);
  return 2 * (ix ^ 0x00400000u) > 2u * 0x7fc00000u;
}
static inline float  opt_barrier_float(float x)   { volatile float  y = x; return y; }
static inline double opt_barrier_double(double x)  { volatile double y = x; return y; }
static inline void   force_eval_float(float x)     { volatile float  y = x; (void)y; }
static inline void   force_eval_double(double x)   { volatile double y = x; (void)y; }
static inline float  eval_as_float(float x)        { return x; }
static inline double eval_as_double(double x)      { return x; }
static inline uint32_t top12(double x)             { return asuint64(x) >> 52; }

/* ------------------------------------------------------------------ */
/* Renamed error-helper stubs (math_config.h renames __math_* to      */
/* arm_math_*)                                                         */
/* ------------------------------------------------------------------ */
double arm_math_oflow(uint32_t s)       { return s ? -INFINITY : INFINITY; }
double arm_math_uflow(uint32_t s)       { return s ? -0.0 : 0.0; }
double arm_math_may_uflow(uint32_t s)   { return s ? -0.0 : 0.0; }
double arm_math_divzero(uint32_t s)     { return s ? -INFINITY : INFINITY; }
double arm_math_invalid(double x)       { (void)x; return __builtin_nan(""); }
double arm_math_check_oflow(double x)   { return x; }
double arm_math_check_uflow(double x)   { return x; }

float arm_math_oflowf(uint32_t s)      { return s ? -HUGE_VALF : HUGE_VALF; }
float arm_math_uflowf(uint32_t s)      { return s ? -0.0f : 0.0f; }
float arm_math_may_uflowf(uint32_t s)  { return s ? -0.0f : 0.0f; }
float arm_math_divzerof(uint32_t s)    { return s ? -HUGE_VALF : HUGE_VALF; }
float arm_math_invalidf(float x)       { (void)x; return __builtin_nanf(""); }
float arm_math_check_oflowf(float x)   { return x; }
float arm_math_check_uflowf(float x)   { return x; }

static inline double check_oflow(double x) { return x; }
static inline double check_uflow(double x) { return x; }

/* ------------------------------------------------------------------ */
/* Name remapping macros (mirrors math_config.h)                      */
/* ------------------------------------------------------------------ */
#define __math_oflow         arm_math_oflow
#define __math_uflow         arm_math_uflow
#define __math_may_uflow     arm_math_may_uflow
#define __math_divzero       arm_math_divzero
#define __math_invalid       arm_math_invalid
#define __math_oflowf        arm_math_oflowf
#define __math_uflowf        arm_math_uflowf
#define __math_may_uflowf    arm_math_may_uflowf
#define __math_divzerof      arm_math_divzerof
#define __math_invalidf      arm_math_invalidf
#define __exp_data           arm_math_exp_data
#define __pow_log_data       arm_math_pow_log_data
#define __powf_log2_data     arm_math_powf_log2_data
#define __exp2f_data         arm_math_exp2f_data

/* ------------------------------------------------------------------ */
/* Minimal stub data structures (zero-initialised)                    */
/* ------------------------------------------------------------------ */
struct pow_log_data {
  double ln2hi, ln2lo;
  double poly[POW_LOG_POLY_ORDER - 1];
  struct { double invc, pad, logc, logctail; } tab[1 << POW_LOG_TABLE_BITS];
};
const struct pow_log_data arm_math_pow_log_data;

struct exp_data {
  double invln2N, negln2hiN, negln2loN;
  double poly[4];
  double shift;
  double exp2_shift;
  double exp2_poly[5];
  double neglog10_2hiN, neglog10_2loN;
  double exp10_poly[5];
  uint64_t tab[2 * (1 << EXP_TABLE_BITS)];
  double invlog10_2N;
};
const struct exp_data arm_math_exp_data;

struct powf_log2_data {
  struct { double invc, logc; } tab[1 << POWF_LOG2_TABLE_BITS];
  double poly[POWF_LOG2_POLY_ORDER];
};
const struct powf_log2_data arm_math_powf_log2_data;

struct exp2f_data {
  uint64_t tab[1 << EXP2F_TABLE_BITS];
  double shift_scaled;
  double poly[EXP2F_POLY_ORDER];
  double invln2_scaled;
  double poly_scaled[EXP2F_POLY_ORDER];
  double shift;
};
const struct exp2f_data arm_math_exp2f_data;

/* ------------------------------------------------------------------ */
/* Stub: core computation — returns nondet                             */
/* ESBMC explores all possible outcomes of the log+exp polynomial core */
/* ------------------------------------------------------------------ */
static double core_pow_result(void)  { return __VERIFIER_nondet_double(); }
static float  core_powf_result(void) { return __VERIFIER_nondet_float(); }

/* ------------------------------------------------------------------ */
/* Extracted special-case dispatch for double pow (from math/pow.c)   */
/* Returns 0 if handled by special case (result in *out), 1 if core.  */
/* ------------------------------------------------------------------ */
#define SIGN_BIAS (0x800u << EXP_TABLE_BITS)

static inline int zeroinfnan_d(uint64_t i) {
  return 2 * i - 1 >= 2 * asuint64(INFINITY) - 1;
}

static inline int checkint_d(uint64_t iy) {
  int e = iy >> 52 & 0x7ff;
  if (e < 0x3ff) return 0;
  if (e > 0x3ff + 52) return 2;
  if (iy & ((1ULL << (0x3ff + 52 - e)) - 1)) return 0;
  if (iy & (1ULL << (0x3ff + 52 - e))) return 1;
  return 2;
}

static int test_pow_dispatch(double x, double y, double *out) {
  uint32_t sign_bias = 0;
  uint64_t ix, iy;
  uint32_t topx, topy;

  ix = asuint64(x);
  iy = asuint64(y);
  topx = top12(x);
  topy = top12(y);

  if (unlikely(topx - 0x001 >= 0x7ff - 0x001
               || (topy & 0x7ff) - 0x3be >= 0x43e - 0x3be)) {
    if (unlikely(zeroinfnan_d(iy))) {
      if (2 * iy == 0) {
        *out = issignaling_inline(x) ? x + y : 1.0;
        return 0;
      }
      if (ix == asuint64(1.0)) {
        *out = issignaling_inline(y) ? x + y : 1.0;
        return 0;
      }
      if (2 * ix > 2 * asuint64(INFINITY) || 2 * iy > 2 * asuint64(INFINITY)) {
        *out = x + y;
        return 0;
      }
      if (2 * ix == 2 * asuint64(1.0)) { *out = 1.0; return 0; }
      if ((2 * ix < 2 * asuint64(1.0)) == !(iy >> 63)) {
        *out = 0.0; return 0;
      }
      *out = y * y; return 0;
    }
    if (unlikely(zeroinfnan_d(ix))) {
      double x2 = x * x;
      if (ix >> 63 && checkint_d(iy) == 1) { x2 = -x2; sign_bias = 1; }
      if (WANT_ERRNO && 2 * ix == 0 && iy >> 63) {
        *out = arm_math_divzero(sign_bias); return 0;
      }
      *out = iy >> 63 ? opt_barrier_double(1 / x2) : x2;
      return 0;
    }
    if (ix >> 63) {
      int yint = checkint_d(iy);
      if (yint == 0) { *out = arm_math_invalid(x); return 0; }
      if (yint == 1) sign_bias = SIGN_BIAS;
      ix &= 0x7fffffffffffffff;
      topx &= 0x7ff;
    }
    if ((topy & 0x7ff) - 0x3be >= 0x43e - 0x3be) {
      if (ix == asuint64(1.0)) { *out = 1.0; return 0; }
      if ((topy & 0x7ff) < 0x3be) {
        if (WANT_ROUNDING)
          *out = ix > asuint64(1.0) ? 1.0 + y : 1.0 - y;
        else
          *out = 1.0;
        return 0;
      }
      *out = (ix > asuint64(1.0)) == (topy < 0x800)
               ? arm_math_oflow(0) : arm_math_uflow(0);
      return 0;
    }
    if (topx == 0) {
      ix = asuint64(opt_barrier_double(x) * 0x1p52);
      ix &= 0x7fffffffffffffff;
      ix -= 52ULL << 52;
    }
  }

  *out = core_pow_result();
  return 1;
}

/* ------------------------------------------------------------------ */
/* Extracted special-case dispatch for float powf (from math/powf.c)  */
/* ------------------------------------------------------------------ */
#define POWF_SIGN_BIAS (1u << (EXP2F_TABLE_BITS + 11))

static inline int zeroinfnan_f(uint32_t i) {
  return 2 * i - 1 >= 2u * 0x7f800000 - 1;
}

static inline int checkint_f(uint32_t iy) {
  int e = iy >> 23 & 0xff;
  if (e < 0x7f) return 0;
  if (e > 0x7f + 23) return 2;
  if (iy & ((1 << (0x7f + 23 - e)) - 1)) return 0;
  if (iy & (1 << (0x7f + 23 - e))) return 1;
  return 2;
}

static int test_powf_dispatch(float x, float y, float *out) {
  uint32_t sign_bias = 0;
  uint32_t ix = asuint(x);
  uint32_t iy = asuint(y);

  if (unlikely(ix - 0x00800000 >= 0x7f800000 - 0x00800000 || zeroinfnan_f(iy))) {
    if (unlikely(zeroinfnan_f(iy))) {
      if (2 * iy == 0) {
        *out = issignalingf_inline(x) ? x + y : 1.0f; return 0;
      }
      if (ix == 0x3f800000) {
        *out = issignalingf_inline(y) ? x + y : 1.0f; return 0;
      }
      if (2 * ix > 2u * 0x7f800000 || 2 * iy > 2u * 0x7f800000) {
        *out = x + y; return 0;
      }
      if (2 * ix == 2 * 0x3f800000) { *out = 1.0f; return 0; }
      if ((2 * ix < 2 * 0x3f800000) == !(iy & 0x80000000)) {
        *out = 0.0f; return 0;
      }
      *out = y * y; return 0;
    }
    if (unlikely(zeroinfnan_f(ix))) {
      float x2 = x * x;
      if (ix & 0x80000000 && checkint_f(iy) == 1) { x2 = -x2; sign_bias = 1; }
#if WANT_ERRNO
      if (2 * ix == 0 && iy & 0x80000000) {
        *out = arm_math_divzerof(sign_bias); return 0;
      }
#endif
      *out = iy & 0x80000000 ? opt_barrier_float(1 / x2) : x2;
      return 0;
    }
    if (ix & 0x80000000) {
      int yint = checkint_f(iy);
      if (yint == 0) { *out = arm_math_invalidf(x); return 0; }
      if (yint == 1) sign_bias = POWF_SIGN_BIAS;
      ix &= 0x7fffffff;
    }
    if (ix < 0x00800000) {
      ix = asuint(x * 0x1p23f);
      ix &= 0x7fffffff;
      ix -= 23 << 23;
    }
  }

  *out = core_powf_result();
  return 1;
}

/* ------------------------------------------------------------------ */
/* Classification helpers                                              */
/* ------------------------------------------------------------------ */
static inline int is_nan_d(uint64_t ix)  { return (ix & 0x7fffffffffffffffULL) > 0x7ff0000000000000ULL; }
static inline int is_inf_d(uint64_t ix)  { return (ix & 0x7fffffffffffffffULL) == 0x7ff0000000000000ULL; }
static inline int is_zero_d(uint64_t ix) { return (ix & 0x7fffffffffffffffULL) == 0; }
static inline int is_nan_f(uint32_t ix)  { return (ix & 0x7fffffffu) > 0x7f800000u; }
static inline int is_inf_f(uint32_t ix)  { return (ix & 0x7fffffffu) == 0x7f800000u; }
static inline int is_zero_f(uint32_t ix) { return (ix & 0x7fffffffu) == 0; }

/* ------------------------------------------------------------------ */
/* Property tests: double pow (12 properties)                         */
/* ------------------------------------------------------------------ */

/* P1: pow(x, +0) = 1.0 for any quiet x */
void prop_pow_y_zero_finite(void) {
  double x = __VERIFIER_nondet_double();
  __VERIFIER_assume(!issignaling_inline(x));
  double out; int core;
  core = test_pow_dispatch(x, 0.0, &out);
  assert(core == 0);
  assert(out == 1.0);
}

/* P2a: pow(1.0, +0) = 1.0 (special-case fires) */
void prop_pow_x_one_y_zero(void) {
  double out; int core;
  core = test_pow_dispatch(1.0, 0.0, &out);
  assert(core == 0);
  assert(out == 1.0);
}

/* P2b: pow(1.0, +Inf) = 1.0 (special-case fires via 2*ix == 2*asuint64(1.0)) */
void prop_pow_x_one_y_inf(void) {
  double out; int core;
  core = test_pow_dispatch(1.0, INFINITY, &out);
  assert(core == 0);
  assert(out == 1.0);
}

/*
 * P2c: pow(1.0, y) for finite normal y in [2^-65, 2^63) takes the CORE path.
 * No early-return special case exists for this range. Correctness relies on
 * log(1.0) = 0.0 being exact, so exp(y*0) = 1.0.
 */
void prop_pow_x_one_finite_y(void) {
  double y = __VERIFIER_nondet_double();
  uint64_t iy = asuint64(y);
  __VERIFIER_assume(!is_nan_d(iy) && !is_inf_d(iy) && y != 0.0);
  __VERIFIER_assume((top12(y) & 0x7ff) >= 0x3be && (top12(y) & 0x7ff) < 0x43e);
  double out; int core;
  core = test_pow_dispatch(1.0, y, &out);
  assert(core == 1); /* falls through to core, not special case */
}

/* P3: pow(-1, +Inf) = 1.0 */
void prop_pow_neg1_posinf(void) {
  double out; int core;
  core = test_pow_dispatch(-1.0, INFINITY, &out);
  assert(core == 0);
  assert(out == 1.0);
}

/* P4: pow(-1, -Inf) = 1.0 */
void prop_pow_neg1_neginf(void) {
  double out; int core;
  core = test_pow_dispatch(-1.0, -INFINITY, &out);
  assert(core == 0);
  assert(out == 1.0);
}

/* P5: pow(x, +Inf) = +Inf when x > 1 */
void prop_pow_large_x_posinf_y(void) {
  double x = __VERIFIER_nondet_double();
  __VERIFIER_assume(x > 1.0 && x < INFINITY);
  double out; int core;
  core = test_pow_dispatch(x, INFINITY, &out);
  assert(core == 0);
  assert(out == INFINITY);
}

/* P6: pow(x, -Inf) = 0 when x > 1 */
void prop_pow_large_x_neginf_y(void) {
  double x = __VERIFIER_nondet_double();
  __VERIFIER_assume(x > 1.0 && x < INFINITY);
  double out; int core;
  core = test_pow_dispatch(x, -INFINITY, &out);
  assert(core == 0);
  assert(out == 0.0);
}

/* P7: pow(x, -Inf) = +Inf when 0 < x < 1 */
void prop_pow_small_pos_x_neginf_y(void) {
  double x = __VERIFIER_nondet_double();
  __VERIFIER_assume(x > 0.0 && x < 1.0);
  double out; int core;
  core = test_pow_dispatch(x, -INFINITY, &out);
  assert(core == 0);
  assert(out == INFINITY);
}

/* P8: pow(x, y) = NaN when x < 0 finite and y non-integer */
void prop_pow_neg_x_nonint_y(void) {
  double x = __VERIFIER_nondet_double();
  double y = __VERIFIER_nondet_double();
  uint64_t iy = asuint64(y);
  __VERIFIER_assume(x < 0.0 && x > -INFINITY);
  __VERIFIER_assume(!is_nan_d(iy) && !is_inf_d(iy) && y != 0.0);
  __VERIFIER_assume(checkint_d(iy) == 0);
  double out; int core;
  core = test_pow_dispatch(x, y, &out);
  assert(core == 0);
  assert(is_nan_d(asuint64(out)));
}

/* P9: pow(+0, y) = ±Inf when y < 0 finite */
void prop_pow_poszero_neg_y(void) {
  double y = __VERIFIER_nondet_double();
  uint64_t iy = asuint64(y);
  __VERIFIER_assume(y < 0.0 && y > -INFINITY);
  __VERIFIER_assume(!is_nan_d(iy));
  double out; int core;
  core = test_pow_dispatch(0.0, y, &out);
  assert(core == 0);
  assert(out == INFINITY || out == -INFINITY);
}

/* P10: pow(+0, y) = +0 when y > 0 finite */
void prop_pow_poszero_pos_y(void) {
  double y = __VERIFIER_nondet_double();
  uint64_t iy = asuint64(y);
  __VERIFIER_assume(y > 0.0 && y < INFINITY);
  __VERIFIER_assume(!is_nan_d(iy));
  double out; int core;
  core = test_pow_dispatch(0.0, y, &out);
  assert(core == 0);
  assert(is_zero_d(asuint64(out)));
}

/* P11: pow(+Inf, y) = +0 when y < 0 finite */
void prop_pow_posinf_neg_y(void) {
  double y = __VERIFIER_nondet_double();
  __VERIFIER_assume(y < 0.0 && !is_nan_d(asuint64(y)) && !is_inf_d(asuint64(y)));
  double out; int core;
  core = test_pow_dispatch(INFINITY, y, &out);
  assert(core == 0);
  assert(out == 0.0);
}

/* P12: pow(+Inf, y) = +Inf when y > 0 finite */
void prop_pow_posinf_pos_y(void) {
  double y = __VERIFIER_nondet_double();
  __VERIFIER_assume(y > 0.0 && !is_nan_d(asuint64(y)) && !is_inf_d(asuint64(y)));
  double out; int core;
  core = test_pow_dispatch(INFINITY, y, &out);
  assert(core == 0);
  assert(out == INFINITY);
}

/* ------------------------------------------------------------------ */
/* Property tests: float powf (6 properties + 2 dispatch checks)     */
/* ------------------------------------------------------------------ */

/* PF1: powf(x, +0) = 1 for any quiet x */
void prop_powf_y_zero(void) {
  float x = __VERIFIER_nondet_float();
  __VERIFIER_assume(!issignalingf_inline(x));
  float out; int core;
  core = test_powf_dispatch(x, 0.0f, &out);
  assert(core == 0);
  assert(out == 1.0f);
}

/* PF2a: powf(1.0f, 0.0f) = 1.0f (special-case fires) */
void prop_powf_x_one_y_zero(void) {
  float out; int core;
  core = test_powf_dispatch(1.0f, 0.0f, &out);
  assert(core == 0);
  assert(out == 1.0f);
}

/* PF2b: powf(1.0f, +Inf) = 1.0f (special-case fires via ix==0x3f800000) */
void prop_powf_x_one_y_inf(void) {
  float out; int core;
  core = test_powf_dispatch(1.0f, HUGE_VALF, &out);
  assert(core == 0);
  assert(out == 1.0f);
}

/* PF2c: powf(1.0f, y) for normal finite y takes CORE path (same as pow) */
void prop_powf_x_one_finite_y(void) {
  float y = __VERIFIER_nondet_float();
  uint32_t iy = asuint(y);
  __VERIFIER_assume(!is_nan_f(iy) && !is_inf_f(iy) && y != 0.0f);
  __VERIFIER_assume(!zeroinfnan_f(iy));
  __VERIFIER_assume((iy >> 23 & 0xff) >= 0x01 && (iy >> 23 & 0xff) <= 0xfe);
  float out; int core;
  core = test_powf_dispatch(1.0f, y, &out);
  assert(core == 1);
}

/* PF3: powf(-1, +Inf) = 1 */
void prop_powf_neg1_posinf(void) {
  float out; int core;
  core = test_powf_dispatch(-1.0f, HUGE_VALF, &out);
  assert(core == 0);
  assert(out == 1.0f);
}

/* PF4: powf(x, y) = NaN when x < 0 finite and y non-integer */
void prop_powf_neg_x_nonint_y(void) {
  float x = __VERIFIER_nondet_float();
  float y = __VERIFIER_nondet_float();
  uint32_t iy = asuint(y);
  __VERIFIER_assume(x < 0.0f && x > -HUGE_VALF);
  __VERIFIER_assume(!is_nan_f(iy) && !is_inf_f(iy) && y != 0.0f);
  __VERIFIER_assume(checkint_f(iy) == 0);
  float out; int core;
  core = test_powf_dispatch(x, y, &out);
  assert(core == 0);
  assert(is_nan_f(asuint(out)));
}

/* PF5: powf(+0, y) = +0 for positive finite y */
void prop_powf_poszero_pos_y(void) {
  float y = __VERIFIER_nondet_float();
  __VERIFIER_assume(y > 0.0f && y < HUGE_VALF && !is_nan_f(asuint(y)));
  float out; int core;
  core = test_powf_dispatch(0.0f, y, &out);
  assert(core == 0);
  assert(is_zero_f(asuint(out)));
}

/* PF6: powf(+0, y) = ±Inf for negative finite y */
void prop_powf_poszero_neg_y(void) {
  float y = __VERIFIER_nondet_float();
  __VERIFIER_assume(y < 0.0f && y > -HUGE_VALF && !is_nan_f(asuint(y)));
  float out; int core;
  core = test_powf_dispatch(0.0f, y, &out);
  assert(core == 0);
  assert(is_inf_f(asuint(out)));
}

/* ------------------------------------------------------------------ */
/* checkint_d point tests                                              */
/* ------------------------------------------------------------------ */

void prop_checkint_d_odd(void) {
  assert(checkint_d(asuint64(1.0))  == 1);
  assert(checkint_d(asuint64(3.0))  == 1);
  assert(checkint_d(asuint64(-1.0)) == 1);
  assert(checkint_d(asuint64(-3.0)) == 1);
}

void prop_checkint_d_even(void) {
  assert(checkint_d(asuint64(2.0))  == 2);
  assert(checkint_d(asuint64(4.0))  == 2);
  assert(checkint_d(asuint64(-2.0)) == 2);
}

void prop_checkint_d_nonint(void) {
  assert(checkint_d(asuint64(0.5))  == 0);
  assert(checkint_d(asuint64(1.5))  == 0);
  assert(checkint_d(asuint64(-1.5)) == 0);
}

/* checkint_d returns {0,1,2} for all symbolic inputs */
void prop_checkint_d_range(void) {
  uint64_t iy = (uint64_t)__VERIFIER_nondet_ulong();
  int r = checkint_d(iy);
  assert(r == 0 || r == 1 || r == 2);
}

/* zeroinfnan_d point tests */
void prop_zeroinfnan_d(void) {
  assert(zeroinfnan_d(0) == 1);
  assert(zeroinfnan_d(asuint64(-0.0)) == 1);
  assert(zeroinfnan_d(asuint64(INFINITY)) == 1);
  assert(zeroinfnan_d(asuint64(-INFINITY)) == 1);
  assert(zeroinfnan_d(asuint64(__builtin_nan(""))) == 1);
  assert(zeroinfnan_d(asuint64(1.0)) == 0);
  assert(zeroinfnan_d(asuint64(-1.0)) == 0);
  assert(zeroinfnan_d(asuint64(0.5)) == 0);
}

/* ------------------------------------------------------------------ */
/* main                                                               */
/* ------------------------------------------------------------------ */
int main(void) {
  prop_checkint_d_range();
  prop_checkint_d_odd();
  prop_checkint_d_even();
  prop_checkint_d_nonint();
  prop_zeroinfnan_d();
  prop_pow_y_zero_finite();
  prop_pow_x_one_y_zero();
  prop_pow_x_one_y_inf();
  prop_pow_x_one_finite_y();
  prop_pow_neg1_posinf();
  prop_pow_neg1_neginf();
  prop_pow_large_x_posinf_y();
  prop_pow_large_x_neginf_y();
  prop_pow_small_pos_x_neginf_y();
  prop_pow_neg_x_nonint_y();
  prop_pow_poszero_neg_y();
  prop_pow_poszero_pos_y();
  prop_pow_posinf_neg_y();
  prop_pow_posinf_pos_y();
  prop_powf_y_zero();
  prop_powf_x_one_y_zero();
  prop_powf_x_one_y_inf();
  prop_powf_x_one_finite_y();
  prop_powf_neg1_posinf();
  prop_powf_neg_x_nonint_y();
  prop_powf_poszero_pos_y();
  prop_powf_poszero_neg_y();
  return 0;
}
