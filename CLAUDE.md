# ARM Optimized Routines — CLAUDE.md

## Project Overview

This is the **ARM Optimized Routines** library, maintained by Arm Limited. It provides
high-performance, architecture-aware implementations of common C library functions
(math, string, networking) optimized specifically for ARM processors (AArch64/ARM32).

Code is designed for upstreaming into glibc, bionic, and other C libraries. It is
dual-licensed: MIT OR Apache-2.0 WITH LLVM-exception.

**Repository**: https://github.com/ARM-software/optimized-routines
**Language standard**: C99, ARM64/ARM32 assembly
**Release cadence**: biannual (vYY.MM format)

---

## Repository Structure

```
optimized-routines/
├── fp/                    # Software floating-point arithmetic (no-HW-FP platforms)
│   ├── armv6-m/           # Thumb-1 for ARMv6-M and ARMv8-M Baseline
│   ├── at32/              # ARM/Thumb-2 compatible
│   └── common/            # Shared fp sources
├── math/                  # Elementary and transcendental math functions
│   ├── aarch64/           # AArch64 scalar implementations + shared data tables
│   │   ├── advsimd/       # 128-bit NEON vector implementations (~92 files)
│   │   ├── sve/           # SVE scalable-vector implementations (~90 files)
│   │   └── experimental/  # Non-production; excluded from standard builds
│   ├── include/           # Public headers (mathlib.h, test_sig.h, test_defs.h)
│   ├── test/              # ULP tester, mathbench, mathtest, test vectors
│   └── tools/             # Sollya scripts for Remez/FPMinimax polynomial generation
├── string/                # String/memory routines
│   ├── aarch64/           # AArch64 assembly implementations
│   │   └── experimental/  # Non-production experimental routines
│   ├── arm/               # ARM 32-bit implementations
│   ├── x86_64/            # x86_64 fallback implementations
│   ├── include/           # Public headers
│   ├── test/              # String tests
│   └── bench/             # String benchmarks
├── networking/            # Network checksum optimizations
│   ├── aarch64/           # AArch64 SIMD checksum implementations
│   ├── arm/               # ARM SIMD checksum
│   ├── include/           # Public headers
│   └── test/              # Networking tests
├── Makefile               # Top-level build file
└── config.mk.dist         # Build configuration template (copy to config.mk)
```

---

## Build System

**Tool**: GNU Make only (not BSD make).

**Setup**:
```bash
cp config.mk.dist config.mk
# edit config.mk as needed
make
make check
```

**Key make targets**:
- `make all-<sub>` / `make check-<sub>` — build/test a single subproject
- `make all-math` / `make check-math`
- `make all-string` / `make check-string`
- `make all-networking` / `make check-networking`
- `make prefix=/path install` — install headers and libraries

**Critical config.mk variables**:
- `ARCH` — target architecture: `aarch64`, `arm`, `x86_64`
- `CC` / `CROSS_COMPILE` — target compiler / cross-compile prefix
- `HOST_CC` — host compiler (for test generators run on build machine)
- `EMULATOR` — for cross-testing (e.g., `qemu-aarch64-static`)
- `USE_MPFR` — enable MPFR-based ULP reference testing
- `WANT_SVE_TESTS` — enable SVE tests (auto-enabled on AArch64)
- `WANT_EXPERIMENTAL_MATH` — include experimental routines
- `WANT_ERRNO` — set errno per ISO C (default 0, not set)
- `USE_GLIBC_ABI` — expose `*_finite` and glibc-hidden symbols

**Math-specific compiler flags** (set in config.mk):
- `-frounding-math -fexcess-precision=standard` — correct rounding behaviour
- `-ffp-contract=fast` — enables FMA contraction
- `-fno-math-errno` — allows inlining builtins
- `-fno-stack-protector` — for hotpath performance

**String-specific flags**:
- `-falign-functions=64` — cache-line alignment for string functions

**Compiler requirements**:
- GCC ≥ 10 or LLVM/Clang ≥ 5 for SVE ACLE support
- No autoconf/automake; intentionally minimal dependency on toolchain features

---

## Subproject: Math

### What it provides

Scalar libm replacements and vector libmvec variants:
- **Scalar**: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`,
  `exp`, `exp2`, `exp10`, `expm1`, `log`, `log2`, `log10`, `log1p`, `pow`, `cbrt`,
  `sqrt`, `hypot`, `erf`, `erfc`, `tgamma`, and their `f`-suffixed float variants.
- **C23 additions**: `sinpi`, `cospi`, `tanpi`, `atan2pi`, `sincospi`, and float variants.
- **Vector (AdvSIMD)**: `_ZGVnN4v_*` (float32x4) and `_ZGVnN2v_*` (float64x2) families.
- **Vector (SVE)**: `_ZGVsMxv_*` families with predicate mask arguments.
- **Experimental** (gated on `WANT_EXPERIMENTAL_MATH`): `erfinv`, `erfinvf`, low-accuracy
  scalar variants, fast sinf/cosf/powf/expf.

### Public API

`math/include/mathlib.h` — declares all scalar and vector functions. Vector declarations
use `__vpcs` (`__aarch64_vector_pcs__`) for NEON and svXxx types for SVE.

### Accuracy requirements (enforced by CI)

| Variant | ULP bound | Test method |
|---|---|---|
| Double-precision scalar | < 0.66 ULP | Random sampling |
| Single-precision scalar | < 1 ULP | Exhaustive |
| Performance-optimized | < 3.5 ULP | Random sampling |

### Implementation structure pattern

Each math function typically follows this pattern:
1. **Special case detection**: NaN, Inf, denormals, domain errors (handled via `__math_invalid`, `__math_divzero`, etc.)
2. **Range reduction**: Map input to a small interval
3. **Polynomial approximation**: Remez-optimized coefficients from Sollya
4. **Reconstruction**: Apply range reduction inverse
5. **errno/exception handling**: Isolated from hot path

Data tables live as `.c` files in `math/aarch64/` (e.g., `v_exp_data.c`, `v_pow_log_data.c`).

### Testing tools

- `build/bin/ulp` — ULP error checker (single precision: exhaustive; double: random)
  ```bash
  ./build/bin/ulp -q -e 3.0 sinf 0 inf
  ./build/bin/ulp -q -e 3.0 sin 0 inf 1000000
  ```
- `build/bin/mathbench` — throughput/latency benchmarks (ns/elem, ns/call)
- `build/bin/mathtest` — directed test case runner
- `math/test/rtest/` — random test case generator
- `math/test/testcases/` — directed test vectors (special values, edge cases)

Requires `libmpfr-dev libmpc-dev` for reference ULP calculations.

---

## Subproject: String

### What it provides

AArch64 assembly implementations of standard string/memory functions:

| Function | Variants available |
|---|---|
| `memcpy` | base, AdvSIMD, SVE, MOPS |
| `memmove` | base, MOPS |
| `memset` | base, SVE, MOPS |
| `memchr` | base, MTE |
| `memrchr` | base |
| `memcmp` | base |
| `strcpy` / `stpcpy` | base |
| `strcmp` / `strncmp` | base |
| `strchr` / `strrchr` | base, MTE |
| `strchrnul` | base, MTE |
| `strlen` / `strnlen` | base, MTE |

**MTE variants** (Memory Tagging Extension): special handling for hardware-tagged pointers.
**MOPS variants** (Memory Operations Extension, ARMv8.8+): single-instruction bulk operations.
**SVE variants**: variable-length vector (128–2048 bit) implementations.

### Assembly conventions

- Entry file per function: `string/aarch64/<func>.S`
- All use `asmdefs.h` for common macros
- Internal symbols prefixed with `__` (e.g., `__memcpy_aarch64`)
- GNU property notes controlled by `WANT_GNU_PROPERTY`
- 64-byte function alignment (`-falign-functions=64`)

### Common implementation techniques

- **Tail copying**: always copy last block from the end — avoids branch for tail
- **Overlapping loads**: safe for forward copies; overlap detection for memmove
- **Unaligned access**: ARM allows unaligned loads; implementations exploit this
- **Software pipelining**: large loops structured for dual-issue scheduling
- **Branchless sequences**: used where branch misprediction cost is high

---

## Subproject: Networking

Provides optimized IP checksum computation:
- `networking/aarch64/` — AdvSIMD and SVE checksum implementations
- `networking/arm/` — ARM NEON checksum
- Assertion checking available via `-DWANT_ASSERT`
- Compiled with `-O2 -fno-tree-vectorize -funroll-loops` (manual vectorization)

---

## Subproject: FP (Software Floating-Point)

For platforms without hardware FP (embedded ARMv6-M/ARMv8-M):
- Basic ops: add, sub, mul, div, recip, sqrt
- Type conversions: float/double/int
- Variants in `fp/armv6-m/`, `fp/at32/`, `fp/common/`

---

## Coding Conventions

### C code

- **Standard**: C99
- **Style**: GNU Coding Standards; `clang-format` with GCC contrib style
- **Naming**: internal symbols in reserved namespace (double-underscore prefix)
- **File headers**: SPDX identifier + Arm Limited copyright on every file
- **Comments**: sparse; only for non-obvious logic
- **errno/fenv**: isolated from approximation logic using helper functions
- **No autoconf**: all config via `config.mk` make variables

### Assembly code

- AArch64 gas syntax
- Assumptions and register usage documented in comments
- Architecture extension use controlled by `__ARM_FEATURE_*` macros at compile time
- `.arch` directives for extension-specific instructions

### Symbol naming

- `__func_aarch64` — internal AArch64 symbol
- `_ZGVnN4v_func` — AdvSIMD vector ABI (4 lanes, float32)
- `_ZGVnN2v_func` — AdvSIMD vector ABI (2 lanes, float64)
- `_ZGVsMxv_func` — SVE vector ABI (variable lanes, mask predicate)
- `arm_math_*` — non-standard arm-specific variants

---

## CI/CD

GitHub Actions (`.github/workflows/tests.yml`) tests on:
1. **Linux AArch64 native** — AWS Graviton3, GCC + LLVM/Clang 20
2. **Linux x86_64 cross → AArch64** — QEMU user-mode
3. **macOS AArch64 native** — Apple Silicon, GCC 14 + system Clang
4. **Windows x86_64 cross → AArch64** — MSYS2 + Mingw64 (build only)

---

## Security Audit Focus Areas

### High-value targets for auditing

1. **Math special case handling** (`math/aarch64/*.c`, `math/aarch64/advsimd/*.c`, `math/aarch64/sve/*.c`):
   - NaN/Inf/denormal propagation correctness
   - Domain error handling (e.g., `log(-1)`, `sqrt(-1)`, `asin(2)`)
   - errno setting correctness when `WANT_ERRNO=1`
   - fenv exception flags (FE_INVALID, FE_DIVBYZERO, FE_OVERFLOW, FE_UNDERFLOW)

2. **String bounds safety** (`string/aarch64/*.S`):
   - Off-by-one errors in size calculations
   - Alignment assumptions — unaligned access is intentional, but boundary checks matter
   - `memmove` overlap detection correctness
   - MTE variant tag handling

3. **Vector code predicates** (`math/aarch64/sve/*.c`):
   - SVE predicate mask (`svbool_t`) usage — inactive lanes must not corrupt results
   - Lane independence — no cross-lane side effects

4. **Polynomial approximation tables** (`math/aarch64/v_*_data.c`):
   - Coefficient accuracy for stated ULP bounds
   - Table index bounds — out-of-range inputs should be caught before table lookup

5. **Networking checksum** (`networking/aarch64/`):
   - Integer overflow in accumulation (carries in ones-complement sum)
   - Buffer boundary correctness
   - Endianness handling

6. **Experimental code** (`math/aarch64/experimental/`, `string/aarch64/experimental/`):
   - Explicitly does not meet production quality requirements
   - Reduced accuracy, relaxed special-case handling — audit carefully

### Known design trade-offs relevant to security

- `WANT_ERRNO=0` by default: math functions do not set errno. This is intentional for
  performance but means callers cannot rely on errno for error detection.
- `fno-stack-protector` in math CFLAGS: stack canaries disabled for performance.
- Unaligned memory access in string routines: relies on architecture-level safety, not
  bounds checking in software.
- Vector functions do not support non-nearest rounding modes or fenv handling.
- SVE functions take a predicate mask — callers must ensure correct masking for
  partial vectors; implementations assume mask is well-formed.

### Key helper patterns to understand

- `__math_invalid(x)` — returns NaN, sets FE_INVALID
- `__math_divzero(sign)` — returns ±Inf, sets FE_DIVBYZERO
- `__math_oflow(sign)` — returns ±Inf, sets FE_OVERFLOW
- `__math_uflow(sign)` — returns ±0, sets FE_UNDERFLOW
- `__math_may_uflow(x)` — underflow without guaranteed exception
- `V_NAME_F1(func)` / `V_NAME_D1(func)` — macros for vector function name mangling

---

## Key Files Reference

| File | Purpose |
|---|---|
| `math/include/mathlib.h` | All public math API declarations |
| `math/aarch64/v_*_data.c` | Polynomial coefficient tables for vector math |
| `config.mk.dist` | Build config template (all knobs documented here) |
| `string/aarch64/asmdefs.h` | Assembly macros used across all string routines |
| `math/test/ulp.h` | ULP error measurement infrastructure |
| `math/tools/*.sollya` | Polynomial coefficient generation scripts |
| `.github/workflows/tests.yml` | CI matrix and test commands |

---

## Formal Verification with ESBMC

### Harness layout

Verification harnesses live under `harness/` mirroring the source tree:

```
harness/
└── math/
    ├── esbmc_pow_harness.c       # 26 IEEE 754 properties for pow/powf
    └── esbmc_checkint_harness.c  # 4 integer-arithmetic properties for checkint_d/f
```

### How to run

```bash
# Main pow/powf harness (all 26 properties)
esbmc harness/math/esbmc_pow_harness.c --boolector --floatbv \
      --unwind 3 -I math/ --timeout 180s

# checkint/zeroinfnan integer arithmetic with full overflow checks
esbmc harness/math/esbmc_checkint_harness.c --boolector \
      --overflow-check --unsigned-overflow-check --unwind 3 --timeout 60s
```

Both commands produce **VERIFICATION SUCCESSFUL**.

### Harness design notes

- **No loops in pow/powf**: `math/pow.c` and `math/powf.c` are entirely
  loop-free (straight-line conditionals + polynomial evaluation). BMC with
  `--unwind 3` is therefore complete — there is nothing left unbounded.
  `--k-induction-parallel` is not applicable here; it is useful only when
  the code under test contains loops with invariants to prove.

- **Stub strategy**: External data tables (`__pow_log_data`, `__exp_data`,
  `__powf_log2_data`, `__exp2f_data`) are zero-initialised stubs. The
  polynomial core (`log_inline`, `exp_inline`, etc.) is replaced with
  `__VERIFIER_nondet_double/float()` so ESBMC explores all possible core
  outputs while verifying only the special-case dispatch logic.

- **x86_64 target**: ESBMC runs on x86_64 where `__aarch64__` is not
  defined. `math_config.h` falls back to `volatile`-based `opt_barrier_*`
  (no inline asm). Set `HAVE_FAST_FMA=0`, `TOINT_INTRINSICS=0`.

### Verified properties (all SAFE)

| ID | Property |
|---|---|
| P1 | `pow(x, ±0) = 1` for any quiet x |
| P2a/b | `pow(1, 0)` and `pow(1, ±Inf) = 1` (special-case fires) |
| P2c | `pow(1, y)` for normal finite y goes through core (not special case) |
| P3–P4 | `pow(±1, ±Inf) = 1` |
| P5–P7 | `pow` with x>1 or 0<x<1 and y=±Inf returns correct Inf/0 |
| P8 | `pow(x<0, non-integer y) = NaN` |
| P9–P10 | `pow(±0, y)` → ±Inf or ±0 depending on sign of y |
| P11–P12 | `pow(±Inf, y)` → 0 or ±Inf depending on sign of y |
| PF1–PF6 | Float equivalents for powf |
| C1–C4 | `checkint_d/f` shift bounds and return-value range |

### Findings

**F1 — No special case for `pow(1, y)` with finite normal y** (not a bug):
Both `pow.c` and `powf.c` have no early-return guard for x=1 when y is a
finite value in the normal exponent range `[2^-65, 2^63)`. The function
falls through to the polynomial core and relies on `log(1.0) = 0.0` being
exact in IEEE 754, so `exp(y * 0) = 1.0`. ESBMC proved the dispatch
reaches the core path (`core == 1`) for this input class.

**F2 — Intentional unsigned wraparound in `zeroinfnan_d/f`** (not a bug):
The expression `2 * i - 1 >= threshold` deliberately wraps for `i = 0`
(positive zero) so that zeros, infinities, and NaNs are all caught by a
single comparison. This is valid C (unsigned arithmetic is defined mod 2ⁿ)
but ESBMC's `--unsigned-overflow-check` flags it. Suppress that flag when
running on files that use this pattern.

**F3 — Intentional FP division by zero in `pow(0, y<0)` path** (not a bug):
`1 / x2` where `x2 = 0.0` intentionally produces `±Inf` and naturally
signals `FE_DIVBYZERO` via hardware. ESBMC's `--overflow-check` flags this
as an FP infinity result. It is correct IEEE 754 behaviour.
