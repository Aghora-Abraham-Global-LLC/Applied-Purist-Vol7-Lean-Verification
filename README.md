# Applied Purist Vol. VII — Lean 4 Formal Verification (`PuristSiliconCore`)

Mathlib-free Lean 4.36.0 / Lake 5.0 formal verification suite (**115 `KERNEL_ONLY` theorems, `0 sorry`, `0 native_decide`**)
+ inherited C99 constant-time Solinas baseline (`c_silicon/solinas_ct.c`) for **Applied Purist Vol. VII** (`10.5281/zenodo.24417929`),
building upon **Vol. VI** (`10.5281/zenodo.24392562`, Lean v1.0.0 `10.5281/zenodo.24496435`) & `https://lean.bhutadamarasena.com/`.

## Reproduce
    lake build && lake exe purist_audit ./proof-manifest.json

## Coverage & Scope Boundaries
- **Formally Proved in Lean (`115/115 KERNEL_ONLY`, `0 sorry`):**
  - **Primality & Solinas Core (`SolinasPocklington`, `Anchor`, `SolinasFields`):** Mathlib-free Pocklington primality proofs `p64_is_prime` (`2^64-59`) and `p106_is_prime` (`2^106-117`), Fermat's Little Theorem, Euler QNR criteria, 2-pass/3-pass Solinas folding, `addModP64Ct`/`subModP64Ct`, and 9-mul `F_{p64^4}` Karatsuba.
  - **Chronometry & Memory (`D106AndBitwise`, `AlgebraicPhysicsAndEft`, `Vol7RemainingCore`):** Centered `D106 -> F_{p106}` injectivity, Knuth/Dekker EFT reconstruction, `SplitTimeEpoch` 10-yr closure bounds, `L_TCL` drift breach & daily ranges, and 5.0PN Pade-Laplace BIBO stability.
  - **Strong-Field Algebra & Astrodynamics (`Vol7RemainingCore`, `Vol7PinnacleCore`, `ArtinBraidAndDomainTags`):** Closed 4-edge Sagnac gauge invariance (plus 2-edge failure witness), scaled-sphere Dirac projector (`dot3 q q = s * s`), Pines norm positivity, 1PN Routh/Kozai stability brackets, Kerr horizon quadratic `Delta(r_+-)=0`, GHSS `T_L + T_R`, Teukolsky-Starobinsky sign flip, `l <= 24` Dray-'t Hooft Cayley unitarity, MSS bound, and Artin `B_n` relations.
  - **WebGPU ABI & IEEE-754 `f32` Accuracy (`StrongFieldChrono64Abi`, `Vol7PinnacleCore`, `SolinasIvc64Abi`):** 64-byte `StrongFieldChronoState64` (Morton-30 `+12B/+52B` immutability, 14/14 non-Morton SP 800-88 wipe, zero `f32` tag transits) and bit-exact `binary32` RNE verification of `0.9999` (`0x3f7ff972`), universal Sterbenz exactness on `[0.5, 1.0)`, and `>1625x` factored vs. naive accuracy.
- **Outside Mathlib-Free Scope (Not Claimed as Lean-Proved):** Continuous PDE/ODE/spectral analysis (Braess-Hackbusch convergence, Teukolsky/Nollert QNMs, Christodoulou BMS integrals, 3D Stokes integrals), empirical GW/geodesy benchmarks, and Mathlib polynomial certificates (`Polynomial.Irreducible (X^4 - 2)` and general `MvPolynomial` Schwartz-Zippel).
- **OPSEC Boundary:** Proprietary web UI, WASM/WebGPU engines, `TMD-Hash v11.0/v12.0` internals, and NUMS constants excluded (`TMD12-BB` black-box only).

## Citation
    @article{unmani2026puristvol7,
      author  = {Ghulam-e-Shah-e-Unmani, Arya Arunachala Ananda},
      title   = {{Strong-Field 5.0PN Gravitational-Wave Memory, Extreme Kerr-CFT2 Ringdown Spectroscopy, Dray-'t Hooft Shockwaves, and Picosecond IAU 2024 Chronometric Geodesy}},
      journal = {Applied Purist Series},
      volume  = {VII},
      year    = {2026},
      doi     = {10.5281/zenodo.24417929}
    }

    @software{unmani2026puristvol7lean,
      author    = {Ghulam-e-Shah-e-Unmani, Arya Arunachala Ananda},
      title     = {{Applied Purist Series Vol. VII — Lean 4 Formal Verification & Silicon ABI Archive}},
      version   = {1.0.0},
      year      = {2026},
      publisher = {Zenodo},
      license   = {CC-BY-4.0},
      url       = {https://lean.bhutadamarasena.com/}
    }
# Applied-Purist-Vol7-Lean-Verification
