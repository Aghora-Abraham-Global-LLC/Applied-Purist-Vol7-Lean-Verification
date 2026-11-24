import PuristSiliconCore.Anchor

namespace PuristSiliconCore

/-- Branchless unsigned canonical subtraction for s < 2 * p64. -/
def canonSubP64 (s : Nat) : Nat :=
  if s ≥ p64 then s - p64 else s

/-- Branchless unsigned canonical subtraction for s < 2 * p106. -/
def canonSubP106 (s : Nat) : Nat :=
  if s ≥ p106 then s - p106 else s

/-- Two-pass intermediate for 128-bit Solinas folding z = z0 + 2^64 * z1. -/
def solinas64Pass2 (z0 z1 : Nat) : Nat :=
  let s1 := z0 + 59 * z1
  (s1 % 2^64) + 59 * (s1 / 2^64)

/-- Three-pass pre-canonical fold for 128-bit Solinas folding. -/
def solinas64Pass3 (z0 z1 : Nat) : Nat :=
  let s2 := solinas64Pass2 z0 z1
  (s2 % 2^64) + 59 * (s2 / 2^64)

def reduce3PassP64 (z0 z1 : Nat) : Nat :=
  canonSubP64 (solinas64Pass3 z0 z1)

/-- Two-pass intermediate for 212-bit Solinas folding z = z0 + 2^106 * z1. -/
def solinas106Pass2 (z0 z1 : Nat) : Nat :=
  let s1 := z0 + 117 * z1
  (s1 % 2^106) + 117 * (s1 / 2^106)

/-- Three-pass pre-canonical fold for 212-bit Solinas folding. -/
def solinas106Pass3 (z0 z1 : Nat) : Nat :=
  let s2 := solinas106Pass2 z0 z1
  (s2 % 2^106) + 117 * (s2 / 2^106)

def reduce3PassP106 (z0 z1 : Nat) : Nat :=
  canonSubP106 (solinas106Pass3 z0 z1)

private theorem mod_add_mul_mod_eq (a b p : Nat) : (a + p * b) % p = a % p := by
  rw [Nat.add_mul_mod_self_left]

private theorem two_pow_64_fold_mod (r q : Nat) : (r + 2^64 * q) % p64 = (r + 59 * q) % p64 := by
  have hsplit : r + 2^64 * q = (r + 59 * q) + p64 * q := by
    rw [two_pow_64_eq_p64_add_59, Nat.add_mul]
    ac_rfl
  rw [hsplit, mod_add_mul_mod_eq]

private theorem two_pow_106_fold_mod (r q : Nat) : (r + 2^106 * q) % p106 = (r + 117 * q) % p106 := by
  have hsplit : r + 2^106 * q = (r + 117 * q) + p106 * q := by
    rw [two_pow_106_eq_p106_add_117, Nat.add_mul]
    ac_rfl
  rw [hsplit, mod_add_mul_mod_eq]

private theorem canonSubP64_eq_mod (s : Nat) (hs : s < 2 * p64) : canonSubP64 s = s % p64 := by
  unfold canonSubP64
  by_cases h : s ≥ p64
  · simp only [h, ↓reduceIte]
    have hlt : s - p64 < p64 := by omega
    have heq : s = (s - p64) + p64 * 1 := by omega
    have hmod : ((s - p64) + p64 * 1) % p64 = s - p64 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rw [← heq] at hmod
    exact hmod.symm
  · simp only [h, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

private theorem canonSubP106_eq_mod (s : Nat) (hs : s < 2 * p106) : canonSubP106 s = s % p106 := by
  unfold canonSubP106
  by_cases h : s ≥ p106
  · simp only [h, ↓reduceIte]
    have hlt : s - p106 < p106 := by omega
    have heq : s = (s - p106) + p106 * 1 := by omega
    have hmod : ((s - p106) + p106 * 1) % p106 = s - p106 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rw [← heq] at hmod
    exact hmod.symm
  · simp only [h, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- MATH-ERR-05: Worst-case 2-pass fold over 128 bits can overshoot 2^64 by at most 3421. -/
theorem solinas64_2pass_overshoot_bound (z0 z1 : Nat) (hz0 : z0 < 2^64) (hz1 : z1 < 2^64) :
    solinas64Pass2 z0 z1 ≤ 2^64 + 3421 := by
  dsimp only [solinas64Pass2]
  have hdiv : 2^64 * ((z0 + 59 * z1) / 2^64) + (z0 + 59 * z1) % 2^64 = z0 + 59 * z1 :=
    Nat.div_add_mod _ _
  have hmod : (z0 + 59 * z1) % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
  omega

/-- MATH-ERR-04 & MATH-ERR-05: Strict 3-pass fold fits natively inside [0, 2^64 - 1]. -/
theorem solinas64_3pass_fits_u64 (z0 z1 : Nat) (hz0 : z0 < 2^64) (hz1 : z1 < 2^64) :
    solinas64Pass3 z0 z1 < 2^64 := by
  have hs2 : solinas64Pass2 z0 z1 ≤ 2^64 + 3421 := solinas64_2pass_overshoot_bound z0 z1 hz0 hz1
  dsimp only [solinas64Pass3]
  have hdiv : 2^64 * (solinas64Pass2 z0 z1 / 2^64) + solinas64Pass2 z0 z1 % 2^64 = solinas64Pass2 z0 z1 :=
    Nat.div_add_mod _ _
  have hmod : solinas64Pass2 z0 z1 % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
  omega

/-- THM-DILATON-APP6-01: 3-pass P64 reduction is exact modulo p64 and strictly canonical (< p64). -/
theorem solinas64_3pass_lt_p64 (z0 z1 : Nat) (hz0 : z0 < 2^64) (hz1 : z1 < 2^64) :
    reduce3PassP64 z0 z1 < p64 := by
  have hs3 : solinas64Pass3 z0 z1 < 2^64 := solinas64_3pass_fits_u64 z0 z1 hz0 hz1
  have hs3_2p : solinas64Pass3 z0 z1 < 2 * p64 := by unfold p64; omega
  unfold reduce3PassP64
  rw [canonSubP64_eq_mod _ hs3_2p]
  exact Nat.mod_lt _ p64_pos

theorem solinas64_3pass_mod_correct (z0 z1 : Nat) (hz0 : z0 < 2^64) (hz1 : z1 < 2^64) :
    reduce3PassP64 z0 z1 = (z0 + 2^64 * z1) % p64 := by
  have hs3 : solinas64Pass3 z0 z1 < 2^64 := solinas64_3pass_fits_u64 z0 z1 hz0 hz1
  have hs3_2p : solinas64Pass3 z0 z1 < 2 * p64 := by unfold p64; omega
  unfold reduce3PassP64
  rw [canonSubP64_eq_mod _ hs3_2p]
  have hs2_eq : solinas64Pass3 z0 z1 % p64 = solinas64Pass2 z0 z1 % p64 := by
    dsimp only [solinas64Pass3]
    rw [← two_pow_64_fold_mod, Nat.mod_add_div]
  have hs1_eq : solinas64Pass2 z0 z1 % p64 = (z0 + 59 * z1) % p64 := by
    dsimp only [solinas64Pass2]
    rw [← two_pow_64_fold_mod, Nat.mod_add_div]
  rw [hs2_eq, hs1_eq, ← two_pow_64_fold_mod]

/-- MATH-ERR-05: 2-pass P106 fold overshoot bound (<= 2^106 + 13571). -/
theorem solinas106_2pass_overshoot_bound (z0 z1 : Nat) (hz0 : z0 < 2^106) (hz1 : z1 < 2^106) :
    solinas106Pass2 z0 z1 ≤ 2^106 + 13571 := by
  dsimp only [solinas106Pass2]
  have hdiv : 2^106 * ((z0 + 117 * z1) / 2^106) + (z0 + 117 * z1) % 2^106 = z0 + 117 * z1 :=
    Nat.div_add_mod _ _
  have hmod : (z0 + 117 * z1) % 2^106 < 2^106 := Nat.mod_lt _ (by decide)
  omega

/-- Strict 3-pass P106 fold fits strictly below 2^106 (< 2 * p106). -/
theorem solinas106_3pass_fits_lt_2p106 (z0 z1 : Nat) (hz0 : z0 < 2^106) (hz1 : z1 < 2^106) :
    solinas106Pass3 z0 z1 < 2^106 ∧ solinas106Pass3 z0 z1 < 2 * p106 := by
  have hs2 : solinas106Pass2 z0 z1 ≤ 2^106 + 13571 := solinas106_2pass_overshoot_bound z0 z1 hz0 hz1
  dsimp only [solinas106Pass3]
  have hdiv : 2^106 * (solinas106Pass2 z0 z1 / 2^106) + solinas106Pass2 z0 z1 % 2^106 = solinas106Pass2 z0 z1 :=
    Nat.div_add_mod _ _
  have hmod : solinas106Pass2 z0 z1 % 2^106 < 2^106 := Nat.mod_lt _ (by decide)
  unfold p106
  omega

/-- THM-DILATON-APP6-01: 3-pass P106 reduction is exact modulo p106 and canonical (< p106). -/
theorem solinas106_3pass_mod_correct (z0 z1 : Nat) (hz0 : z0 < 2^106) (hz1 : z1 < 2^106) :
    reduce3PassP106 z0 z1 = (z0 + 2^106 * z1) % p106 ∧ reduce3PassP106 z0 z1 < p106 := by
  have hs3_2p : solinas106Pass3 z0 z1 < 2 * p106 := (solinas106_3pass_fits_lt_2p106 z0 z1 hz0 hz1).2
  unfold reduce3PassP106
  rw [canonSubP106_eq_mod _ hs3_2p]
  have hs2_eq : solinas106Pass3 z0 z1 % p106 = solinas106Pass2 z0 z1 % p106 := by
    dsimp only [solinas106Pass3]
    rw [← two_pow_106_fold_mod, Nat.mod_add_div]
  have hs1_eq : solinas106Pass2 z0 z1 % p106 = (z0 + 117 * z1) % p106 := by
    dsimp only [solinas106Pass2]
    rw [← two_pow_106_fold_mod, Nat.mod_add_div]
  have hmod : solinas106Pass3 z0 z1 % p106 = (z0 + 2^106 * z1) % p106 := by
    rw [hs2_eq, hs1_eq, ← two_pow_106_fold_mod]
  exact ⟨hmod, Nat.mod_lt _ p106_pos⟩

/-- Branchless C99/WGSL add_mod_p64_ct model over 64-bit unsigned words. -/
def addModP64Ct (a b : Nat) : Nat :=
  let s0 := (a + b) % 2^64
  let c0 := if a + b ≥ 2^64 then 1 else 0
  let s1 := (s0 + c0 * 59) % 2^64
  let c1 := if s0 + c0 * 59 ≥ 2^64 then 1 else 0
  let s2 := s1 + c1 * 59
  canonSubP64 s2

/-- Branchless borrow-safe sub_mod_p64_ct (MATH-ERR-04). -/
def subModP64Ct (a b : Nat) : Nat :=
  let ca := canonSubP64 a
  let cb := canonSubP64 b
  if ca < cb then ca + p64 - cb else ca - cb

theorem addModP64Ct_correct (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    addModP64Ct a b = (a + b) % p64 ∧ addModP64Ct a b < p64 := by
  dsimp only [addModP64Ct]
  let s0 := (a + b) % 2^64
  let c0 := if a + b ≥ 2^64 then 1 else 0
  have hc0_eq : c0 = (a + b) / 2^64 := by
    dsimp only [c0]
    by_cases h : a + b ≥ 2^64
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega
  have hsum0 : s0 + 2^64 * c0 = a + b := by
    dsimp only [s0]
    rw [hc0_eq, Nat.mod_add_div]
  have hs0_lt : s0 < 2^64 := Nat.mod_lt _ (by decide)
  have hc0_le : c0 ≤ 1 := by
    dsimp only [c0]
    by_cases h : a + b ≥ 2^64 <;> simp [h]
  let sum1 := s0 + c0 * 59
  have hsum1_bound : sum1 < 2^64 + 59 := by dsimp only [sum1]; omega
  let s1 := sum1 % 2^64
  let c1 := if sum1 ≥ 2^64 then 1 else 0
  have hc1_eq : c1 = sum1 / 2^64 := by
    dsimp only [c1]
    by_cases h : sum1 ≥ 2^64
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega
  have hsum1_dm : 2^64 * (sum1 / 2^64) + s1 = sum1 := Nat.div_add_mod sum1 (2^64)
  have hs1_lt_div : s1 < 2^64 := Nat.mod_lt sum1 (by decide)
  have hsum1_eq : s1 + 2^64 * c1 = sum1 := by
    rw [hc1_eq]
    omega
  have hs2_lt_u64 : s1 + c1 * 59 < 2^64 := by
    dsimp only [c1]
    by_cases h : sum1 ≥ 2^64
    · simp only [h, ↓reduceIte]
      have : sum1 / 2^64 = 1 := by omega
      have : s1 < 59 := by omega
      omega
    · simp only [h, ↓reduceIte]
      omega
  have hs2_lt_2p : s1 + c1 * 59 < 2 * p64 := by unfold p64; omega
  change canonSubP64 (s1 + c1 * 59) = (a + b) % p64 ∧ canonSubP64 (s1 + c1 * 59) < p64
  rw [canonSubP64_eq_mod _ hs2_lt_2p]
  have hmod_step : (s1 + c1 * 59) % p64 = (a + b) % p64 := by
    calc (s1 + c1 * 59) % p64
        = (s1 + 59 * c1) % p64 := by rw [Nat.mul_comm c1 59]
      _ = (s1 + 2^64 * c1) % p64 := (two_pow_64_fold_mod s1 c1).symm
      _ = sum1 % p64 := by rw [hsum1_eq]
      _ = (s0 + 59 * c0) % p64 := by dsimp only [sum1]; rw [Nat.mul_comm c0 59]
      _ = (s0 + 2^64 * c0) % p64 := (two_pow_64_fold_mod s0 c0).symm
      _ = (a + b) % p64 := by rw [hsum0]
  exact ⟨hmod_step, hmod_step ▸ Nat.mod_lt _ p64_pos⟩

theorem subModP64Ct_correct (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    subModP64Ct a b = ((a % p64) + p64 - (b % p64)) % p64 ∧ subModP64Ct a b < p64 := by
  dsimp only [subModP64Ct]
  have ha2p : a < 2 * p64 := by unfold p64; omega
  have hb2p : b < 2 * p64 := by unfold p64; omega
  rw [canonSubP64_eq_mod a ha2p, canonSubP64_eq_mod b hb2p]
  have ha_lt : a % p64 < p64 := Nat.mod_lt a p64_pos
  have hb_lt : b % p64 < p64 := Nat.mod_lt b p64_pos
  by_cases hlt : a % p64 < b % p64
  · simp only [hlt, ↓reduceIte]
    have hd : a % p64 + p64 - b % p64 < p64 := by omega
    exact ⟨(Nat.mod_eq_of_lt hd).symm, hd⟩
  · simp only [hlt, ↓reduceIte]
    have hd : a % p64 - b % p64 < p64 := by omega
    have heq : a % p64 + p64 - b % p64 = (a % p64 - b % p64) + p64 * 1 := by omega
    constructor
    · rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    · exact hd

/-- Canonical Quartic Tower F_{p64^2} = F_{p64}[u]/(u^2 - 2) -> F_{p64^4} = F_{p64^2}[v]/(v^2 - u). -/
structure Fp64_2 where
  c0 : Int
  c1 : Int

structure Fp64_4 where
  a0 : Fp64_2
  a1 : Fp64_2

def fp64_2MulSchoolbook (x y : Fp64_2) : Fp64_2 :=
  ⟨x.c0 * y.c0 + 2 * (x.c1 * y.c1), x.c0 * y.c1 + x.c1 * y.c0⟩

def fp64_2MulKaratsuba (x y : Fp64_2) : Fp64_2 :=
  let m0 := x.c0 * y.c0
  let m1 := x.c1 * y.c1
  let m2 := (x.c0 + x.c1) * (y.c0 + y.c1)
  ⟨m0 + 2 * m1, m2 - m0 - m1⟩

theorem fp64_2MulKaratsuba_eq (x y : Fp64_2) :
    fp64_2MulKaratsuba x y = fp64_2MulSchoolbook x y := by
  unfold fp64_2MulKaratsuba fp64_2MulSchoolbook
  simp only [Int.add_mul, Int.mul_add]
  congr 1
  omega

def fp64_2MulU (x : Fp64_2) : Fp64_2 :=
  ⟨2 * x.c1, x.c0⟩

def fp64_2Add (x y : Fp64_2) : Fp64_2 :=
  ⟨x.c0 + y.c0, x.c1 + y.c1⟩

def fp64_2Sub (x y : Fp64_2) : Fp64_2 :=
  ⟨x.c0 - y.c0, x.c1 - y.c1⟩

/-- Schoolbook F_{p64^4} multiplication over v^2 = u (4 F_{p64^2} muls). -/
def fp64_4MulSchoolbook (x y : Fp64_4) : Fp64_4 :=
  ⟨fp64_2Add (fp64_2MulSchoolbook x.a0 y.a0) (fp64_2MulU (fp64_2MulSchoolbook x.a1 y.a1)),
   fp64_2Add (fp64_2MulSchoolbook x.a0 y.a1) (fp64_2MulSchoolbook x.a1 y.a0)⟩

/-- Karatsuba F_{p64^4} multiplication consuming exactly 9 base F_{p64} multiplications. -/
def fp64_4MulKaratsuba9 (x y : Fp64_4) : Fp64_4 :=
  let m0 := fp64_2MulKaratsuba x.a0 y.a0
  let m1 := fp64_2MulKaratsuba x.a1 y.a1
  let m2 := fp64_2MulKaratsuba (fp64_2Add x.a0 x.a1) (fp64_2Add y.a0 y.a1)
  ⟨fp64_2Add m0 (fp64_2MulU m1), fp64_2Sub (fp64_2Sub m2 m0) m1⟩

/-- THM-DILATON-APP6-01(ii): 9-multiplication Karatsuba tower product is algebraically exact. -/
theorem fp64_4MulKaratsuba9_eq_schoolbook (x y : Fp64_4) :
    fp64_4MulKaratsuba9 x y = fp64_4MulSchoolbook x y := by
  unfold fp64_4MulKaratsuba9 fp64_4MulSchoolbook
  rw [fp64_2MulKaratsuba_eq, fp64_2MulKaratsuba_eq, fp64_2MulKaratsuba_eq]
  unfold fp64_2MulSchoolbook fp64_2MulU fp64_2Add fp64_2Sub
  simp only [Int.add_mul, Int.mul_add]
  congr 1 <;> congr 1 <;> omega

end PuristSiliconCore
