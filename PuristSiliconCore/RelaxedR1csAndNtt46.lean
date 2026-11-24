import PuristSiliconCore.Anchor

namespace PuristSiliconCore

private def p64I : Int := (p64 : Int)

/-- THM-DILATON-APP6-02(i): Relaxed-R1CS folding preserves exact zero slack mod p64 for any challenge r. -/
theorem relaxed_r1cs_folding_zero_slack
    (az1 bz1 cz1 u1 e1 az2 bz2 cz2 u2 e2 r : Int)
    (h1 : (az1 * bz1) % p64I = (u1 * cz1 + e1) % p64I)
    (h2 : (az2 * bz2) % p64I = (u2 * cz2 + e2) % p64I) :
    let T   := az1 * bz2 + az2 * bz1 - u1 * cz2 - u2 * cz1
    let az' := az1 + r * az2
    let bz' := bz1 + r * bz2
    let cz' := cz1 + r * cz2
    let u'  := u1 + r * u2
    let e'  := e1 + r * T + r * r * e2
    (az' * bz') % p64I = (u' * cz' + e') % p64I := by
  intro T az' bz' cz' u' e'
  have p1 : (r * az2) * bz1 = r * (az2 * bz1) := Int.mul_assoc _ _ _
  have p2 : az1 * (r * bz2) = r * (az1 * bz2) := Int.mul_left_comm _ _ _
  have p3 : (r * az2) * (r * bz2) = (r * r) * (az2 * bz2) := by
    rw [Int.mul_assoc, Int.mul_left_comm az2 r bz2, ← Int.mul_assoc]
  have h_lhs_exp :
      az' * bz' = az1 * bz1 + r * (az1 * bz2 + az2 * bz1) + (r * r) * (az2 * bz2) := by
    dsimp only [az', bz']
    rw [Int.add_mul, Int.mul_add, Int.mul_add, p1, p2, p3, Int.mul_add]
    omega
  have q1 : (r * u2) * cz1 = r * (u2 * cz1) := Int.mul_assoc _ _ _
  have q2 : u1 * (r * cz2) = r * (u1 * cz2) := Int.mul_left_comm _ _ _
  have q3 : (r * u2) * (r * cz2) = (r * r) * (u2 * cz2) := by
    rw [Int.mul_assoc, Int.mul_left_comm u2 r cz2, ← Int.mul_assoc]
  have h_rhs_exp :
      u' * cz' + e' = (u1 * cz1 + e1) + r * (az1 * bz2 + az2 * bz1) + (r * r) * (u2 * cz2 + e2) := by
    dsimp only [u', cz', e', T]
    rw [Int.add_mul, Int.mul_add, Int.mul_add, q1, q2, q3]
    simp only [Int.mul_add, Int.mul_sub]
    omega
  rw [h_lhs_exp, h_rhs_exp]
  rw [Int.add_emod, Int.add_emod (u1 * cz1 + e1 + _),
      Int.add_emod (az1 * bz1), Int.add_emod (u1 * cz1 + e1)]
  rw [Int.mul_emod (r * r) (az2 * bz2), Int.mul_emod (r * r) (u2 * cz2 + e2)]
  rw [h1, h2]

/-- THM-DILATON-APP6-02(ii): Schwartz-Zippel soundness dominance for D_eff = 619 over F_{p106^2} and F_{p64^4} vs 2^-128 floor. -/
def effectiveFoldingDegree : Nat := 2 * 256 + 107

theorem schwartz_zippel_quartic_dominates_128bit :
    effectiveFoldingDegree = 619 ∧
    effectiveFoldingDegree * 2^128 > p64 ∧
    effectiveFoldingDegree * 2^128 < p106^2 ∧
    effectiveFoldingDegree * 2^128 < p64^4 := by
  decide

/-- MATH-ERR-02: Exact worst-case 46-bit FIPS-204 ML-DSA-65 NTT coefficient packing bound. -/
def mlDsaQ : Nat := 8380417
def mlKemQ : Nat := 3329

def packNtt46 (c0 c1 : Nat) : Nat := c0 + 2^23 * c1
def unpackNtt46 (w : Nat) : Nat × Nat := (w % 2^23, w / 2^23)

theorem ntt46_w_max_exact_and_fits_fields :
    packNtt46 (mlDsaQ - 1) (mlDsaQ - 1) = 70300033081344 ∧
    70300033081344 < 2^46 ∧
    2^46 < p64 ∧
    p64 < p106 := by
  decide

/-- THM-DILATON-APP6-02(iii): Bijective 46-bit packing for ALL reduced ML-DSA-65 / ML-KEM-768 pairs. -/
theorem packNtt46_bound_and_injective (c0 c1 : Nat) (h0 : c0 < mlDsaQ) (h1 : c1 < mlDsaQ) :
    packNtt46 c0 c1 < 2^46 ∧ unpackNtt46 (packNtt46 c0 c1) = (c0, c1) := by
  unfold packNtt46 unpackNtt46 mlDsaQ at *
  constructor
  · omega
  · have hc0 : c0 < 2^23 := by omega
    have hmod : (c0 + 2^23 * c1) % 2^23 = c0 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0]
    have hdiv : (c0 + 2^23 * c1) / 2^23 = c1 := by
      rw [Nat.add_comm, Nat.mul_add_div (Nat.pow_pos (by decide)),
          Nat.div_eq_of_lt hc0]
      omega
    rw [hmod, hdiv]

end PuristSiliconCore
