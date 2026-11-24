import PuristSiliconCore.Anchor

namespace PuristSiliconCore

/-! ## 1. Branchless Artin B_n Generator Encoding (Vol. VI Sec. 8.2 ActOne) -/

/-- Branchless generator map g_k = 2*i + (0 if s=+1 else 1), disjoint from 0 pad and 1 sentinel. -/
def encodeBraidGen (i : Nat) (posSign : Bool) : Nat :=
  match posSign with
  | true => 2 * i
  | false => 2 * i + 1

theorem encodeBraidGen_ge_two (i : Nat) (posSign : Bool) (hi : 1 ≤ i) :
    2 ≤ encodeBraidGen i posSign := by
  cases posSign <;> simp only [encodeBraidGen] <;> omega

theorem encodeBraidGen_injective (i1 i2 : Nat) (s1 s2 : Bool)
    (h : encodeBraidGen i1 s1 = encodeBraidGen i2 s2) :
    i1 = i2 ∧ s1 = s2 := by
  cases s1 <;> cases s2 <;> simp only [encodeBraidGen] at h <;>
    first | exact ⟨by omega, rfl⟩ | omega

theorem encodeBraidGen_bitwise_parity_small :
    ((List.range 64).tail).all (fun i =>
      (((i <<< 1) ||| 0) == encodeBraidGen i true) &&
      (((i <<< 1) ||| 1) == encodeBraidGen i false)) = true := by
  decide

/-! ## 2. Artin Braid Group B_4 Permutation & Vol. V [P_4, P_4] Pure Braid Purity -/

inductive BraidGen4 where
  | s1 | s1Inv | s2 | s2Inv | s3 | s3Inv
  deriving Repr, DecidableEq

structure Perm4 where
  p0 : Fin 4
  p1 : Fin 4
  p2 : Fin 4
  p3 : Fin 4
  deriving Repr, DecidableEq

def idPerm4 : Perm4 := ⟨0, 1, 2, 3⟩

def applyGen4 (g : BraidGen4) (p : Perm4) : Perm4 :=
  match g with
  | .s1 | .s1Inv => ⟨p.p1, p.p0, p.p2, p.p3⟩
  | .s2 | .s2Inv => ⟨p.p0, p.p2, p.p1, p.p3⟩
  | .s3 | .s3Inv => ⟨p.p0, p.p1, p.p3, p.p2⟩

def evalPerm4 (word : List BraidGen4) : Perm4 :=
  word.foldl (fun acc g => applyGen4 g acc) idPerm4

def gen4Writhe (g : BraidGen4) : Int :=
  match g with
  | .s1 | .s2 | .s3 => 1
  | .s1Inv | .s2Inv | .s3Inv => -1

def wordWrithe4 (word : List BraidGen4) : Int :=
  word.foldl (fun acc g => acc + gen4Writhe g) 0

/-- Vol. V Theorem 4.1 commutator word W_4 in [P_4, P_4] subset P_4 subset B_4. -/
def vol5CommutatorW4 : List BraidGen4 :=
  [ .s1, .s1, .s2, .s2, .s1Inv, .s1Inv, .s2Inv, .s2Inv,
    .s2, .s2, .s3, .s3, .s2Inv, .s2Inv, .s3Inv, .s3Inv ]

/-- Artin braid relations and far commutativity hold on the B_4 -> S_4 quotient. -/
theorem b4_artin_braid_and_far_commutativity :
    evalPerm4 [.s1, .s2, .s1] = evalPerm4 [.s2, .s1, .s2] ∧
    evalPerm4 [.s2, .s3, .s2] = evalPerm4 [.s3, .s2, .s3] ∧
    evalPerm4 [.s1, .s3] = evalPerm4 [.s3, .s1] := by
  decide

/-- THM-TRIBODY-APP5-02: Vol. V [P_4, P_4] commutator W_4 induces identity permutation (pure braid) and zero total writhe. -/
theorem vol5_commutator_w4_pure_and_zero_writhe :
    evalPerm4 vol5CommutatorW4 = idPerm4 ∧ wordWrithe4 vol5CommutatorW4 = 0 := by
  decide

/-! ## 3. Symbolic Reduced Burau 2x2 Artin Braid Relation over Z[t] (Vol. V Thm 4.1) -/

structure Mat2Int where
  m00 : Int
  m01 : Int
  m10 : Int
  m11 : Int
  deriving Repr, DecidableEq

def matMul2 (a b : Mat2Int) : Mat2Int :=
  ⟨ a.m00 * b.m00 + a.m01 * b.m10, a.m00 * b.m01 + a.m01 * b.m11,
    a.m10 * b.m00 + a.m11 * b.m10, a.m10 * b.m01 + a.m11 * b.m11 ⟩

def matDet2 (a : Mat2Int) : Int :=
  a.m00 * a.m11 - a.m01 * a.m10

def burauS1 (t : Int) : Mat2Int := ⟨-t, 1, 0, 1⟩
def burauS2 (t : Int) : Mat2Int := ⟨1, 0, t, -t⟩

private theorem int_neg_add_self (a : Int) : -a + a = 0 := by omega
private theorem int_add_neg_self (a : Int) : a + -a = 0 := by omega

/-- Symbolic Artin braid relation beta_t(s1) * beta_t(s2) * beta_t(s1) = beta_t(s2) * beta_t(s1) * beta_t(s2) for ALL t : Int. -/
theorem burau_artin_relation_b3_exact (t : Int) :
    matMul2 (matMul2 (burauS1 t) (burauS2 t)) (burauS1 t) =
    matMul2 (matMul2 (burauS2 t) (burauS1 t)) (burauS2 t) := by
  unfold matMul2 burauS1 burauS2
  simp only [Int.mul_zero, Int.zero_mul, Int.one_mul, Int.mul_one,
             Int.zero_add, Int.add_zero, Int.mul_neg, Int.neg_zero,
             int_neg_add_self, int_add_neg_self]

theorem burau_b3_det_product (t : Int) :
    matDet2 (burauS1 t) = -t ∧
    matDet2 (burauS2 t) = -t ∧
    matDet2 (burauS1 (-1)) = 1 ∧
    matDet2 (burauS2 (-1)) = 1 := by
  unfold matDet2 burauS1 burauS2
  simp only [Int.mul_zero, Int.one_mul, Int.sub_zero]
  omega

/-! ## 4. Disjoint Tier-1 + Tier-2 + Vol. VIII Domain-Tag Registry (DRIFT-TAG-04) -/

/-- Pairwise disjoint domain separation tags across Table 4, CCSDS, SubTranslate (0x11..0x15), ActOne, Runes, and Vol. VIII FS81/ZW81. -/
def canonicalEcosystemDomainTags : List Nat :=
  [ 0x00000001, -- Canonical Table 4 Default
    0x004f454d, -- CCSDS OEM ('OEM')
    0x004f504d, -- CCSDS OPM ('OPM')
    0x00000011, -- AUX SubTranslate Acoustic Stego
    0x00000012, -- AUX SubTranslate ZWJ Text
    0x00000013, -- AUX SubTranslate QR Pay
    0x00000014, -- AUX SubTranslate ML-DSA-65 (replaces legacy 0x04 collision)
    0x00000015, -- AUX SubTranslate VTT/SRT
    0x41435436, -- AUX ActOne Main ('ACT6')
    0x50513635, -- AUX ActOne PQ65 Transcript ('PQ65')
    0x52554e36, -- AUX Ancient Runes ('RUN6')
    0x46533831, -- Vol. VIII ActOne Fountain Zero-Alloc Scanner ('FS81')
    0x5a573831  -- Vol. VIII ActOne ZW81 Solinas Stego ('ZW81')
  ]

theorem domain_tags_pairwise_disjoint_and_fit_p64 :
    canonicalEcosystemDomainTags.length = 13 ∧
    canonicalEcosystemDomainTags.Nodup ∧
    canonicalEcosystemDomainTags.all (fun t => 0 < t && t < p64) = true := by
  decide

end PuristSiliconCore
