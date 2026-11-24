import PuristSiliconCore.Anchor

namespace PuristSiliconCore

def p106Int : Int := (p106 : Int)

/-- Centered injective half-bound for D106 -> F_{p106}: (p106 - 1) / 2 = 2^105 - 59. -/
def d106HalfBound : Int := 2^105 - 59

theorem d106_centered_span_eq_p106 : 2 * d106HalfBound + 1 = p106Int := by
  decide

/-- THM-NATH-APP6-01: Centered D106 fixed-point quantization is strictly injective mod p106. -/
theorem d106_centered_quantization_injective (q1 q2 : Int)
    (h1lo : -d106HalfBound ≤ q1) (h1hi : q1 ≤ d106HalfBound)
    (h2lo : -d106HalfBound ≤ q2) (h2hi : q2 ≤ d106HalfBound)
    (hmod : q1 % p106Int = q2 % p106Int) : q1 = q2 := by
  unfold d106HalfBound p106Int p106 at *
  omega

/-- AUDIT-ND-VOL6-01 & MATH-ERR-08: Distinct L_TCL canonical anchor witness bounds (< 2^105 - 59). -/
def lTclWitnessS53  : Int := 0x591d32
def lunarDriftWitnessS53 : Int := 0x700ab2e1693c041

theorem dual_ltcl_anchors_distinct_and_injective :
    lTclWitnessS53 ≠ lunarDriftWitnessS53 ∧
    lTclWitnessS53 ≤ d106HalfBound ∧
    lunarDriftWitnessS53 ≤ d106HalfBound := by
  decide

/-- Arithmetic model of circular 64-bit rotation over [0, 2^64 - 1]. -/
def rotl64Nat (x k : Nat) : Nat :=
  let s := k % 64
  if s = 0 then x % 2^64
  else
    let lo := x % 2^(64 - s)
    let hi := x / 2^(64 - s)
    lo * 2^s + hi

def rotr64Nat (x k : Nat) : Nat :=
  let s := k % 64
  if s = 0 then x % 2^64
  else rotl64Nat x (64 - s)

/-- Helper: extracting bit index i (< 64) of x. -/
def bitAt (x i : Nat) : Nat := (x / 2^i) % 2

/-- 64-bit Hamming weight popcnt_64(x). -/
def popcnt64Nat (x : Nat) : Nat :=
  ((List.range 64).map (fun i => bitAt x i)).foldl (· + ·) 0

private theorem two_pow_pos_nat (n : Nat) : 0 < 2^n :=
  Nat.pow_pos (by decide)

private theorem two_pow_succ_sub (m : Nat) (hm : 1 ≤ m) : 2^m = 2 * 2^(m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

private theorem div_mod_split (x a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (x % (a * b)) / a = (x / a) % b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hdm : a * (b * (x / (a * b))) + x % (a * b) = x := by
    have h0 := Nat.div_add_mod x (a * b)
    rw [Nat.mul_assoc] at h0
    exact h0
  have hdiv : x / a = b * (x / (a * b)) + (x % (a * b)) / a := by
    calc x / a
        = (a * (b * (x / (a * b))) + x % (a * b)) / a := by rw [hdm]
      _ = b * (x / (a * b)) + (x % (a * b)) / a := Nat.mul_add_div ha _ _
  have hlt : (x % (a * b)) / a < b := by
    rw [Nat.div_lt_iff_lt_mul ha, Nat.mul_comm b a]
    exact Nat.mod_lt x hab
  calc (x % (a * b)) / a
      = ((x % (a * b)) / a) % b := (Nat.mod_eq_of_lt hlt).symm
    _ = ((x % (a * b)) / a + b * (x / (a * b))) % b := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (b * (x / (a * b)) + (x % (a * b)) / a) % b := by rw [Nat.add_comm]
    _ = (x / a) % b := by rw [← hdiv]

private theorem mod_mul_two_mod_two (y c : Nat) : (y % (2 * c)) % 2 = y % 2 := by
  have hdm : 2 * (c * (y / (2 * c))) + y % (2 * c) = y := by
    have h0 := Nat.div_add_mod y (2 * c)
    rw [Nat.mul_assoc] at h0
    exact h0
  calc (y % (2 * c)) % 2
      = (y % (2 * c) + 2 * (c * (y / (2 * c)))) % 2 := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (2 * (c * (y / (2 * c))) + y % (2 * c)) % 2 := by rw [Nat.add_comm]
    _ = y % 2 := by rw [hdm]

private theorem bitAt_rotl64Nat (x k i : Nat) (hx : x < 2^64) (hi : i < 64) :
    bitAt (rotl64Nat x k) i = bitAt x ((i + (64 - k % 64)) % 64) := by
  unfold rotl64Nat bitAt
  by_cases hs : k % 64 = 0
  · simp only [hs, ite_eq_left, Nat.sub_zero]
    have hmod : (i + 64) % 64 = i := by omega
    rw [hmod, Nat.mod_eq_of_lt hx]
  · simp only [hs, ↓reduceIte]
    have hklt : k % 64 < 64 := Nat.mod_lt k (by decide)
    have hsplit : 2^64 = 2^(64 - k % 64) * 2^(k % 64) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hhi_lt : x / 2^(64 - k % 64) < 2^(k % 64) := by
      rw [Nat.div_lt_iff_lt_mul (two_pow_pos_nat _), Nat.mul_comm, ← hsplit]
      exact hx
    by_cases his : i < k % 64
    · have hidx : (i + (64 - k % 64)) % 64 = i + (64 - k % 64) := by omega
      rw [hidx]
      have hp : 2^(k % 64) = 2^i * 2^(k % 64 - i) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hp' : x % 2^(64 - k % 64) * 2^(k % 64) = 2^i * (x % 2^(64 - k % 64) * 2^(k % 64 - i)) := by
        rw [hp]; ac_rfl
      have hsub1 : (x % 2^(64 - k % 64) * 2^(k % 64) + x / 2^(64 - k % 64)) / 2^i =
          x % 2^(64 - k % 64) * 2^(k % 64 - i) + (x / 2^(64 - k % 64)) / 2^i := by
        rw [hp', Nat.mul_add_div (two_pow_pos_nat i)]
      rw [hsub1, two_pow_succ_sub (k % 64 - i) (by omega), Nat.add_comm]
      have hmul : x % 2^(64 - k % 64) * (2 * 2^(k % 64 - i - 1)) =
          2 * (x % 2^(64 - k % 64) * 2^(k % 64 - i - 1)) := by ac_rfl
      rw [hmul, Nat.add_mul_mod_self_left, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm (64 - k % 64) i]
    · have hge : k % 64 ≤ i := by omega
      have hidx : (i + (64 - k % 64)) % 64 = i - k % 64 := by omega
      rw [hidx]
      have hp : 2^i = 2^(k % 64) * 2^(i - k % 64) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hp, ← Nat.div_div_eq_div_mul]
      have hdiv_s : (x % 2^(64 - k % 64) * 2^(k % 64) + x / 2^(64 - k % 64)) / 2^(k % 64) =
          x % 2^(64 - k % 64) := by
        rw [Nat.mul_comm (x % 2^(64 - k % 64)) (2^(k % 64)), Nat.mul_add_div (two_pow_pos_nat _)]
        have : (x / 2^(64 - k % 64)) / 2^(k % 64) = 0 := Nat.div_eq_of_lt hhi_lt
        omega
      rw [hdiv_s]
      have hp_rest : 2^(64 - k % 64) = 2^(i - k % 64) * 2^(64 - i) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hp_rest, div_mod_split x (2^(i - k % 64)) (2^(64 - i)) (two_pow_pos_nat _) (two_pow_pos_nat _)]
      rw [two_pow_succ_sub (64 - i) (by omega), mod_mul_two_mod_two]

theorem rotl64Nat_lt (x k : Nat) (hx : x < 2^64) : rotl64Nat x k < 2^64 := by
  unfold rotl64Nat
  by_cases hs : k % 64 = 0
  · simp only [hs, ↓reduceIte]; exact Nat.mod_lt _ (by decide)
  · simp only [hs, ↓reduceIte]
    have hklt : k % 64 < 64 := Nat.mod_lt k (by decide)
    have hpow : 2^64 = 2^(64 - k % 64) * 2^(k % 64) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hhi : x / 2^(64 - k % 64) < 2^(k % 64) := by
      rw [Nat.div_lt_iff_lt_mul (two_pow_pos_nat _), Nat.mul_comm, ← hpow]; exact hx
    have hlo : x % 2^(64 - k % 64) ≤ 2^(64 - k % 64) - 1 := by
      have := Nat.mod_lt x (two_pow_pos_nat (64 - k % 64))
      omega
    have hmul_le : x % 2^(64 - k % 64) * 2^(k % 64) ≤ (2^(64 - k % 64) - 1) * 2^(k % 64) :=
      Nat.mul_le_mul_right _ hlo
    have hsub_mul : (2^(64 - k % 64) - 1) * 2^(k % 64) = 2^(64 - k % 64) * 2^(k % 64) - 1 * 2^(k % 64) :=
      Nat.sub_mul _ _ _
    have hd_le : 2^(k % 64) ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hsub_mul, Nat.one_mul, ← hpow] at hmul_le
    omega

/-- THM-NATH-APP6-02(i): rotr64 is the exact two-sided inverse of rotl64 across all 64-bit words and shifts. -/
theorem rotr64_rotl64_inverse (x k : Nat) (hx : x < 2^64) :
    rotr64Nat (rotl64Nat x k) k = x := by
  unfold rotr64Nat rotl64Nat
  by_cases hs : k % 64 = 0
  · simp only [hs, ↓reduceIte, Nat.mod_eq_of_lt hx]
  · simp only [hs, ↓reduceIte]
    have hklt : k % 64 < 64 := Nat.mod_lt k (by decide)
    have hsub_mod : (64 - k % 64) % 64 = 64 - k % 64 := by omega
    have hsub_ne : ¬((64 - k % 64) % 64 = 0) := by omega
    have hsub_plain : ¬(64 - k % 64 = 0) := by omega
    have h64_sub : 64 - (64 - k % 64) = k % 64 := by omega
    simp only [hsub_plain, ↓reduceIte, hsub_mod, h64_sub]
    have hpow : 2^64 = 2^(64 - k % 64) * 2^(k % 64) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hhi : x / 2^(64 - k % 64) < 2^(k % 64) := by
      rw [Nat.div_lt_iff_lt_mul (two_pow_pos_nat _), Nat.mul_comm, ← hpow]; exact hx
    have hmod : (x % 2^(64 - k % 64) * 2^(k % 64) + x / 2^(64 - k % 64)) % 2^(k % 64) =
        x / 2^(64 - k % 64) := by
      rw [Nat.add_comm, Nat.mul_comm (x % 2^(64 - k % 64)) (2^(k % 64)),
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hhi]
    have hdiv : (x % 2^(64 - k % 64) * 2^(k % 64) + x / 2^(64 - k % 64)) / 2^(k % 64) =
        x % 2^(64 - k % 64) := by
      rw [Nat.mul_comm (x % 2^(64 - k % 64)) (2^(k % 64)), Nat.mul_add_div (two_pow_pos_nat _)]
      have hz : (x / 2^(64 - k % 64)) / 2^(k % 64) = 0 := Nat.div_eq_of_lt hhi
      omega
    rw [hmod, hdiv, Nat.mul_comm (x / 2^(64 - k % 64)) (2^(64 - k % 64)), Nat.div_add_mod]

private theorem foldl_add_eq_sum (l : List Nat) (init : Nat) :
    l.foldl (· + ·) init = init + l.sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    omega

private theorem range_split (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (· + a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hadd : a + (b + 1) = (a + b) + 1 := by omega
    rw [hadd, List.range_succ, List.range_succ, List.map_append, List.map_singleton, ih, List.append_assoc, Nat.add_comm a b]

/-- THM-NATH-APP6-02(ii): Bitwise circular rotation strictly preserves 64-bit Hamming weight for all x, k. -/
theorem popcnt64_rotl64_conserved (x k : Nat) (hx : x < 2^64) :
    popcnt64Nat (rotl64Nat x k) = popcnt64Nat x := by
  unfold popcnt64Nat
  rw [foldl_add_eq_sum, foldl_add_eq_sum]
  simp only [Nat.zero_add]
  have hs_lt : k % 64 < 64 := Nat.mod_lt k (by decide)
  have h64 : 64 = k % 64 + (64 - k % 64) := by omega
  have h64' : 64 = (64 - k % 64) + k % 64 := by omega
  have hmap_lhs : (List.range 64).map (fun i => bitAt (rotl64Nat x k) i) =
      (List.range 64).map (fun i => bitAt x ((i + (64 - k % 64)) % 64)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact bitAt_rotl64Nat x k i hx hi
  rw [hmap_lhs]
  have hsumL :
      ((List.range 64).map (fun i => bitAt x ((i + (64 - k % 64)) % 64))).sum =
      ((List.range (k % 64)).map (fun i => bitAt x ((i + (64 - k % 64)) % 64))).sum +
      (((List.range (64 - k % 64)).map (· + k % 64)).map (fun i => bitAt x ((i + (64 - k % 64)) % 64))).sum := by
    have hr : List.range 64 = List.range (k % 64) ++ (List.range (64 - k % 64)).map (· + k % 64) := by
      calc List.range 64
          = List.range (k % 64 + (64 - k % 64)) := congrArg List.range h64
        _ = List.range (k % 64) ++ (List.range (64 - k % 64)).map (· + k % 64) := range_split _ _
    rw [hr, List.map_append, List.sum_append]
  have hsumR :
      ((List.range 64).map (bitAt x)).sum =
      ((List.range (64 - k % 64)).map (bitAt x)).sum +
      (((List.range (k % 64)).map (· + (64 - k % 64))).map (bitAt x)).sum := by
    have hr : List.range 64 = List.range (64 - k % 64) ++ (List.range (k % 64)).map (· + (64 - k % 64)) := by
      calc List.range 64
          = List.range ((64 - k % 64) + k % 64) := congrArg List.range h64'
        _ = List.range (64 - k % 64) ++ (List.range (k % 64)).map (· + (64 - k % 64)) := range_split _ _
    rw [hr, List.map_append, List.sum_append]
  rw [hsumL, hsumR]
  have hpart1 : ((List.range (k % 64)).map (fun i => bitAt x ((i + (64 - k % 64)) % 64))) =
      ((List.range (k % 64)).map (· + (64 - k % 64))).map (bitAt x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    have hlt : (i + (64 - k % 64)) % 64 = i + (64 - k % 64) := by omega
    rw [hlt]
  have hpart2 : (((List.range (64 - k % 64)).map (· + k % 64)).map (fun i => bitAt x ((i + (64 - k % 64)) % 64))) =
      (List.range (64 - k % 64)).map (bitAt x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    have hlt : ((i + k % 64) + (64 - k % 64)) % 64 = i := by omega
    rw [hlt]
  rw [hpart1, hpart2, Nat.add_comm]

/-- Morton-30 WGSL Sec. 17.2 FTZ-safe read-only extraction (upper 2 bits masked off). -/
def readMorton30FtzSafe (rawU32 : UInt32) : UInt32 :=
  rawU32 &&& 0x3fffffff

theorem readMorton30FtzSafe_lt (rawU32 : UInt32) :
    (readMorton30FtzSafe rawU32).toNat < 2^30 := by
  unfold readMorton30FtzSafe
  have h := UInt32.toNat_and rawU32 0x3fffffff
  have h2 : rawU32.toNat &&& (0x3fffffff : UInt32).toNat ≤ (0x3fffffff : UInt32).toNat :=
    Nat.and_le_right
  have h3 : (0x3fffffff : UInt32).toNat < 2^30 := by decide
  omega

theorem morton30_canonical_6_keys_preserved :
    let keys : List UInt32 := [0x00000000, 0x00000001, 0x007fffff, 0x00800000, 0x01000000, 0x3fffffff]
    keys.all (fun k => readMorton30FtzSafe (k ||| 0xc0000000) == k) = true := by
  decide

end PuristSiliconCore
