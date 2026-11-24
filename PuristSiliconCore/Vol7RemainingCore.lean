import PuristSiliconCore.Anchor

namespace PuristSiliconCore

/-!
## Applied Purist Vol. VII — Remaining Mathlib-Free Algebraic & Discrete Core
Covers Sec. 6 (4-edge Sagnac gauge invariance, Routh & Kozai bounds),
Sec. 4 (Kerr horizon quadratic, GHSS sum law, Teukolsky-Starobinsky parity),
Sec. 5 (Dray-'t Hooft l<=24 Cayley unitarity & MSS bound),
Sec. 2 (IAU 2024 L_TCL breach bound & range scaling), and
Sec. 3 (5.0PN Pade-Laplace O(1) mode BIBO boundedness).
-/

/-! ### 1. Closed 4-Edge Sagnac Gauge Invariance & 2-Edge Omitted-Area Bias (Sec. 6) -/

structure SagnacVec3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

def sAdd (a b : SagnacVec3) : SagnacVec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def sSub (a b : SagnacVec3) : SagnacVec3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def sNeg (a : SagnacVec3) : SagnacVec3 := ⟨-a.x, -a.y, -a.z⟩
def sDot (a b : SagnacVec3) : Int := a.x * b.x + a.y * b.y + a.z * b.z
def sCross (a b : SagnacVec3) : SagnacVec3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def sagnac4ClosedArea2 (r1 r2 r3 r4 : SagnacVec3) : SagnacVec3 :=
  sAdd (sAdd (sCross r1 r2) (sCross r2 r3))
       (sAdd (sCross r3 r4) (sCross r4 r1))

def sagnac2EdgeArea2 (r1 r2 r3 r4 : SagnacVec3) : SagnacVec3 :=
  sAdd (sCross r1 r2) (sCross r3 r4)

def sagnacOmittedArea2 (r1 r2 r3 r4 : SagnacVec3) : SagnacVec3 :=
  sAdd (sCross r2 r3) (sCross r4 r1)

private theorem sVec_eq_of_fields {a b : SagnacVec3}
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

private theorem sCross_add_left (a b c : SagnacVec3) :
    sCross (sAdd a b) c = sAdd (sCross a c) (sCross b c) := by
  apply sVec_eq_of_fields <;> simp only [sCross, sAdd, Int.add_mul] <;> omega

private theorem sCross_add_right (a b c : SagnacVec3) :
    sCross a (sAdd b c) = sAdd (sCross a b) (sCross a c) := by
  apply sVec_eq_of_fields <;> simp only [sCross, sAdd, Int.mul_add] <;> omega

private theorem sCross_self (v : SagnacVec3) : sCross v v = ⟨0, 0, 0⟩ := by
  apply sVec_eq_of_fields <;> simp only [sCross]
  · rw [Int.mul_comm v.z v.y]; omega
  · rw [Int.mul_comm v.x v.z]; omega
  · rw [Int.mul_comm v.y v.x]; omega

private theorem sCross_antisymm (a b : SagnacVec3) : sCross a b = sNeg (sCross b a) := by
  apply sVec_eq_of_fields <;> simp only [sCross, sNeg]
  · rw [Int.mul_comm b.z a.y, Int.mul_comm b.y a.z]; omega
  · rw [Int.mul_comm b.x a.z, Int.mul_comm b.z a.x]; omega
  · rw [Int.mul_comm b.y a.x, Int.mul_comm b.x a.y]; omega

private theorem sCross_shift (a b v : SagnacVec3) :
    sCross (sAdd a v) (sAdd b v) =
      sAdd (sCross a b) (sSub (sCross a v) (sCross b v)) := by
  rw [sCross_add_left, sCross_add_right, sCross_add_right, sCross_self, sCross_antisymm v b]
  apply sVec_eq_of_fields <;> simp only [sAdd, sSub, sNeg] <;> omega

theorem sagnac_4edge_gauge_invariant (r1 r2 r3 r4 v : SagnacVec3) :
    sagnac4ClosedArea2 (sAdd r1 v) (sAdd r2 v) (sAdd r3 v) (sAdd r4 v) =
      sagnac4ClosedArea2 r1 r2 r3 r4 := by
  simp only [sagnac4ClosedArea2, sCross_shift]
  apply sVec_eq_of_fields <;> simp only [sAdd, sSub] <;> omega

theorem sagnac_1x_delay_gauge_invariant (omegaE r1 r2 r3 r4 v : SagnacVec3) :
    sDot omegaE (sagnac4ClosedArea2 (sAdd r1 v) (sAdd r2 v) (sAdd r3 v) (sAdd r4 v)) =
      sDot omegaE (sagnac4ClosedArea2 r1 r2 r3 r4) := by
  rw [sagnac_4edge_gauge_invariant]

theorem sagnac_4edge_equals_2edge_plus_omitted (r1 r2 r3 r4 : SagnacVec3) :
    sagnac4ClosedArea2 r1 r2 r3 r4 =
      sAdd (sagnac2EdgeArea2 r1 r2 r3 r4) (sagnacOmittedArea2 r1 r2 r3 r4) := by
  apply sVec_eq_of_fields <;>
    simp only [sagnac4ClosedArea2, sagnac2EdgeArea2, sagnacOmittedArea2, sAdd] <;> omega

theorem sagnac_2edge_fails_gauge_invariance :
    ∃ r1 r2 r3 r4 v : SagnacVec3,
      sagnac2EdgeArea2 (sAdd r1 v) (sAdd r2 v) (sAdd r3 v) (sAdd r4 v) ≠
        sagnac2EdgeArea2 r1 r2 r3 r4 := by
  refine ⟨⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨2, 1, 0⟩, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩, ?_⟩
  decide

/-! ### 2. Kerr Horizon Quadratic, GHSS Sum Law & Teukolsky-Starobinsky Sign Flip (Sec. 4) -/

theorem kerr_horizon_quad_eq_zero (M a b : Int) (hb : b * b = M * M - a * a) :
    (M + b) * (M + b) - 2 * M * (M + b) + a * a = 0 ∧
    (M - b) * (M - b) - 2 * M * (M - b) + a * a = 0 := by
  have h1 : (M + b) * (M + b) = M * M + 2 * (M * b) + b * b := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b M]
    omega
  have h2 : (M - b) * (M - b) = M * M - 2 * (M * b) + b * b := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b M]
    omega
  have h3 : 2 * M * (M + b) = 2 * (M * M) + 2 * (M * b) := by
    rw [Int.mul_add, Int.mul_assoc, Int.mul_assoc]
  have h4 : 2 * M * (M - b) = 2 * (M * M) - 2 * (M * b) := by
    rw [Int.mul_sub, Int.mul_assoc, Int.mul_assoc]
  omega

theorem kerr_horizon_sum_diff_and_area_id (M a b : Int) (hb : b * b = M * M - a * a) :
    ((M + b) + (M - b) = 2 * M) ∧
    ((M + b) - (M - b) = 2 * b) ∧
    ((M + b) * (M + b) + a * a = 2 * M * (M + b)) := by
  have hq := (kerr_horizon_quad_eq_zero M a b hb).1
  refine ⟨by omega, by omega, by omega⟩

theorem ghss_temperature_sum_cleared (M b tL tR D : Int)
    (hL : tL * D = M) (hR : tR * D = b) :
    (tL + tR) * D = M + b := by
  rw [Int.add_mul, hL, hR]

theorem teukolsky_superradiance_iff_neg_horizon_flux (R T fluxScale : Int)
    (hTS : R + T = fluxScale) :
    R > fluxScale ↔ T < 0 := by
  omega

/-! ### 3. Dray-'t Hooft l<=24 Cayley Unitarity & MSS Chaos Bound (Sec. 5) -/

theorem cayley_unitarity_algebra (p q : Int) :
    (q * q - p * p) * (q * q - p * p) + (2 * (p * q)) * (2 * (p * q)) =
      (q * q + p * p) * (q * q + p * p) := by
  have h1 : (q * q - p * p) * (q * q - p * p) =
      (q * q) * (q * q) - 2 * ((q * q) * (p * p)) + (p * p) * (p * p) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm (p * p) (q * q)]
    omega
  have h2 : (q * q + p * p) * (q * q + p * p) =
      (q * q) * (q * q) + 2 * ((q * q) * (p * p)) + (p * p) * (p * p) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (p * p) (q * q)]
    omega
  have h4c : (2 : Int) * 2 = 4 := by decide
  have h3 : (2 * (p * q)) * (2 * (p * q)) = 4 * ((q * q) * (p * p)) := by
    calc
      (2 * (p * q)) * (2 * (p * q))
        = 4 * ((p * q) * (p * q)) := by
            rw [Int.mul_assoc, Int.mul_comm (p * q) (2 * (p * q)),
                Int.mul_assoc, ← Int.mul_assoc 2 2 _, h4c]
      _ = 4 * ((q * q) * (p * p)) := by
            congr 1
            rw [Int.mul_assoc p q (p * q), Int.mul_comm q (p * q),
                ← Int.mul_assoc p (p * q) q, ← Int.mul_assoc p p q,
                Int.mul_assoc (p * p) q q, Int.mul_comm (p * p) (q * q)]
  omega

theorem dray_thooft_l24_mode_count_and_unitarity (p q : Nat → Int) :
    (List.range 25).length = 25 ∧
    ∀ l, l ≤ 24 →
      (q l * q l - p l * p l) * (q l * q l - p l * p l) +
        (2 * (p l * q l)) * (2 * (p l * q l)) =
        (q l * q l + p l * p l) * (q l * q l + p l * p l) := by
  refine ⟨by decide, fun l _ => cayley_unitarity_algebra (p l) (q l)⟩

theorem mss_chaos_bound_le_and_einstein_limit
    (kappaH alpha' twoEllSq : Nat) (hAlpha : alpha' ≤ twoEllSq) :
    kappaH * (twoEllSq - alpha') ≤ kappaH * twoEllSq ∧
    (alpha' = 0 → kappaH * (twoEllSq - alpha') = kappaH * twoEllSq) := by
  have hSub : (twoEllSq - alpha') + alpha' = twoEllSq := by omega
  have hEq : kappaH * (twoEllSq - alpha') + kappaH * alpha' = kappaH * twoEllSq := by
    rw [← Nat.mul_add, hSub]
  refine ⟨by omega, fun hz => by subst hz; simp⟩

/-! ### 4. 1PN Routh Discriminant & Kozai Critical Inclination Bounds (Sec. 6) -/

def routhDiscriminantScaled (p q : Nat) : Int :=
  (q : Int) * q - 27 * (p : Int) * ((q : Int) - p)

theorem routh_earth_moon_and_1pn_strictly_stable :
    routhDiscriminantScaled 121505856 10000000000 > 0 ∧
    routhDiscriminantScaled 385206825 10000000000 > 0 ∧
    (121505856 : Nat) < 385206825 := by
  decide

theorem routh_newtonian_root_bracket :
    routhDiscriminantScaled 385208965 10000000000 > 0 ∧
    routhDiscriminantScaled 385208966 10000000000 < 0 := by
  decide

theorem kozai_1pn_shift_strictly_inside_interval :
    5 * ((2000000 : Int) - 56268) - 10000000 + 281340 = 0 ∧
    (0 : Nat) < 2000000 - 56268 ∧
    (2000000 : Nat) - 56268 < 2000000 ∧
    (2000000 : Nat) < 6000000 := by
  decide

/-! ### 5. IAU 2024 L_TCL Drift Breach & 5.0PN Pade-Laplace BIBO Stability (Secs. 2 & 3) -/

theorem ltcl_legacy_drift_breaches_1ps_under_12min :
    let lTcl := (64839000 : Nat)
    let lTclLeg := (64839148 : Nat)
    let driftPerDay := (lTclLeg - lTcl) * 86400
    driftPerDay = 12787200 ∧
    driftPerDay * 36525 / 100 = 4670524800 ∧
    driftPerDay * 720 > 100000 * 86400 := by
  decide

theorem ltcl_daily_range_metrics_exact :
    let lTcl := (64839000 : Nat)
    let cSI := (299792458 : Nat)
    let secPerDay := (86400 : Nat)
    let oneWay := lTcl * cSI * secPerDay
    let twoWay := 2 * oneWay
    1679464211100000000000 ≤ oneWay ∧
    oneWay < 1679464211200000000000 ∧
    twoWay = 2 * oneWay := by
  decide

private theorem nat_mul_le_cancel_left {S y M : Nat} (hS : 0 < S) (h : S * y ≤ S * M) :
    y ≤ M := by
  by_cases hy : y ≤ M
  · exact hy
  · have hd : y = M + ((y - M - 1) + 1) := by omega
    rw [hd, Nat.mul_add, Nat.mul_succ] at h
    omega

theorem pade_tail_mode_bibo_bound
    (S alpha B M : Nat) (yAbs : Nat → Nat)
    (hS : 0 < S) (hAlpha : alpha ≤ S)
    (hStep : ∀ n, S * yAbs (n + 1) ≤ alpha * yAbs n + B)
    (hDrive : B ≤ (S - alpha) * M)
    (hInit : yAbs 0 ≤ M) :
    ∀ n, yAbs n ≤ M := by
  intro n
  induction n with
  | zero => exact hInit
  | succ k ih =>
    have hM : M = yAbs k + (M - yAbs k) := by omega
    have hAlphaLe : alpha * yAbs k ≤ alpha * M := by
      rw [hM, Nat.mul_add]
      omega
    have hSsplit : S = alpha + (S - alpha) := by omega
    have hSM : alpha * M + (S - alpha) * M = S * M := by
      rw [← Nat.add_mul, ← hSsplit]
    have hBound : S * yAbs (k + 1) ≤ S * M := by
      have hk := hStep k
      omega
    exact nat_mul_le_cancel_left hS hBound

end PuristSiliconCore
