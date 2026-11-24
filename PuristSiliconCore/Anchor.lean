namespace PuristSiliconCore

def documentCode : String := "TMD-12-PURIST-APPLIED-VOL-VI-SOLINAS-IVC-2026"
def preprintDoi  : String := "10.5281/zenodo.24392562"
def softwareDoi  : String := "10.5281/zenodo.24417410"

def p64  : Nat := 2^64 - 59
def p106 : Nat := 2^106 - 117

/-- Infrastructure smoke check preserved for baseline harness compatibility. -/
theorem anchor_infrastructure_smoke : 2 + 2 = 4 := rfl

/-- MATH-ERR-01: Exact decimal expansion of p64 and p106 (...947). -/
theorem p64_exact_decimal : p64 = 18446744073709551557 := rfl
theorem p106_exact_decimal : p106 = 81129638414606681695789005143947 := rfl

theorem p64_pos : 0 < p64 := by decide
theorem p106_pos : 0 < p106 := by decide

/-- Residue-class criteria for irreducible quadratic/quartic towers (THM-DILATON-APP6-01). -/
theorem p64_mod_8 : p64 % 8 = 5 := rfl
theorem p64_mod_4 : p64 % 4 = 1 := rfl
theorem p106_mod_4 : p106 % 4 = 3 := rfl

/-- Solinas folding congruences: 2^64 ≡ 59 (mod p64) and 2^106 ≡ 117 (mod p106). -/
theorem two_pow_64_eq_p64_add_59 : 2^64 = p64 + 59 := rfl
theorem two_pow_106_eq_p106_add_117 : 2^106 = p106 + 117 := rfl
theorem two_pow_64_mod_p64 : (2^64) % p64 = 59 := rfl
theorem two_pow_106_mod_p106 : (2^106) % p106 = 117 := rfl

/-- Base-16 kernel-transparent modular exponentiation (16 steps for 64-bit, 27 for 106-bit). -/
def modPowSmall (n base m : Nat) : Nat :=
  match n with
  | 0 => 1 % m
  | n + 1 => (modPowSmall n base m * (base % m)) % m

def modPow16Fuel (fuel base exp m : Nat) : Nat :=
  match fuel with
  | 0 => 1 % m
  | fuel + 1 =>
    match exp with
    | 0 => 1 % m
    | _ =>
      let acc := modPow16Fuel fuel base (exp / 16) m
      let a2 := (acc * acc) % m
      let a4 := (a2 * a2) % m
      let a8 := (a4 * a4) % m
      let a16 := (a8 * a8) % m
      (a16 * modPowSmall (exp % 16) base m) % m

def modPow64 (base exp m : Nat) : Nat :=
  match m with
  | 0 => 0
  | 1 => 0
  | _ => modPow16Fuel 18 (base % m) exp m

def modPow128 (base exp m : Nat) : Nat :=
  match m with
  | 0 => 0
  | 1 => 0
  | _ => modPow16Fuel 32 (base % m) exp m

/-- Precomputed Frobenius primitive 4th-root factor zeta = 2^((p64 - 1)/4) mod p64. -/
def frobeniusZetaP64 : Nat := modPow64 2 ((p64 - 1) / 4) p64

section EulerAndFrobenius
set_option maxRecDepth 8192

/-- Euler's criterion: (2 / p64) = -1, certifying u^2 - 2 irreducible over F_{p64}. -/
theorem euler_two_qnr_p64 : modPow64 2 ((p64 - 1) / 2) p64 = p64 - 1 := rfl

/-- Euler's criterion: (-1 / p106) = -1, certifying u^2 + 1 irreducible over F_{p106}. -/
theorem euler_neg_one_qnr_p106 : modPow128 (p106 - 1) ((p106 - 1) / 2) p106 = p106 - 1 := rfl

theorem frobeniusZetaP64_sq_mod : (frobeniusZetaP64 * frobeniusZetaP64) % p64 = p64 - 1 := rfl
theorem frobeniusZetaP64_pow4_mod : modPow64 frobeniusZetaP64 4 p64 = 1 := rfl

end EulerAndFrobenius

end PuristSiliconCore
