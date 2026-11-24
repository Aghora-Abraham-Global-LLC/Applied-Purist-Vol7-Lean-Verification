import PuristSiliconCore.Anchor

namespace PuristSiliconCore

/-!
## Mathlib-Free Kernel-Checked Pocklington Primality Certificates for p64 and p106
Proves `IsPrime p64` (2^64 - 59) and `IsPrime p106` (2^106 - 117) purely in Lean 4's kernel
with zero Mathlib, zero `sorry`, and zero `native_decide`, directly reusing Anchor.lean's
`modPow64` and `modPow128`.
-/

def IsPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d, 1 < d → d < p → ¬ (d ∣ p)

/-! ### 1. Small-Prime Trial Scanner & Elementary Divisibility -/

def noDivisorBelow (p : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | d + 1 => decide (p % (d + 1) ≠ 0) && noDivisorBelow p d

private theorem noDivisorBelow_sound (p k d : Nat)
    (h : noDivisorBelow p k = true) (hd1 : 1 < d) (hdk : d ≤ k) :
    p % d ≠ 0 := by
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m' =>
      unfold noDivisorBelow at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hEq : d = m' + 2
      · subst hEq; exact h.1
      · exact ih h.2 (by omega)

private theorem isPrime_of_noDivisorBelow (p : Nat) (hp : 1 < p)
    (h : noDivisorBelow p (p - 1) = true) : IsPrime p := by
  refine ⟨hp, fun d hd1 hdp hdvd => ?_⟩
  exact noDivisorBelow_sound p (p - 1) d h hd1 (by omega) (Nat.mod_eq_zero_of_dvd hdvd)

private theorem nat_sq_lt_sq {a b : Nat} (h : a < b) : a * a < b * b := by
  have ha : a + 1 ≤ b := h
  have h1 : a * a ≤ (a + 1) * a := Nat.mul_le_mul_right a (by omega)
  have h2 : (a + 1) * (a + 1) ≤ b * b := Nat.mul_le_mul ha ha
  have h3 : (a + 1) * a + (a + 1) = (a + 1) * (a + 1) := (Nat.mul_succ (a + 1) a).symm
  omega

private theorem dvd_right_of_add {r x y z : Nat}
    (hx : r ∣ x) (hy : r ∣ y) (hsum : x = y + z) : r ∣ z := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  by_cases hr : r = 0
  · subst hr; simp only [Nat.zero_mul] at hsum; exact ⟨0, by omega⟩
  · have hba : b ≤ a := by
      apply Classical.byContradiction
      intro hgt
      have hs : b = a + ((b - a - 1) + 1) := by omega
      rw [hs, Nat.mul_add, Nat.mul_succ] at hsum
      omega
    refine ⟨a - b, ?_⟩
    have hab : (a - b) + b = a := by omega
    have hmul : r * (a - b) + r * b = r * a := by
      rw [← Nat.mul_add, hab]
    omega

private theorem dvd_mod_of_dvd {r a b : Nat} (ha : r ∣ a) (hb : r ∣ b) : r ∣ a % b := by
  have hsplit : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
  exact dvd_right_of_add ha (Nat.dvd_trans hb (Nat.dvd_mul_right b _)) hsplit

private theorem exists_prime_dvd (m : Nat) (hm : 1 < m) :
    ∃ r, IsPrime r ∧ r ∣ m := by
  induction m using Nat.strongRecOn with
  | ind k ih =>
    by_cases hp : IsPrime k
    · exact ⟨k, hp, Nat.dvd_refl k⟩
    · have ⟨d, hd1, hdk, hdvd⟩ : ∃ d, 1 < d ∧ d < k ∧ d ∣ k := by
        apply Classical.byContradiction
        intro hno
        apply hp
        refine ⟨hm, fun d hd1 hdk hdvd => hno ⟨d, hd1, hdk, hdvd⟩⟩
      rcases ih d hdk hd1 with ⟨r, hrp, hrd⟩
      exact ⟨r, hrp, Nat.dvd_trans hrd hdvd⟩

private theorem exists_prime_dvd_sq_le (n : Nat) (hn : 1 < n) (hnp : ¬ IsPrime n) :
    ∃ r, IsPrime r ∧ r ∣ n ∧ r * r ≤ n := by
  have ⟨d, hd1, hdn, hdvd⟩ : ∃ d, 1 < d ∧ d < n ∧ d ∣ n := by
    apply Classical.byContradiction
    intro hno
    apply hnp
    refine ⟨hn, fun d hd1 hdn hdvd => hno ⟨d, hd1, hdn, hdvd⟩⟩
  let e := n / d
  have hde : d * e = n := Nat.mul_div_cancel' hdvd
  have he1 : 1 < e := by
    apply Classical.byContradiction
    intro hle
    have : e ≤ 1 := by omega
    have : d * e ≤ d * 1 := Nat.mul_le_mul_left d this
    omega
  by_cases hcmp : d ≤ e
  · rcases exists_prime_dvd d hd1 with ⟨r, hrp, hrd⟩
    have hrle : r ≤ d := Nat.le_of_dvd (by omega) hrd
    have hrr : r * r ≤ d * d := Nat.mul_le_mul hrle hrle
    have hdd : d * d ≤ d * e := Nat.mul_le_mul_left d hcmp
    exact ⟨r, hrp, Nat.dvd_trans hrd hdvd, by omega⟩
  · rcases exists_prime_dvd e he1 with ⟨r, hrp, hre⟩
    have hrle : r ≤ e := Nat.le_of_dvd (by omega) hre
    have hrr : r * r ≤ e * e := Nat.mul_le_mul hrle hrle
    have hee : e * e ≤ d * e := Nat.mul_le_mul_right e (by omega)
    exact ⟨r, hrp, Nat.dvd_trans hre ⟨d, by rw [Nat.mul_comm, hde]⟩, by omega⟩

/-! ### 2. Euclid's Prime Lemma & Fermat's Little Theorem -/

private theorem isPrime_dvd_mul_lt (r k b : Nat)
    (hr : IsPrime r) (hk1 : 1 ≤ k) (hkr : k < r) (hdvd : r ∣ k * b) : r ∣ b := by
  induction k using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm1 : m = 1
    · subst hm1; simpa using hdvd
    · have hmgt : 1 < m := by omega
      have hndvd : ¬ (m ∣ r) := hr.2 m hmgt hkr
      have hmodPos : 1 ≤ r % m := by
        have hnz : r % m ≠ 0 := fun hz => hndvd (Nat.dvd_of_mod_eq_zero hz)
        omega
      have hmodLt : r % m < m := Nat.mod_lt r (by omega)
      have hmulEq : r * b = (m * b) * (r / m) + (r % m) * b := by
        have hdiv := Nat.div_add_mod r m
        calc r * b = (m * (r / m) + r % m) * b := by rw [hdiv]
          _ = (m * (r / m)) * b + (r % m) * b := Nat.add_mul _ _ _
          _ = (m * b) * (r / m) + (r % m) * b := by
                rw [Nat.mul_assoc, Nat.mul_comm (r / m) b, ← Nat.mul_assoc]
      have hmodDvd : r ∣ (r % m) * b :=
        dvd_right_of_add (Nat.dvd_mul_right r b)
          (Nat.dvd_trans hdvd (Nat.dvd_mul_right (m * b) (r / m))) hmulEq
      exact ih (r % m) hmodLt hmodPos (by omega) hmodDvd

theorem isPrime_dvd_mul {r a b : Nat} (hr : IsPrime r) (hdvd : r ∣ a * b) :
    r ∣ a ∨ r ∣ b := by
  by_cases ha : r ∣ a
  · exact Or.inl ha
  · refine Or.inr ?_
    have hrPos : 0 < r := by have := hr.1; omega
    have hmodPos : 1 ≤ a % r := by
      have hnz : a % r ≠ 0 := fun hz => ha (Nat.dvd_of_mod_eq_zero hz)
      omega
    have hmodLt : a % r < r := Nat.mod_lt a hrPos
    have hsplit : a * b = r * ((a / r) * b) + (a % r) * b := by
      have hdiv := Nat.div_add_mod a r
      calc a * b = (r * (a / r) + a % r) * b := by rw [hdiv]
        _ = (r * (a / r)) * b + (a % r) * b := Nat.add_mul _ _ _
        _ = r * ((a / r) * b) + (a % r) * b := by rw [Nat.mul_assoc]
    have hmodDvd : r ∣ (a % r) * b :=
      dvd_right_of_add hdvd (Nat.dvd_mul_right r ((a / r) * b)) hsplit
    exact isPrime_dvd_mul_lt r (a % r) b hr hmodPos hmodLt hmodDvd

private def range1 : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: range1 n

private theorem mem_range1 {x n : Nat} : x ∈ range1 n ↔ 1 ≤ x ∧ x ≤ n := by
  induction n with
  | zero =>
    constructor
    · intro h; cases h
    · intro ⟨h1, h2⟩; omega
  | succ k ih =>
    simp only [range1, List.mem_cons, ih]
    omega

private theorem length_range1 (n : Nat) : (range1 n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [range1, ih]

private def AllDistinct : List Nat → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ AllDistinct xs

private def prodMod (r : Nat) : List Nat → Nat
  | [] => 1 % r
  | x :: xs => (x * prodMod r xs) % r

private def eraseOne (y : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x == y then xs else x :: eraseOne y xs

private theorem mem_eraseOne_of_ne {z y : Nat} {xs : List Nat}
    (hz : z ∈ xs) (hne : z ≠ y) : z ∈ eraseOne y xs := by
  induction xs with
  | nil => cases hz
  | cons x t ih =>
    simp only [List.mem_cons] at hz
    cases hxy : (x == y) with
    | true =>
      have hxy' : x = y := beq_iff_eq.mp hxy
      have her : eraseOne y (x :: t) = t := by simp only [eraseOne, hxy]; rfl
      rw [her]
      rcases hz with rfl | hzt
      · exact absurd hxy' hne
      · exact hzt
    | false =>
      have her : eraseOne y (x :: t) = x :: eraseOne y t := by simp only [eraseOne, hxy]; rfl
      rw [her, List.mem_cons]
      rcases hz with rfl | hzt
      · exact Or.inl rfl
      · exact Or.inr (ih hzt)

private theorem length_eraseOne {y : Nat} {xs : List Nat} (hy : y ∈ xs) :
    (eraseOne y xs).length + 1 = xs.length := by
  induction xs with
  | nil => cases hy
  | cons x t ih =>
    simp only [List.mem_cons] at hy
    cases hxy : (x == y) with
    | true =>
      have her : eraseOne y (x :: t) = t := by simp only [eraseOne, hxy]; rfl
      rw [her, List.length_cons]
    | false =>
      have hxy' : x ≠ y := fun h => by subst h; simp at hxy
      have her : eraseOne y (x :: t) = x :: eraseOne y t := by simp only [eraseOne, hxy]; rfl
      rw [her, List.length_cons, List.length_cons]
      rcases hy with rfl | hyt
      · exact absurd rfl hxy'
      · have := ih hyt; omega

private theorem prodMod_eraseOne (r y : Nat) (xs : List Nat) (hy : y ∈ xs) :
    prodMod r xs = (y * prodMod r (eraseOne y xs)) % r := by
  induction xs with
  | nil => cases hy
  | cons x t ih =>
    simp only [List.mem_cons] at hy
    cases hxy : (x == y) with
    | true =>
      have hxy' : x = y := beq_iff_eq.mp hxy
      have her : eraseOne y (x :: t) = t := by simp only [eraseOne, hxy]; rfl
      rw [her, hxy']
      rfl
    | false =>
      have hxy' : x ≠ y := fun h => by subst h; simp at hxy
      have her : eraseOne y (x :: t) = x :: eraseOne y t := by simp only [eraseOne, hxy]; rfl
      rw [her]
      rcases hy with rfl | hyt
      · exact absurd rfl hxy'
      · have lhsEq : prodMod r (x :: t) = (x * prodMod r t) % r := rfl
        have rhsEq : prodMod r (x :: eraseOne y t) = (x * prodMod r (eraseOne y t)) % r := rfl
        rw [lhsEq, rhsEq, ih hyt]
        calc (x * (y * prodMod r (eraseOne y t) % r)) % r
          _ = ((x % r) * ((y * prodMod r (eraseOne y t) % r) % r)) % r := Nat.mul_mod _ _ _
          _ = ((x % r) * (y * prodMod r (eraseOne y t) % r)) % r := by rw [Nat.mod_mod]
          _ = (x * (y * prodMod r (eraseOne y t))) % r := (Nat.mul_mod _ _ _).symm
          _ = (y * (x * prodMod r (eraseOne y t))) % r := by rw [Nat.mul_left_comm]
          _ = ((y % r) * (x * prodMod r (eraseOne y t) % r)) % r := Nat.mul_mod _ _ _
          _ = ((y % r) * ((x * prodMod r (eraseOne y t) % r) % r)) % r := by rw [Nat.mod_mod]
          _ = (y * (x * prodMod r (eraseOne y t) % r)) % r := (Nat.mul_mod _ _ _).symm

private theorem prodMod_perm_eq (r : Nat) (ys xs : List Nat)
    (hlen : ys.length = xs.length)
    (hsub : ∀ y, y ∈ ys → y ∈ xs)
    (hdist : AllDistinct ys) :
    prodMod r xs = prodMod r ys := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons y ys' ih =>
    have hyxs : y ∈ xs := hsub y (by simp)
    have hlen' : ys'.length = (eraseOne y xs).length := by
      have h1 := length_eraseOne hyxs
      simp only [List.length_cons] at hlen
      omega
    have hsub' : ∀ z, z ∈ ys' → z ∈ eraseOne y xs := by
      intro z hz
      have hzx : z ∈ xs := hsub z (by simp [hz])
      have hne : z ≠ y := fun h => by subst h; exact hdist.1 hz
      exact mem_eraseOne_of_ne hzx hne
    have hih := ih (eraseOne y xs) hlen' hsub' hdist.2
    rw [prodMod_eraseOne r y xs hyxs, hih]
    rfl

private theorem prodMod_map_mul (r a : Nat) (xs : List Nat) :
    prodMod r (xs.map (fun x => (a * x) % r)) = (a ^ xs.length * prodMod r xs) % r := by
  induction xs with
  | nil =>
    simp [prodMod]
  | cons x t ih =>
    simp only [List.map_cons, List.length_cons]
    change (((a * x) % r) * prodMod r (t.map (fun z => (a * z) % r))) % r =
      (a ^ (t.length + 1) * ((x * prodMod r t) % r)) % r
    rw [ih, Nat.pow_succ]
    calc ((a * x) % r * ((a ^ t.length * prodMod r t) % r)) % r
      _ = ((a * x) * (a ^ t.length * prodMod r t)) % r := (Nat.mul_mod _ _ _).symm
      _ = ((a ^ t.length * a) * (x * prodMod r t)) % r := by
            rw [Nat.mul_assoc a x _, Nat.mul_left_comm x (a ^ t.length) _,
                ← Nat.mul_assoc a (a ^ t.length) _, Nat.mul_comm a (a ^ t.length)]
      _ = (((a ^ t.length * a) % r) * ((x * prodMod r t) % r)) % r := Nat.mul_mod _ _ _
      _ = (((a ^ t.length * a) % r) * (((x * prodMod r t) % r) % r)) % r := by rw [Nat.mod_mod]
      _ = ((a ^ t.length * a) * ((x * prodMod r t) % r)) % r := (Nat.mul_mod _ _ _).symm

private theorem not_dvd_prodMod_range1 (r n : Nat) (hr : IsPrime r) (hn : n < r) :
    ¬ (r ∣ prodMod r (range1 n)) := by
  induction n with
  | zero =>
    simp only [range1, prodMod]
    have hr1 : 1 < r := hr.1
    rw [Nat.mod_eq_of_lt hr1]
    intro h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  | succ k ih =>
    have ihk := ih (by omega)
    intro hdvd
    change r ∣ ((k + 1) * prodMod r (range1 k)) % r at hdvd
    have hmulDvd : r ∣ (k + 1) * prodMod r (range1 k) := by
      have hdiv := (Nat.div_add_mod ((k + 1) * prodMod r (range1 k)) r).symm
      rw [hdiv]
      exact Nat.dvd_add (Nat.dvd_mul_right r _) hdvd
    rcases isPrime_dvd_mul hr hmulDvd with hk1 | hprod
    · have := Nat.le_of_dvd (by omega) hk1
      omega
    · exact ihk hprod

private theorem mul_mod_inj_dvd {r a x y : Nat}
    (hr : IsPrime r) (ha : ¬ (r ∣ a))
    (hx1 : 1 ≤ x) (hx2 : x < r) (hy1 : 1 ≤ y) (hy2 : y < r)
    (heq : (a * x) % r = (a * y) % r) : x = y := by
  by_cases hxy : y ≤ x
  · have hq : r ∣ a * (x - y) := by
      have h1 : a * x = r * ((a * x) / r) + (a * x) % r := (Nat.div_add_mod (a * x) r).symm
      have h2 : a * y = r * ((a * y) / r) + (a * y) % r := (Nat.div_add_mod (a * y) r).symm
      have hx' : x = y + (x - y) := by omega
      have h3 : a * x = a * y + a * (x - y) := by
        calc a * x = a * (y + (x - y)) := congrArg (a * ·) hx'
          _ = a * y + a * (x - y) := Nat.mul_add a y (x - y)
      have h4 : r * ((a * x) / r) = r * ((a * y) / r) + a * (x - y) := by omega
      exact dvd_right_of_add (Nat.dvd_mul_right r _) (Nat.dvd_mul_right r _) h4
    rcases isPrime_dvd_mul hr hq with ha' | hdiff
    · exact absurd ha' ha
    · by_cases hpos : x - y = 0
      · omega
      · have := Nat.le_of_dvd (by omega) hdiff
        omega
  · have hq : r ∣ a * (y - x) := by
      have h1 : a * y = r * ((a * y) / r) + (a * y) % r := (Nat.div_add_mod (a * y) r).symm
      have h2 : a * x = r * ((a * x) / r) + (a * x) % r := (Nat.div_add_mod (a * x) r).symm
      have hy' : y = x + (y - x) := by omega
      have h3 : a * y = a * x + a * (y - x) := by
        calc a * y = a * (x + (y - x)) := congrArg (a * ·) hy'
          _ = a * x + a * (y - x) := Nat.mul_add a x (y - x)
      have h4 : r * ((a * y) / r) = r * ((a * x) / r) + a * (y - x) := by omega
      exact dvd_right_of_add (Nat.dvd_mul_right r _) (Nat.dvd_mul_right r _) h4
    rcases isPrime_dvd_mul hr hq with ha' | hdiff
    · exact absurd ha' ha
    · by_cases hpos : y - x = 0
      · omega
      · have := Nat.le_of_dvd (by omega) hdiff
        omega

private theorem allDistinct_map_mul (r a n : Nat)
    (hr : IsPrime r) (ha : ¬ (r ∣ a)) (hn : n < r) :
    AllDistinct ((range1 n).map (fun x => (a * x) % r)) := by
  induction n with
  | zero => trivial
  | succ k ih =>
    simp only [range1, List.map_cons]
    refine ⟨fun hmem => ?_, ih (by omega)⟩
    rcases List.mem_map.mp hmem with ⟨y, hymem, heq⟩
    have hyb := mem_range1.mp hymem
    have heq' : (a * (k + 1)) % r = (a * y) % r := heq.symm
    have hxy := mul_mod_inj_dvd hr ha (by omega) hn hyb.1 (by omega) heq'
    omega

theorem fermat_little_theorem {r a : Nat} (hr : IsPrime r) (ha : ¬ (r ∣ a)) :
    a ^ (r - 1) % r = 1 := by
  let xs := range1 (r - 1)
  let ys := xs.map (fun x => (a * x) % r)
  have hlen : ys.length = xs.length := by simp [ys]
  have hsub : ∀ y, y ∈ ys → y ∈ xs := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxb := mem_range1.mp hx
    have hrPos : 0 < r := by have := hr.1; omega
    have hnx : ¬ (r ∣ x) := fun hdx => by
      have := Nat.le_of_dvd (by omega) hdx
      omega
    have hndvd : ¬ (r ∣ a * x) := fun hdm => by
      rcases isPrime_dvd_mul hr hdm with ha' | hx'
      · exact ha ha'
      · exact hnx hx'
    have hnz : (a * x) % r ≠ 0 := fun hz => hndvd (Nat.dvd_of_mod_eq_zero hz)
    have hlt : (a * x) % r < r := Nat.mod_lt (a * x) hrPos
    exact mem_range1.mpr ⟨by omega, by omega⟩
  have hdist : AllDistinct ys := allDistinct_map_mul r a (r - 1) hr ha (by have := hr.1; omega)
  have hperm := prodMod_perm_eq r ys xs hlen hsub hdist
  have hmap := prodMod_map_mul r a xs
  have hP : prodMod r xs = (a ^ (r - 1) * prodMod r xs) % r := by
    calc prodMod r xs = prodMod r ys := hperm
      _ = (a ^ xs.length * prodMod r xs) % r := hmap
      _ = (a ^ (r - 1) * prodMod r xs) % r := by rw [length_range1]
  let P := prodMod r xs
  have hPndvd : ¬ (r ∣ P) := not_dvd_prodMod_range1 r (r - 1) hr (by have := hr.1; omega)
  have haPos : 1 ≤ a := by
    apply Classical.byContradiction
    intro h0
    have ha0 : a = 0 := by omega
    subst ha0
    exact ha (Nat.dvd_zero r)
  have hPowPos : 1 ≤ a ^ (r - 1) := Nat.pow_pos haPos
  have hmul : a ^ (r - 1) * P = r * ((a ^ (r - 1) * P) / r) + P := by
    have hdiv := (Nat.div_add_mod (a ^ (r - 1) * P) r).symm
    change a ^ (r - 1) * P = r * ((a ^ (r - 1) * P) / r) + P
    rw [← hP] at hdiv
    exact hdiv
  have hsplit : a ^ (r - 1) * P = P + (a ^ (r - 1) - 1) * P := by
    have ha1 : a ^ (r - 1) = 1 + (a ^ (r - 1) - 1) := by omega
    calc a ^ (r - 1) * P = (1 + (a ^ (r - 1) - 1)) * P := congrArg (· * P) ha1
      _ = 1 * P + (a ^ (r - 1) - 1) * P := Nat.add_mul _ _ _
      _ = P + (a ^ (r - 1) - 1) * P := by rw [Nat.one_mul]
  have hdvdProd : r ∣ (a ^ (r - 1) - 1) * P :=
    ⟨(a ^ (r - 1) * P) / r, by omega⟩
  rcases isPrime_dvd_mul hr hdvdProd with hpow | hP'
  · rcases hpow with ⟨t, ht⟩
    have ht1 : a ^ (r - 1) = r * t + 1 := by omega
    rw [ht1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr.1]
  · exact absurd hP' hPndvd

/-! ### 3. Fast Kernel GCD Fuel + Structural Pocklington Theorems -/

def myGcdFuel (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if b == 0 then a else myGcdFuel fuel b (a % b)

private theorem myGcdFuel_dvd (fuel a b r : Nat) (ha : r ∣ a) (hb : r ∣ b) :
    r ∣ myGcdFuel fuel a b := by
  induction fuel generalizing a b with
  | zero => exact Nat.dvd_zero r
  | succ f ih =>
    unfold myGcdFuel
    cases hb0 : (b == 0) with
    | true => exact ha
    | false => exact ih b (a % b) hb (dvd_mod_of_dvd ha hb)

private theorem myGcdFuel_dvd_args (fuel a b : Nat) (hbf : b < fuel) :
    myGcdFuel fuel a b ∣ a ∧ myGcdFuel fuel a b ∣ b := by
  induction fuel generalizing a b with
  | zero => omega
  | succ f ih =>
    cases hb0 : (b == 0) with
    | true =>
      have hb0' : b = 0 := beq_iff_eq.mp hb0
      subst hb0'
      have hstep : myGcdFuel (f + 1) a 0 = a := by simp only [myGcdFuel]; rfl
      rw [hstep]
      exact ⟨Nat.dvd_refl a, Nat.dvd_zero _⟩
    | false =>
      have hbne : b ≠ 0 := fun h => by subst h; simp at hb0
      have hmod : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hbne)
      have hstep : myGcdFuel (f + 1) a b = myGcdFuel f b (a % b) := by
        simp only [myGcdFuel, hb0]; rfl
      rw [hstep]
      have ih' := ih b (a % b) (by omega)
      rcases ih' with ⟨hdb, hdmod⟩
      refine ⟨?_, hdb⟩
      have hsum : myGcdFuel f b (a % b) ∣ b * (a / b) + a % b :=
        Nat.dvd_add (Nat.dvd_trans hdb (Nat.dvd_mul_right b _)) hdmod
      have hsplit : b * (a / b) + a % b = a := Nat.div_add_mod a b
      rcases hsum with ⟨u, hu⟩
      exact ⟨u, hsplit.symm.trans hu⟩

private theorem pow_mod_step (a r e1 e2 : Nat) (hr : 1 < r)
    (h1 : a ^ e1 % r = 1) (h2 : a ^ e2 % r = 1) :
    a ^ (e1 % e2) % r = 1 := by
  have hdiv : e1 = e2 * (e1 / e2) + e1 % e2 := (Nat.div_add_mod e1 e2).symm
  have hpow : a ^ e1 % r = ((a ^ e2) ^ (e1 / e2) * a ^ (e1 % e2)) % r := by
    calc a ^ e1 % r = a ^ (e2 * (e1 / e2) + e1 % e2) % r := by rw [← hdiv]
      _ = ((a ^ e2) ^ (e1 / e2) * a ^ (e1 % e2)) % r := by rw [Nat.pow_add, Nat.pow_mul]
  have h1pow : (a ^ e2) ^ (e1 / e2) % r = 1 := by
    rw [Nat.pow_mod, h2, Nat.one_pow, Nat.mod_eq_of_lt hr]
  rw [hpow, Nat.mul_mod, h1pow, Nat.one_mul, Nat.mod_mod] at h1
  exact h1

private theorem pow_mod_myGcdFuel_one (a r fuel e1 e2 : Nat) (hr : 1 < r) (hf : e2 < fuel)
    (h1 : a ^ e1 % r = 1) (h2 : a ^ e2 % r = 1) :
    a ^ (myGcdFuel fuel e1 e2) % r = 1 := by
  induction fuel generalizing e1 e2 with
  | zero => omega
  | succ f ih =>
    unfold myGcdFuel
    cases hb0 : (e2 == 0) with
    | true => exact h1
    | false =>
      have hne : e2 ≠ 0 := fun h => by subst h; simp at hb0
      have hmod : e1 % e2 < e2 := Nat.mod_lt e1 (Nat.pos_of_ne_zero hne)
      exact ih e2 (e1 % e2) (by omega) h2 (pow_mod_step a r e1 e2 hr h1 h2)

private theorem pocklington_prime_factor_dvd_r_sub_1
    {n a q r : Nat} (hn : 1 < n) (hr : IsPrime r) (hrDvdN : r ∣ n)
    (hqPrime : IsPrime q) (hqDvd : q ∣ n - 1)
    (hFermat : a ^ (n - 1) % n = 1)
    (hCoprime : myGcdFuel 256 (a ^ ((n - 1) / q) % n - 1) n = 1) :
    q ∣ r - 1 := by
  have hr1 : 1 < r := hr.1
  have hFermatR : a ^ (n - 1) % r = 1 := by
    rcases hrDvdN with ⟨k, rfl⟩
    have hdiv := (Nat.div_add_mod (a ^ (r * k - 1)) (r * k)).symm
    rw [hFermat] at hdiv
    calc a ^ (r * k - 1) % r
      _ = (r * k * (a ^ (r * k - 1) / (r * k)) + 1) % r := congrArg (· % r) hdiv
      _ = (r * (k * (a ^ (r * k - 1) / (r * k))) + 1) % r := by rw [Nat.mul_assoc]
      _ = 1 % r := Nat.mul_add_mod _ _ _
      _ = 1 := Nat.mod_eq_of_lt hr1
  have hNotDvdA : ¬ (r ∣ a) := by
    intro hda
    have hnp : 0 < n - 1 := by omega
    have hpow0 : a ^ (n - 1) % r = 0 := by
      have hk : n - 1 = (n - 2) + 1 := by omega
      rw [hk, Nat.pow_succ]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hda (Nat.dvd_mul_left a _))
    omega
  have hFlt : a ^ (r - 1) % r = 1 := fermat_little_theorem hr hNotDvdA
  let d := myGcdFuel r (n - 1) (r - 1)
  have hd_n : d ∣ n - 1 := (myGcdFuel_dvd_args r (n - 1) (r - 1) (by omega)).1
  have hd_r : d ∣ r - 1 := (myGcdFuel_dvd_args r (n - 1) (r - 1) (by omega)).2
  have hPowD : a ^ d % r = 1 :=
    pow_mod_myGcdFuel_one a r r (n - 1) (r - 1) hr1 (by omega) hFermatR hFlt
  apply Classical.byContradiction
  intro hnq
  have hdDvdQuot : d ∣ (n - 1) / q := by
    rcases hqDvd with ⟨m, hm⟩
    have hmEq : (n - 1) / q = m := by
      rw [hm, Nat.mul_div_cancel_left m (by have := hqPrime.1; omega)]
    rw [hmEq]
    have hdqm : d ∣ q * m := by rw [← hm]; exact hd_n
    rcases hdqm with ⟨k, hk⟩
    have hqdk : q ∣ d * k := ⟨m, hk.symm⟩
    rcases isPrime_dvd_mul hqPrime hqdk with hqd | hqk
    · exact absurd (Nat.dvd_trans hqd hd_r) hnq
    · rcases hqk with ⟨k', rfl⟩
      refine ⟨k', ?_⟩
      have hqPos : 0 < q := by have := hqPrime.1; omega
      have hmul : q * (d * k') = q * m := by
        calc q * (d * k') = d * (q * k') := by rw [← Nat.mul_assoc, Nat.mul_comm q d, Nat.mul_assoc]
          _ = q * m := hk.symm
      exact (Nat.mul_left_cancel hqPos hmul).symm
  have hPowQuotR : a ^ ((n - 1) / q) % r = 1 := by
    rcases hdDvdQuot with ⟨t, ht⟩
    rw [ht, Nat.pow_mul, Nat.pow_mod, hPowD, Nat.one_pow, Nat.mod_eq_of_lt hr1]
  let x := a ^ ((n - 1) / q) % n
  have hx1 : 1 ≤ x := by
    apply Classical.byContradiction
    intro hx0
    have hxz : x = 0 := by omega
    have hrZero : r ∣ (x - 1) := by change r ∣ (x - 1); rw [hxz]; exact Nat.dvd_zero r
    have hrGcd := myGcdFuel_dvd 256 (x - 1) n r hrZero hrDvdN
    change myGcdFuel 256 (x - 1) n = 1 at hCoprime
    rw [hCoprime] at hrGcd
    have := Nat.le_of_dvd (by omega) hrGcd
    omega
  have hrSub : r ∣ x - 1 := by
    have hmodR : x % r = 1 := by
      rcases hrDvdN with ⟨k, hkN⟩
      have hdiv0 : a ^ ((n - 1) / q) = n * (a ^ ((n - 1) / q) / n) + x := (Nat.div_add_mod _ _).symm
      have hdiv : a ^ ((n - 1) / q) = (r * k) * (a ^ ((n - 1) / q) / n) + x := by
        rw [← hkN]; exact hdiv0
      have hxMod : a ^ ((n - 1) / q) % r = x % r := by
        calc a ^ ((n - 1) / q) % r
          _ = ((r * k) * (a ^ ((n - 1) / q) / n) + x) % r := congrArg (· % r) hdiv
          _ = (r * (k * (a ^ ((n - 1) / q) / n)) + x) % r := by rw [Nat.mul_assoc]
          _ = x % r := Nat.mul_add_mod _ _ _
      rw [← hxMod, hPowQuotR]
    have hdivX := (Nat.div_add_mod x r).symm
    rw [hmodR] at hdivX
    exact ⟨x / r, by omega⟩
  have hrGcd := myGcdFuel_dvd 256 (x - 1) n r hrSub hrDvdN
  change myGcdFuel 256 (x - 1) n = 1 at hCoprime
  rw [hCoprime] at hrGcd
  have := Nat.le_of_dvd (by omega) hrGcd
  omega

theorem pocklington_step_1 (n a q : Nat)
    (hn : 1 < n) (hqPrime : IsPrime q) (hqDvd : q ∣ n - 1)
    (hSq : n < q * q) (hFermat : a ^ (n - 1) % n = 1)
    (hCoprime : myGcdFuel 256 (a ^ ((n - 1) / q) % n - 1) n = 1) :
    IsPrime n := by
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn hnp with ⟨r, hr, hrDvdN, hrSq⟩
  have hqr := pocklington_prime_factor_dvd_r_sub_1 hn hr hrDvdN hqPrime hqDvd hFermat hCoprime
  have hrPos : 1 ≤ r - 1 := by have := hr.1; omega
  have hle : q ≤ r - 1 := Nat.le_of_dvd hrPos hqr
  have hlt : q < r := by omega
  have hqq : q * q < r * r := nat_sq_lt_sq hlt
  omega

theorem pocklington_step_2 (n a q1 q2 : Nat)
    (hn : 1 < n) (hq1Prime : IsPrime q1) (hq2Prime : IsPrime q2) (hqNe : q1 ≠ q2)
    (hq1Dvd : q1 ∣ n - 1) (hq2Dvd : q2 ∣ n - 1)
    (hSq : n < (q1 * q2) * (q1 * q2)) (hFermat : a ^ (n - 1) % n = 1)
    (hCoprime1 : myGcdFuel 256 (a ^ ((n - 1) / q1) % n - 1) n = 1)
    (hCoprime2 : myGcdFuel 256 (a ^ ((n - 1) / q2) % n - 1) n = 1) :
    IsPrime n := by
  apply Classical.byContradiction
  intro hnp
  rcases exists_prime_dvd_sq_le n hn hnp with ⟨r, hr, hrDvdN, hrSq⟩
  have hq1r := pocklington_prime_factor_dvd_r_sub_1 hn hr hrDvdN hq1Prime hq1Dvd hFermat hCoprime1
  have hq2r := pocklington_prime_factor_dvd_r_sub_1 hn hr hrDvdN hq2Prime hq2Dvd hFermat hCoprime2
  have hq12r : q1 * q2 ∣ r - 1 := by
    rcases hq1r with ⟨k, hk⟩
    have hq2Prod : q2 ∣ q1 * k := by rw [← hk]; exact hq2r
    have hq2nq1 : ¬ (q2 ∣ q1) := by
      intro hd
      rcases Classical.em (q2 < q1) with hlt | hge
      · exact hq1Prime.2 q2 hq2Prime.1 hlt hd
      · have := Nat.le_of_dvd (by have := hq1Prime.1; omega) hd
        omega
    rcases isPrime_dvd_mul hq2Prime hq2Prod with hbad | hq2k
    · exact absurd hbad hq2nq1
    · rcases hq2k with ⟨t, rfl⟩
      exact ⟨t, by rw [hk, Nat.mul_assoc]⟩
  have hrPos : 1 ≤ r - 1 := by have := hr.1; omega
  have hle : q1 * q2 ≤ r - 1 := Nat.le_of_dvd hrPos hq12r
  have hlt : q1 * q2 < r := by omega
  have hqq : (q1 * q2) * (q1 * q2) < r * r := nat_sq_lt_sq hlt
  omega

/-! ### 4. Bridge to Anchor.lean's `modPow64` & `modPow128` -/

private theorem mod_pow_mod (base exp m : Nat) : (base % m) ^ exp % m = base ^ exp % m := by
  induction exp with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    calc ((base % m) ^ k * (base % m)) % m
      _ = (((base % m) ^ k % m) * ((base % m) % m)) % m := Nat.mul_mod _ _ _
      _ = ((base ^ k % m) * (base % m)) % m := by rw [ih, Nat.mod_mod]
      _ = (base ^ k * base) % m := (Nat.mul_mod (base ^ k) base m).symm

private theorem modPowSmall_eq (n base m : Nat) :
    modPowSmall n base m = base ^ n % m := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold modPowSmall
    calc (modPowSmall k base m * (base % m)) % m
      _ = ((base ^ k % m) * (base % m)) % m := by rw [ih]
      _ = (base ^ k * base) % m := (Nat.mul_mod (base ^ k) base m).symm
      _ = base ^ (k + 1) % m := by rw [← Nat.pow_succ]

private theorem modPow16Fuel_eq (fuel base exp m : Nat) (hexp : exp < 16 ^ fuel) :
    modPow16Fuel fuel base exp m = base ^ exp % m := by
  induction fuel generalizing exp with
  | zero =>
    have h0 : exp = 0 := by
      have : (16 : Nat) ^ 0 = 1 := rfl
      omega
    subst h0; rfl
  | succ f ih =>
    cases exp with
    | zero => rfl
    | succ e' =>
      have hpow : (16 : Nat) ^ (f + 1) = 16 ^ f * 16 := rfl
      have hdiv : (e' + 1) / 16 < 16 ^ f := by omega
      have hih := ih ((e' + 1) / 16) hdiv
      have hstep : modPow16Fuel (f + 1) base (e' + 1) m =
          let acc := modPow16Fuel f base ((e' + 1) / 16) m
          let a2 := (acc * acc) % m
          let a4 := (a2 * a2) % m
          let a8 := (a4 * a4) % m
          let a16 := (a8 * a8) % m
          (a16 * modPowSmall ((e' + 1) % 16) base m) % m := rfl
      rw [hstep]
      dsimp only
      rw [hih, modPowSmall_eq]
      have ha2 : ((base ^ ((e' + 1) / 16) % m) * (base ^ ((e' + 1) / 16) % m)) % m =
          base ^ (2 * ((e' + 1) / 16)) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add]; congr 2; omega
      have ha4 : ((base ^ (2 * ((e' + 1) / 16)) % m) * (base ^ (2 * ((e' + 1) / 16)) % m)) % m =
          base ^ (4 * ((e' + 1) / 16)) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add]; congr 2; omega
      have ha8 : ((base ^ (4 * ((e' + 1) / 16)) % m) * (base ^ (4 * ((e' + 1) / 16)) % m)) % m =
          base ^ (8 * ((e' + 1) / 16)) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add]; congr 2; omega
      have ha16 : ((base ^ (8 * ((e' + 1) / 16)) % m) * (base ^ (8 * ((e' + 1) / 16)) % m)) % m =
          base ^ (16 * ((e' + 1) / 16)) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add]; congr 2; omega
      rw [ha2, ha4, ha8, ha16, ← Nat.mul_mod, ← Nat.pow_add]
      have hrem : 16 * ((e' + 1) / 16) + (e' + 1) % 16 = e' + 1 := Nat.div_add_mod (e' + 1) 16
      rw [hrem]

theorem modPow64_eq (base exp m : Nat) (hm : 1 < m) (hexp : exp < 16 ^ 18) :
    modPow64 base exp m = base ^ exp % m := by
  cases m with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ m' =>
      have hdef : modPow64 base exp (m' + 2) = modPow16Fuel 18 (base % (m' + 2)) exp (m' + 2) := rfl
      rw [hdef, modPow16Fuel_eq 18 (base % (m' + 2)) exp (m' + 2) hexp, mod_pow_mod]

theorem modPow128_eq (base exp m : Nat) (hm : 1 < m) (hexp : exp < 16 ^ 32) :
    modPow128 base exp m = base ^ exp % m := by
  cases m with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ m' =>
      have hdef : modPow128 base exp (m' + 2) = modPow16Fuel 32 (base % (m' + 2)) exp (m' + 2) := rfl
      rw [hdef, modPow16Fuel_eq 32 (base % (m' + 2)) exp (m' + 2) hexp, mod_pow_mod]

private theorem pock64_step1 (n q : Nat)
    (hn : 1 < n) (hqPrime : IsPrime q) (_hqPos : 0 < q)
    (hMod : (n - 1) % q = 0)
    (hBound : n < 16 ^ 18) (hSq : n < q * q)
    (hF : modPow64 2 (n - 1) n = 1)
    (hC : myGcdFuel 256 (modPow64 2 ((n - 1) / q) n - 1) n = 1) :
    IsPrime n := by
  have h1 : n - 1 < 16 ^ 18 := by omega
  have h2 : (n - 1) / q < 16 ^ 18 := by
    have : (n - 1) / q ≤ n - 1 := Nat.div_le_self _ _
    omega
  rw [modPow64_eq 2 (n - 1) n hn h1] at hF
  rw [modPow64_eq 2 ((n - 1) / q) n hn h2] at hC
  exact pocklington_step_1 n 2 q hn hqPrime (Nat.dvd_of_mod_eq_zero hMod) hSq hF hC

private theorem pock64_step2 (n q1 q2 : Nat)
    (hn : 1 < n) (hq1Prime : IsPrime q1) (hq2Prime : IsPrime q2) (hqNe : q1 ≠ q2)
    (_hq1Pos : 0 < q1) (_hq2Pos : 0 < q2)
    (hMod1 : (n - 1) % q1 = 0) (hMod2 : (n - 1) % q2 = 0)
    (hBound : n < 16 ^ 18) (hSq : n < (q1 * q2) * (q1 * q2))
    (hF : modPow64 2 (n - 1) n = 1)
    (hC1 : myGcdFuel 256 (modPow64 2 ((n - 1) / q1) n - 1) n = 1)
    (hC2 : myGcdFuel 256 (modPow64 2 ((n - 1) / q2) n - 1) n = 1) :
    IsPrime n := by
  have h1 : n - 1 < 16 ^ 18 := by omega
  have h2a : (n - 1) / q1 < 16 ^ 18 := by
    have : (n - 1) / q1 ≤ n - 1 := Nat.div_le_self _ _
    omega
  have h2b : (n - 1) / q2 < 16 ^ 18 := by
    have : (n - 1) / q2 ≤ n - 1 := Nat.div_le_self _ _
    omega
  rw [modPow64_eq 2 (n - 1) n hn h1] at hF
  rw [modPow64_eq 2 ((n - 1) / q1) n hn h2a] at hC1
  rw [modPow64_eq 2 ((n - 1) / q2) n hn h2b] at hC2
  exact pocklington_step_2 n 2 q1 q2 hn hq1Prime hq2Prime hqNe
    (Nat.dvd_of_mod_eq_zero hMod1) (Nat.dvd_of_mod_eq_zero hMod2) hSq hF hC1 hC2

private theorem pock128_step1 (n q : Nat)
    (hn : 1 < n) (hqPrime : IsPrime q) (_hqPos : 0 < q)
    (hMod : (n - 1) % q = 0)
    (hBound : n < 16 ^ 32) (hSq : n < q * q)
    (hF : modPow128 2 (n - 1) n = 1)
    (hC : myGcdFuel 256 (modPow128 2 ((n - 1) / q) n - 1) n = 1) :
    IsPrime n := by
  have h1 : n - 1 < 16 ^ 32 := by omega
  have h2 : (n - 1) / q < 16 ^ 32 := by
    have : (n - 1) / q ≤ n - 1 := Nat.div_le_self _ _
    omega
  rw [modPow128_eq 2 (n - 1) n hn h1] at hF
  rw [modPow128_eq 2 ((n - 1) / q) n hn h2] at hC
  exact pocklington_step_1 n 2 q hn hqPrime (Nat.dvd_of_mod_eq_zero hMod) hSq hF hC

/-! ### 5. Base Primes & Kernel-Checked Pocklington Certificates for `p64` and `p106` -/

section SolinasPrimalityCertificates
set_option maxRecDepth 8192

private theorem prime_7 : IsPrime 7 := isPrime_of_noDivisorBelow 7 (by decide) rfl
private theorem prime_11 : IsPrime 11 := isPrime_of_noDivisorBelow 11 (by decide) rfl
private theorem prime_13 : IsPrime 13 := isPrime_of_noDivisorBelow 13 (by decide) rfl
private theorem prime_71 : IsPrime 71 := isPrime_of_noDivisorBelow 71 (by decide) rfl
private theorem prime_73 : IsPrime 73 := isPrime_of_noDivisorBelow 73 (by decide) rfl

-- p64 chain
private theorem prime_15331 : IsPrime 15331 :=
  pock64_step2 15331 73 7 (by decide) prime_73 prime_7 (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) rfl rfl rfl

private theorem prime_2131 : IsPrime 2131 :=
  pock64_step1 2131 71 (by decide) prime_71 (by decide) rfl (by decide) (by decide) rfl rfl

private theorem prime_5594472617641 : IsPrime 5594472617641 :=
  pock64_step2 5594472617641 15331 2131 (by decide) prime_15331 prime_2131 (by decide)
    (by decide) (by decide) rfl rfl (by decide) (by decide) rfl rfl rfl

/-- Formal Mathlib-free Lean 4 kernel proof that p64 = 2^64 - 59 is prime. -/
theorem p64_is_prime : IsPrime p64 := by
  rw [p64_exact_decimal]
  exact pock64_step1 18446744073709551557 5594472617641 (by decide) prime_5594472617641
    (by decide) rfl (by decide) (by decide) rfl rfl

-- p106 chain
private theorem prime_3433 : IsPrime 3433 :=
  pock64_step2 3433 13 11 (by decide) prime_13 prime_11 (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) rfl rfl rfl

private theorem prime_75527 : IsPrime 75527 :=
  pock64_step1 75527 3433 (by decide) prime_3433 (by decide) rfl (by decide) (by decide) rfl rfl

private theorem prime_2699 : IsPrime 2699 :=
  pock64_step1 2699 71 (by decide) prime_71 (by decide) rfl (by decide) (by decide) rfl rfl

private theorem prime_5399 : IsPrime 5399 :=
  pock64_step1 5399 2699 (by decide) prime_2699 (by decide) rfl (by decide) (by decide) rfl rfl

private theorem prime_43223648939 : IsPrime 43223648939 :=
  pock64_step2 43223648939 75527 5399 (by decide) prime_75527 prime_5399 (by decide)
    (by decide) (by decide) rfl rfl (by decide) (by decide) rfl rfl rfl

private theorem prime_2939208127853 : IsPrime 2939208127853 :=
  pock64_step1 2939208127853 43223648939 (by decide) prime_43223648939 (by decide)
    rfl (by decide) (by decide) rfl rfl

private theorem prime_387975472876597 : IsPrime 387975472876597 :=
  pock64_step1 387975472876597 2939208127853 (by decide) prime_2939208127853 (by decide)
    rfl (by decide) (by decide) rfl rfl

private theorem prime_2132313198929777113 : IsPrime 2132313198929777113 :=
  pock64_step1 2132313198929777113 387975472876597 (by decide) prime_387975472876597 (by decide)
    rfl (by decide) (by decide) rfl rfl

private theorem prime_5212866077423626108151101 : IsPrime 5212866077423626108151101 :=
  pock128_step1 5212866077423626108151101 2132313198929777113 (by decide)
    prime_2132313198929777113 (by decide) rfl (by decide) (by decide) rfl rfl

/-- Formal Mathlib-free Lean 4 kernel proof that p106 = 2^106 - 117 is prime. -/
theorem p106_is_prime : IsPrime p106 := by
  rw [p106_exact_decimal]
  exact pock128_step1 81129638414606681695789005143947 5212866077423626108151101
    (by decide) prime_5212866077423626108151101 (by decide) rfl (by decide) (by decide) rfl rfl

end SolinasPrimalityCertificates

end PuristSiliconCore
