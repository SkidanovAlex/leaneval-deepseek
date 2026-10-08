
import Mathlib
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.polyRep_add
import Submission.Work.Higman.coeff_vanishing_of_scale
import Submission.Work.Higman.bivariate_monomial_indep
import Submission.Work.Higman.bilinear_frob
import Submission.Work.Higman.pow_two_mod_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 1. Frobenius expansion of a two-variable additive map -/

/-- **Frobenius expansion of a biadditive map.**  If `|F| = 2 ^ n` and `B` is additive in each
variable, then `B x y = ∑_{k,l<n} d k l * x ^ (2 ^ k) * y ^ (2 ^ l)`. -/
theorem bilinear_frob_general {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (B : F → F → F)
    (hx : ∀ y x x', B (x + x') y = B x y + B x' y)
    (hy : ∀ x y y', B x (y + y') = B x y + B x y') :
    ∃ d : ℕ → ℕ → F, ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      d k l * x ^ (2 ^ k) * y ^ (2 ^ l) := by
  classical
  let a : ℕ → F → F := fun k y => (polyRep (fun x => B x y)).coeff (2 ^ k)
  have hA : ∀ y x, B x y = ∑ k ∈ Finset.range n, a k y * x ^ (2 ^ k) := by
    intro y x
    exact additive_frob hcard (fun x => B x y) (fun x x' => hx y x x') x
  have ha_add : ∀ k, ∀ y y', a k (y + y') = a k y + a k y' := by
    intro k y y'
    have hp : polyRep (fun x => B x (y + y')) =
        polyRep (fun x => B x y) + polyRep (fun x => B x y') := by
      rw [show (fun x => B x (y + y')) = (fun x => B x y + B x y') from
        funext (fun x => hy x y y')]
      exact polyRep_add (fun x => B x y) (fun x => B x y')
    show (polyRep (fun x => B x (y + y'))).coeff (2 ^ k) =
      (polyRep (fun x => B x y)).coeff (2 ^ k) + (polyRep (fun x => B x y')).coeff (2 ^ k)
    rw [hp, Polynomial.coeff_add]
  refine ⟨fun k l => (polyRep (a k)).coeff (2 ^ l), ?_⟩
  intro x y
  rw [hA y x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [additive_frob hcard (a k) (ha_add k) y, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **The coefficient constraint.**  If `B` has Frobenius expansion `d` and satisfies the
equivariance `B (λ₁x) (λ₂y) = γ * B x y`, then every coefficient satisfies
`d k l * (λ₁ ^ (2 ^ k) * λ₂ ^ (2 ^ l) - γ) = 0`. -/
theorem bilinear_frob_general_constraint {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (B : F → F → F) (d : ℕ → ℕ → F)
    (hexp : ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
    (las1 las2 gam : F) (heq : ∀ x y, B (las1 * x) (las2 * y) = gam * B x y) :
    ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n,
      d k l * (las1 ^ (2 ^ k) * las2 ^ (2 ^ l) - gam) = 0 := by
  classical
  have hsum : ∀ x y, (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (d k l * (las1 ^ (2 ^ k) * las2 ^ (2 ^ l) - gam)) * x ^ (2 ^ k) * y ^ (2 ^ l))
      = B (las1 * x) (las2 * y) - gam * B x y := by
    intro x y
    rw [hexp (las1 * x) (las2 * y), hexp x y, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_pow, mul_pow, mul_assoc]
    ring
  refine bivariate_monomial_indep hcard
    (fun k l => d k l * (las1 ^ (2 ^ k) * las2 ^ (2 ^ l) - gam)) (fun x y => ?_)
  rw [hsum x y, heq x y, sub_self]

/-! ## 2. Arithmetic -/

/-- Two numbers in `[1, 2 ^ n]` that are congruent modulo `2 ^ n - 1` are either equal, or one is
`1` and the other `2 ^ n`. -/
theorem eq_or_eq_one_of_modEq {n A B : ℕ} (hA : 1 ≤ A) (hA' : A ≤ 2 ^ n) (hB : 1 ≤ B)
    (hB' : B ≤ 2 ^ n) (hAB : A ≡ B [MOD 2 ^ n - 1]) :
    A = B ∨ (A = 1 ∧ B = 2 ^ n) ∨ (A = 2 ^ n ∧ B = 1) := by
  rcases le_total A B with hle | hle
  · have hdvd : 2 ^ n - 1 ∣ B - A := (Nat.modEq_iff_dvd' hle).mp hAB
    rcases Nat.eq_zero_or_pos (B - A) with h0 | hpos
    · left; omega
    · right; left
      have h1 : 2 ^ n - 1 ≤ B - A := Nat.le_of_dvd hpos hdvd
      have h2 : B - A ≤ 2 ^ n - 1 := by omega
      constructor <;> omega
  · have hdvd : 2 ^ n - 1 ∣ A - B := (Nat.modEq_iff_dvd' hle).mp hAB.symm
    rcases Nat.eq_zero_or_pos (A - B) with h0 | hpos
    · left; omega
    · right; right
      have h1 : 2 ^ n - 1 ≤ A - B := Nat.le_of_dvd hpos hdvd
      have h2 : A - B ≤ 2 ^ n - 1 := by omega
      constructor <;> omega

/-- For `i < j < n` and `2 ≤ n` one has `2 ^ i + 2 ^ j < 2 ^ n`. -/
theorem two_pow_sum_lt_two_pow {n i j : ℕ} (hn : 2 ≤ n) (hij : i < j) (hjn : j < n) :
    2 ^ i + 2 ^ j < 2 ^ n := by
  have hi : i ≤ n - 2 := by omega
  have hj : j ≤ n - 1 := by omega
  have h1 : 2 ^ i ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) hi
  have h2 : 2 ^ j ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hj
  have h3 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have h4 : 2 ^ n = 2 ^ (n - 2) * 4 := by
    rw [show n = (n - 2) + 2 by omega, pow_add]; norm_num
  rw [h4]
  have hpos : 0 < 2 ^ (n - 2) := pow_pos (by norm_num) _
  have h5 : 2 ^ i + 2 ^ j ≤ 2 ^ (n - 2) + 2 ^ (n - 2) * 2 := by linarith
  nlinarith [h5, hpos]

/-- `2 ^ i + 2 ^ j` (`i < j`) is not a power of two. -/
theorem two_pow_add_ne_two_pow {i j m : ℕ} (hij : i < j) (h : 2 ^ m = 2 ^ i + 2 ^ j) : False := by
  have hji : 1 ≤ j - i := by omega
  have him : i < m := by
    by_contra hcon
    have hcon' : m ≤ i := by omega
    have h1 : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hcon'
    have h2 : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have h3 : 2 ^ i + 1 ≤ 2 ^ m := by omega
    omega
  have hsplit : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by
    rw [← pow_add]; congr 1; omega
  have hmi : 2 ^ m = 2 ^ i * 2 ^ (m - i) := by
    rw [← pow_add]; congr 1; omega
  have hkey : 2 ^ (m - i) = 1 + 2 ^ (j - i) := by
    have h2 : 2 ^ i * 2 ^ (m - i) = 2 ^ i * (1 + 2 ^ (j - i)) := by
      rw [← hmi, h, hsplit]; ring
    exact Nat.mul_left_cancel (pow_pos (by norm_num) i) h2
  have hdvd : 2 ∣ 2 ^ (m - i) := dvd_pow_self 2 (by omega)
  rw [hkey] at hdvd
  exact not_two_dvd_one_add_two_pow hji hdvd

/-- A sum of two powers of two with exponents `< n` is not congruent to a single power of two
modulo `2 ^ n - 1`. -/
theorem pow_ne_two_pow_sum {n i j m : ℕ} (hn : 2 ≤ n) (hij : i < j) (hjn : j < n) (hm : m < n)
    (h : 2 ^ m ≡ 2 ^ i + 2 ^ j [MOD 2 ^ n - 1]) : False := by
  have hA : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hA' : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (le_of_lt hm)
  have hB : 1 ≤ 2 ^ i + 2 ^ j := by
    have h1 : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
    exact le_trans h1 (Nat.le_add_right _ _)
  have hlt := two_pow_sum_lt_two_pow hn hij hjn
  have hB' : 2 ^ i + 2 ^ j ≤ 2 ^ n := le_of_lt hlt
  rcases eq_or_eq_one_of_modEq hA hA' hB hB' h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact two_pow_add_ne_two_pow hij h1
  · exact absurd h2 (ne_of_lt hlt)
  · exact absurd h1 (ne_of_lt (Nat.pow_lt_pow_right (by norm_num) hm))

/-- **Arithmetic core, sign-flipped form.**  Let `2 ≤ n`, `t = 2 ^ i + 2 ^ j` with `i < j < n`.
Then `2 ^ r + t * (2 ^ s - 1) ≡ 0 [MOD 2 ^ n - 1]` has at most one solution `(r,s)` with
`r, s < n` and `s ≠ 0`. -/
theorem pow_two_mod_unique_neg (n i j r s r' s' : ℕ) (h2 : 2 ≤ n) (hij : i < j) (hjn : j < n)
    (hr : r < n) (hs : s < n) (hr' : r' < n) (hs' : s' < n) (hs0 : s ≠ 0) (hs0' : s' ≠ 0)
    (h1 : 2 ^ r + (2 ^ i + 2 ^ j) * (2 ^ s - 1) ≡ 0 [MOD 2 ^ n - 1])
    (h2' : 2 ^ r' + (2 ^ i + 2 ^ j) * (2 ^ s' - 1) ≡ 0 [MOD 2 ^ n - 1]) :
    r = r' ∧ s = s' := by
  set N := 2 ^ n - 1 with hNdef
  set t := 2 ^ i + 2 ^ j with htdef
  have hn : 1 ≤ n := by omega
  have hN3 : 3 ≤ N := by
    have h : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hpowN : (2 : ℕ) ^ n % N = 1 := by
    have hN1 : 2 ^ n = N + 1 := by omega
    rw [hN1, Nat.add_comm, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : ∀ x : ℕ, 2 ^ x ≡ 2 ^ (x % n) [MOD N] := by
    intro x
    have hx : (x / n) * n + x % n = x := by
      rw [mul_comm]; exact Nat.div_add_mod x n
    have hN1' : (2 : ℕ) ^ n ≡ 1 [MOD N] := by
      rw [Nat.ModEq, hpowN, Nat.mod_eq_of_lt (by omega : 1 < N)]
    calc 2 ^ x = 2 ^ ((x / n) * n + x % n) := by rw [hx]
      _ = (2 ^ n) ^ (x / n) * 2 ^ (x % n) := by rw [pow_add, mul_comm (x / n) n, ← pow_mul]
      _ ≡ 1 ^ (x / n) * 2 ^ (x % n) [MOD N] := Nat.ModEq.mul (hN1'.pow _) (Nat.ModEq.refl _)
      _ = 2 ^ (x % n) := by simp
  have hmul1 : 2 ^ r * (2 ^ s' - 1) + t * (2 ^ s - 1) * (2 ^ s' - 1) ≡ 0 [MOD N] := by
    have h := h1.mul (Nat.ModEq.refl (2 ^ s' - 1))
    simpa [mul_add, add_mul, mul_assoc] using h
  have hmul2 : 2 ^ r' * (2 ^ s - 1) + t * (2 ^ s - 1) * (2 ^ s' - 1) ≡ 0 [MOD N] := by
    have h := h2'.mul (Nat.ModEq.refl (2 ^ s - 1))
    have hsw : t * (2 ^ s' - 1) * (2 ^ s - 1) = t * (2 ^ s - 1) * (2 ^ s' - 1) := by ring
    simpa [mul_add, add_mul, mul_assoc, hsw] using h
  have hkey : 2 ^ r * (2 ^ s' - 1) ≡ 2 ^ r' * (2 ^ s - 1) [MOD N] := by
    have h3 : 2 ^ r * (2 ^ s' - 1) + t * (2 ^ s - 1) * (2 ^ s' - 1) ≡
        2 ^ r' * (2 ^ s - 1) + t * (2 ^ s - 1) * (2 ^ s' - 1) [MOD N] :=
      hmul1.trans hmul2.symm
    exact Nat.ModEq.add_right_cancel' _ h3
  have e1 : 2 ^ r * (2 ^ s' - 1) = 2 ^ (r + s') - 2 ^ r := by
    have h : 1 ≤ 2 ^ s' := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.mul_sub_left_distrib, mul_one, pow_add]
  have e2 : 2 ^ r' * (2 ^ s - 1) = 2 ^ (r' + s) - 2 ^ r' := by
    have h : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.mul_sub_left_distrib, mul_one, pow_add]
  rw [e1, e2] at hkey
  have hkey2 : 2 ^ (r + s') - 2 ^ r + (2 ^ r + 2 ^ r') ≡
      2 ^ (r' + s) - 2 ^ r' + (2 ^ r + 2 ^ r') [MOD N] :=
    hkey.add (Nat.ModEq.refl _)
  have s1 : 2 ^ (r + s') - 2 ^ r + (2 ^ r + 2 ^ r') = 2 ^ (r + s') + 2 ^ r' := by
    have hle : 2 ^ r ≤ 2 ^ (r + s') := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have s2 : 2 ^ (r' + s) - 2 ^ r' + (2 ^ r + 2 ^ r') = 2 ^ (r' + s) + 2 ^ r := by
    have hle : 2 ^ r' ≤ 2 ^ (r' + s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [s1, s2] at hkey2
  have hred : 2 ^ ((r + s') % n) + 2 ^ r' ≡ 2 ^ ((r' + s) % n) + 2 ^ r [MOD N] := by
    have a1 := (hmod (r + s')).add (Nat.ModEq.refl (2 ^ r'))
    have a2 := (hmod (r' + s)).add (Nat.ModEq.refl (2 ^ r))
    exact a1.symm.trans (hkey2.trans a2)
  rcases two_pow_sum_modEq (Nat.mod_lt _ (by omega)) hr' (Nat.mod_lt _ (by omega)) hr hred with
    ⟨ha1, hr'e⟩ | ⟨ha1, hr'e⟩
  · subst hr'e
    refine ⟨rfl, ?_⟩
    have hmod' : (r' + s') % n = (r' + s) % n := ha1
    have hm : r' + s' ≡ r' + s [MOD n] := hmod'
    have hss : s' ≡ s [MOD n] := Nat.ModEq.add_left_cancel (Nat.ModEq.refl r') hm
    exact (hss.eq_of_lt_of_lt hs' hs).symm
  · exfalso
    have hz : (r' + s) % n = (r' + 0) % n := by
      rw [Nat.add_zero, ← hr'e]
      exact (Nat.mod_eq_of_lt hr').symm
    have hss : s ≡ 0 [MOD n] := Nat.ModEq.add_left_cancel (Nat.ModEq.refl r') hz
    exact hs0 (hss.eq_of_lt_of_lt hs (by omega))

/-! ## 3. `λ ^ A = λ ^ B` forces a congruence -/

theorem modEq_of_pow_eq_pow {x : F} {N A B : ℕ} (hx0 : x ≠ 0) (hN : orderOf x = N)
    (h : x ^ A = x ^ B) : A ≡ B [MOD N] := by
  rcases le_total A B with hle | hle
  · have h1 : x ^ (B - A) = 1 := by
      have h2 : x ^ A * x ^ (B - A) = x ^ A * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hle, h]
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
    have h3 : orderOf x ∣ B - A := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hN] at h3
    exact (Nat.modEq_iff_dvd' hle).mpr h3
  · have h1 : x ^ (A - B) = 1 := by
      have h2 : x ^ B * x ^ (A - B) = x ^ B * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hle, ← h]
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
    have h3 : orderOf x ∣ A - B := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hN] at h3
    exact ((Nat.modEq_iff_dvd' hle).mpr h3).symm

/-! ## 4. The core -/

/-- **The finite-field core of the `C₄` exclusion** (see the module docstring). -/
theorem c4_field_core (n : ℕ) (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n) (lam mu : F)
    (hlam : lam ≠ 0) (hmu : mu ≠ 0) (hlamu : lam ≠ mu)
    (hordlam : orderOf lam = 2 ^ n - 1) (hordmu : orderOf mu = 2 ^ n - 1)
    (beta : F → F → F) (f : F → F) (B : F → F → F)
    (hbeta1 : ∀ a b d : F, beta (a + b) d = beta a d + beta b d)
    (hbeta2 : ∀ a b d : F, beta a (b + d) = beta a b + beta a d)
    (hbetaeq : ∀ a b : F, beta (lam * a) (lam * b) = mu * beta a b)
    (hbetaalt : ∀ a : F, beta a a = 0)
    (hbetane : ∃ a b : F, beta a b ≠ 0)
    (hfinj : ∀ a : F, f a = 0 → a = 0)
    (hB1 : ∀ a b d : F, B (a + b) d = B a d + B b d)
    (hB2 : ∀ a b d : F, B a (b + d) = B a b + B a d)
    (hBeq : ∀ a b : F, B (lam * a) (mu * b) = mu * B a b)
    (hBne : ∃ a b : F, B a b ≠ 0)
    (hBquad : ∀ a : F, B a (f a) = 0) :
    False := by
  classical
  have htwo : (2 : F) = 0 := by
    have h := (CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl 2)
    simpa using h
  have hadd : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, htwo, zero_mul]
  -- ## β is symmetric
  have hbetasym : ∀ x y, beta x y = beta y x := by
    intro x y
    have h := hbetaalt (x + y)
    rw [hbeta1 x y (x + y)] at h
    rw [hbeta2 x x y, hbeta2 y x y, hbetaalt x, hbetaalt y] at h
    simp only [zero_add, add_zero] at h
    have hu : beta x y + beta x y = 0 := hadd _
    calc beta x y = beta x y + (beta x y + beta y x) := by rw [h, add_zero]
      _ = (beta x y + beta x y) + beta y x := by abel
      _ = 0 + beta y x := by rw [hu]
      _ = beta y x := zero_add _
  -- ## the Frobenius expansion of β and its coefficient constraint
  obtain ⟨bd, hbdsym, hbddiag, hbdexp⟩ :=
    bilinear_frob hcard beta (fun y x x' => hbeta1 x x' y) (fun x y y' => hbeta2 x y y')
      hbetasym hbetaalt
  have hbdc : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n,
      bd k l * (lam ^ (2 ^ k + 2 ^ l) - mu) = 0 := by
    intro k hk l hl
    have h := bilinear_frob_general_constraint hcard beta bd hbdexp lam lam mu hbetaeq k hk l hl
    rwa [← pow_add] at h
  -- ## a non-zero coefficient of β, giving the exponent relation `mu = lam ^ t`
  have hex : ∃ k l, k ∈ Finset.range n ∧ l ∈ Finset.range n ∧ bd k l ≠ 0 := by
    by_contra hcon
    obtain ⟨a, b, hab⟩ := hbetane
    refine hab ?_
    rw [hbdexp a b]
    refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl => ?_))
    by_contra hkl
    exact hcon ⟨k, l, hk, hl, fun h0 => hkl (by rw [h0]; ring)⟩
  obtain ⟨k0, l0, hk0n, hl0n, hk0ne⟩ := hex
  have hk0lt : k0 < n := Finset.mem_range.mp hk0n
  have hl0lt : l0 < n := Finset.mem_range.mp hl0n
  have hlamt : lam ^ (2 ^ k0 + 2 ^ l0) = mu := by
    rcases mul_eq_zero.mp (hbdc k0 hk0n l0 hl0n) with h1 | h1
    · exact absurd h1 hk0ne
    · exact sub_eq_zero.mp h1
  have hk0l0 : k0 ≠ l0 := by
    intro h
    rw [← h] at hk0ne
    exact hk0ne (hbddiag k0)
  -- ## the Frobenius expansion of `B` and its coefficient constraint
  obtain ⟨d, hdexp⟩ := bilinear_frob_general hcard B (fun y x x' => hB1 x x' y)
    (fun x y y' => hB2 x y y')
  have hdc : ∀ r ∈ Finset.range n, ∀ s ∈ Finset.range n,
      d r s * (lam ^ (2 ^ r) * mu ^ (2 ^ s) - mu) = 0 :=
    bilinear_frob_general_constraint hcard B d hdexp lam mu mu hBeq
  have hexB : ∃ r s, r ∈ Finset.range n ∧ s ∈ Finset.range n ∧ d r s ≠ 0 := by
    by_contra hcon
    obtain ⟨a, b, hab⟩ := hBne
    refine hab ?_
    rw [hdexp a b]
    refine Finset.sum_eq_zero (fun r hr => Finset.sum_eq_zero (fun s hs => ?_))
    by_contra hrs
    exact hcon ⟨r, s, hr, hs, fun h0 => hrs (by rw [h0]; ring)⟩
  -- ## the congruence satisfied by the support of `B`
  have hdcong : ∀ r s, r < n → s < n → d r s ≠ 0 →
      2 ^ r + (2 ^ k0 + 2 ^ l0) * (2 ^ s - 1) ≡ 0 [MOD 2 ^ n - 1] := by
    intro r s hr hs hdrs
    have h1 : lam ^ (2 ^ r) * mu ^ (2 ^ s) = mu := by
      rcases mul_eq_zero.mp (hdc r (Finset.mem_range.mpr hr) s (Finset.mem_range.mpr hs))
        with h2 | h2
      · exact absurd h2 hdrs
      · exact sub_eq_zero.mp h2
    have h2 : mu ^ (2 ^ s) = lam ^ ((2 ^ k0 + 2 ^ l0) * 2 ^ s) := by
      rw [← hlamt, pow_mul]
    have h3 : lam ^ (2 ^ r + (2 ^ k0 + 2 ^ l0) * 2 ^ s) = lam ^ (2 ^ k0 + 2 ^ l0) := by
      rw [pow_add, ← h2, h1, hlamt]
    have h5 := modEq_of_pow_eq_pow hlam hordlam h3
    have h6 : (2 ^ k0 + 2 ^ l0) * 2 ^ s = (2 ^ k0 + 2 ^ l0) * (2 ^ s - 1) + (2 ^ k0 + 2 ^ l0) := by
      have h7 : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by norm_num)
      have h8 : (2 ^ k0 + 2 ^ l0) * (2 ^ s - 1) + (2 ^ k0 + 2 ^ l0)
          = (2 ^ k0 + 2 ^ l0) * ((2 ^ s - 1) + 1) := by rw [Nat.mul_add, mul_one]
      rw [h8, Nat.sub_add_cancel h7]
    have h8 : 2 ^ r + ((2 ^ k0 + 2 ^ l0) * (2 ^ s - 1) + (2 ^ k0 + 2 ^ l0))
        = (2 ^ r + (2 ^ k0 + 2 ^ l0) * (2 ^ s - 1)) + (2 ^ k0 + 2 ^ l0) := by ring
    rw [h6, h8] at h5
    have h9 : (2 ^ r + (2 ^ k0 + 2 ^ l0) * (2 ^ s - 1)) + (2 ^ k0 + 2 ^ l0)
        ≡ 0 + (2 ^ k0 + 2 ^ l0) [MOD 2 ^ n - 1] := by simpa using h5
    exact Nat.ModEq.add_right_cancel' (2 ^ k0 + 2 ^ l0) h9
  -- ## `s ≠ 0` for the support of `B`
  have hdsne : ∀ r s, r < n → s < n → d r s ≠ 0 → s ≠ 0 := by
    intro r s hr hs hdrs h0
    have h1 := hdcong r s hr hs hdrs
    rw [h0, pow_zero, Nat.sub_self, mul_zero, add_zero] at h1
    have h2 : 2 ^ n - 1 ∣ 2 ^ r := Nat.dvd_of_mod_eq_zero (by rw [h1, Nat.zero_mod])
    have hodd : Odd (2 ^ n - 1) := by
      have hn1 : 1 ≤ n := by omega
      refine ⟨2 ^ (n - 1) - 1, ?_⟩
      have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn1]
      have h4 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
    have hcop : (2 ^ n - 1).Coprime (2 ^ r) := (Nat.coprime_two_right.mpr hodd).pow_right r
    have hdvd1 : 2 ^ n - 1 ∣ 1 := hcop.dvd_of_dvd_mul_left (by simpa using h2)
    have hle1 : 2 ^ n - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd1
    have h3 : 3 ≤ 2 ^ n - 1 := by
      have h5 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    omega
  -- ## uniqueness: `B` has a single non-zero coefficient
  have huniq : ∀ r s r' s', r < n → s < n → r' < n → s' < n → d r s ≠ 0 → d r' s' ≠ 0 →
      r = r' ∧ s = s' := by
    intro r s r' s' hr hs hr' hs' h1 h2'
    rcases lt_or_gt_of_ne hk0l0 with hlt | hlt
    · exact pow_two_mod_unique_neg n k0 l0 r s r' s' hn hlt hl0lt hr hs hr' hs'
        (hdsne r s hr hs h1) (hdsne r' s' hr' hs' h2') (hdcong r s hr hs h1)
        (hdcong r' s' hr' hs' h2')
    · have h3 := hdcong r s hr hs h1
      rw [add_comm (2 ^ k0) (2 ^ l0)] at h3
      have h4 := hdcong r' s' hr' hs' h2'
      rw [add_comm (2 ^ k0) (2 ^ l0)] at h4
      exact pow_two_mod_unique_neg n l0 k0 r s r' s' hn hlt hk0lt hr hs hr' hs'
        (hdsne r s hr hs h1) (hdsne r' s' hr' hs' h2') h3 h4
  obtain ⟨r0, s0, hr0n, hs0n, hr0s0⟩ := hexB
  have hzero : ∀ r s, r < n → s < n → (r, s) ≠ (r0, s0) → d r s = 0 := by
    intro r s hr hs hne
    by_contra h0
    have h := huniq r s r0 s0 hr hs (Finset.mem_range.mp hr0n) (Finset.mem_range.mp hs0n)
      h0 hr0s0
    exact hne (Prod.ext h.1 h.2)
  have hB_eq : ∀ x y : F, B x y = d r0 s0 * x ^ (2 ^ r0) * y ^ (2 ^ s0) := by
    intro x y
    rw [hdexp x y]
    have h1 : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
        = ∑ l ∈ Finset.range n, d r0 l * x ^ (2 ^ r0) * y ^ (2 ^ l) :=
      Finset.sum_eq_single r0 (fun k hk hkne => by
        refine Finset.sum_eq_zero (fun l hl => ?_)
        rw [hzero k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)
          (fun h => hkne (congrArg Prod.fst h))]
        ring) (fun hnot => absurd hr0n hnot)
    rw [h1]
    rw [Finset.sum_eq_single s0 (fun l hl hlne => by
        rw [hzero r0 l (Finset.mem_range.mp hr0n) (Finset.mem_range.mp hl)
          (fun h => hlne (congrArg Prod.snd h))]
        ring) (fun hnot => absurd hs0n hnot)]
  -- ## the contradiction
  have hfinal := hBquad 1
  rw [hB_eq 1 (f 1)] at hfinal
  have hf1 : f 1 ≠ 0 := fun h => one_ne_zero (hfinj 1 h)
  have hne : d r0 s0 * (1 : F) ^ (2 ^ r0) * (f 1) ^ (2 ^ s0) ≠ 0 := by
    rw [one_pow, mul_one]
    exact mul_ne_zero hr0s0 (pow_ne_zero _ hf1)
  exact hne hfinal

end Work.Higman
