import Mathlib

open Filter
open scoped Topology

namespace Work.ZeroFreeTables.XY.PrincipalSigma

open Complex

/-!
# Bounds for the Euler factors of the principal character mod `q`

For a prime `p ≥ 2` and `s : ℂ` with `1 ≤ s.re` we have `‖p ^ s‖ = p ^ s.re ≥ p ≥ 2`, hence
`‖p ^ s - 1‖ ≥ p ^ s.re / 2`.  This makes the Euler factors

`f_p(z) = log p / (p ^ z - 1)`

as well as their first two derivatives small:

* `‖f_p(s)‖ ≤ 2 log p / p`,
* `‖f_p'(s)‖ ≤ 4 (log p)^2 / p`,
* `‖f_p''(s)‖ ≤ 16 (log p)^3 / p`.

Summing over the prime divisors of `q` (and using the subadditivity of the norm and the rule
for iterated derivatives of finite sums) yields `EulerFactorBounds`.
-/

/-! ### Elementary facts about `p ^ z` -/

theorem efb_norm_prime_cpow (p : ℕ) (hp : 1 ≤ p) (z : ℂ) :
    ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp))]

theorem efb_two_le_rpow {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 1 ≤ z.re) :
    (2 : ℝ) ≤ (p : ℝ) ^ z.re := by
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp)
  have h2 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ z.re := Real.rpow_le_rpow_of_exponent_le h1 hz
  rw [Real.rpow_one] at h2
  have h3 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

theorem efb_le_rpow {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 1 ≤ z.re) :
    (p : ℝ) ≤ (p : ℝ) ^ z.re := by
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp)
  have h2 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ z.re := Real.rpow_le_rpow_of_exponent_le h1 hz
  rwa [Real.rpow_one] at h2

theorem efb_denom {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 1 ≤ z.re) :
    ((p : ℝ) ^ z.re) / 2 ≤ ‖(p : ℂ) ^ z - 1‖ := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hx : ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := efb_norm_prime_cpow p hp1 z
  have h2 : (2 : ℝ) ≤ (p : ℝ) ^ z.re := efb_two_le_rpow hp hz
  have h3 : ‖(p : ℂ) ^ z‖ - ‖(1 : ℂ)‖ ≤ ‖(p : ℂ) ^ z - 1‖ := norm_sub_norm_le _ _
  simp only [norm_one] at h3
  rw [hx] at h3
  linarith

/-- All the elementary estimates for the size of `p ^ z - 1` in one package. -/
lemma efb_facts {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    (2 ≤ (p : ℝ) ^ s.re ∧ (p : ℝ) ≤ (p : ℝ) ^ s.re ∧
      (p : ℝ) ^ s.re / 2 ≤ ‖(p : ℂ) ^ s - 1‖ ∧
      ‖(p : ℂ) ^ s‖ = (p : ℝ) ^ s.re ∧ (0 : ℝ) < (p : ℝ) ∧ 0 ≤ Real.log (p : ℝ)) :=
  ⟨efb_two_le_rpow hp hs, efb_le_rpow hp hs, efb_denom hp hs,
    efb_norm_prime_cpow p (le_trans (by norm_num) hp) s,
    by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp),
    Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hp))⟩

/-! ### The arithmetic core of the three estimates -/

lemma efb_abs_value {L X D p : ℝ} (hL : 0 ≤ L) (hX : 2 ≤ X) (hpX : p ≤ X) (hp : 2 ≤ p)
    (hD : X / 2 ≤ D) : L / D ≤ 2 * L / p := by
  have h1 : L / D ≤ L / (X / 2) := div_le_div_of_nonneg_left hL (by linarith) hD
  have h2 : L / (X / 2) = 2 * L / X := by field_simp
  have h3 : 2 * L / X ≤ 2 * L / p := div_le_div_of_nonneg_left (by linarith) (by linarith) hpX
  linarith

lemma efb_abs_deriv {L X D p : ℝ} (hL : 0 ≤ L) (hX : 2 ≤ X) (hpX : p ≤ X) (hp : 2 ≤ p)
    (hD : X / 2 ≤ D) : L ^ 2 * X / D ^ 2 ≤ 4 * L ^ 2 / p := by
  have hXpos : 0 < X := by linarith
  have hLXnn : (0 : ℝ) ≤ L ^ 2 * X := mul_nonneg (pow_nonneg hL 2) (by linarith)
  have hq : (0 : ℝ) < (X / 2) ^ 2 := pow_pos (by linarith) 2
  have hD2 : (X / 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by linarith) hD 2
  have h1 : L ^ 2 * X / D ^ 2 ≤ L ^ 2 * X / (X / 2) ^ 2 :=
    div_le_div_of_nonneg_left hLXnn hq hD2
  have h2 : L ^ 2 * X / (X / 2) ^ 2 = 4 * L ^ 2 / X := by field_simp; ring
  have h3 : 4 * L ^ 2 / X ≤ 4 * L ^ 2 / p :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hpX
  linarith

lemma efb_abs_deriv2 {L X D W p : ℝ} (hL : 0 ≤ L) (hX : 2 ≤ X) (hpX : p ≤ X) (hp : 2 ≤ p)
    (hD : X / 2 ≤ D) (hW0 : 0 ≤ W) (hW : W ≤ X + 1) :
    L ^ 3 * X * W / D ^ 3 ≤ 16 * L ^ 3 / p := by
  have hXpos : 0 < X := by linarith
  have hXnn : (0 : ℝ) ≤ X := by linarith
  have hL3nn : (0 : ℝ) ≤ L ^ 3 := pow_nonneg hL 3
  have hLXW : (0 : ℝ) ≤ L ^ 3 * X * W := mul_nonneg (mul_nonneg hL3nn hXnn) hW0
  have hD3 : (X / 2) ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ (by linarith) hD 3
  have h0 : L ^ 3 * X * W / D ^ 3 ≤ L ^ 3 * X * W / (X / 2) ^ 3 :=
    div_le_div_of_nonneg_left hLXW (pow_pos (by linarith) 3) hD3
  have hnum : L ^ 3 * X * W ≤ L ^ 3 * X * (X + 1) :=
    mul_le_mul_of_nonneg_left hW (mul_nonneg hL3nn hXnn)
  have h1 : L ^ 3 * X * W / (X / 2) ^ 3 ≤ L ^ 3 * X * (X + 1) / (X / 2) ^ 3 :=
    div_le_div_of_nonneg_right hnum (pow_nonneg (by linarith) 3)
  have h2 : L ^ 3 * X * (X + 1) / (X / 2) ^ 3 = 8 * L ^ 3 * ((X + 1) / X ^ 2) := by
    field_simp; ring
  have key : (X + 1) / X ^ 2 ≤ 2 / X := by
    rw [div_le_div_iff₀ (by positivity) hXpos]
    nlinarith
  have h3 : 8 * L ^ 3 * ((X + 1) / X ^ 2) ≤ 8 * L ^ 3 * (2 / X) :=
    mul_le_mul_of_nonneg_left key (by positivity)
  have h4 : 8 * L ^ 3 * (2 / X) = 16 * L ^ 3 / X := by field_simp; ring
  have h5 : 16 * L ^ 3 / X ≤ 16 * L ^ 3 / p :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hpX
  linarith

/-! ### The two derivative expressions -/

noncomputable def efbD1 (p : ℕ) (z : ℂ) : ℂ :=
  -(((Real.log (p : ℝ) : ℂ)) ^ 2) * (p : ℂ) ^ z / ((p : ℂ) ^ z - 1) ^ 2

noncomputable def efbD2 (p : ℕ) (z : ℂ) : ℂ :=
  ((((Real.log (p : ℝ) : ℂ)) ^ 3) * (p : ℂ) ^ z * ((p : ℂ) ^ z + 1) / ((p : ℂ) ^ z - 1) ^ 3)

/-! ### Analyticity and the first two derivatives of one Euler factor -/

theorem EulerFactorContDiff (p : ℕ) (hp : p ≠ 0) (s : ℂ) (hs : (p : ℂ) ^ s ≠ 1) (n : ℕ) :
    ContDiffAt ℂ n (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hfun : ∀ z : ℂ, (p : ℂ) ^ z = Complex.exp (Complex.log (p : ℂ) * z) :=
    fun z => Complex.cpow_def_of_ne_zero hpC z
  simp only [hfun]
  have hlin : ContDiff ℂ n (fun z : ℂ => Complex.log (p : ℂ) * z) :=
    contDiff_const.mul contDiff_id
  have h1 : ContDiffAt ℂ n (fun z : ℂ => Complex.exp (Complex.log (p : ℂ) * z)) s :=
    (Complex.contDiff_exp.comp hlin).contDiffAt
  have h2 : ContDiffAt ℂ n (fun z : ℂ => Complex.exp (Complex.log (p : ℂ) * z) - 1) s :=
    h1.sub contDiffAt_const
  have hne : Complex.exp (Complex.log (p : ℂ) * s) - 1 ≠ 0 := by
    rw [← hfun s]; exact sub_ne_zero.mpr hs
  have hc : ContDiffAt ℂ n (fun _ : ℂ => (Real.log (p : ℝ) : ℂ)) s := contDiffAt_const
  exact hc.div h2 hne

theorem EulerFactorDeriv (p : ℕ) (hp : p ≠ 0) (z : ℂ) (hz : (p : ℂ) ^ z ≠ 1) :
    deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) z = efbD1 p z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (by positivity)).symm
  have hpw : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * Complex.log (p : ℂ)) z := by
    have h := HasDerivAt.const_cpow (hasDerivAt_id z) (Or.inl hpC)
    simpa [mul_one] using h
  have hden : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w - 1) ((p : ℂ) ^ z * Complex.log (p : ℂ)) z :=
    hpw.sub_const 1
  have hquot := (hasDerivAt_const z ((Real.log (p : ℝ) : ℂ))).div hden (sub_ne_zero.mpr hz)
  have hfun_eq : (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))
      = ((fun _ : ℂ => (Real.log (p : ℝ) : ℂ)) / (fun w : ℂ => (p : ℂ) ^ w - 1)) := by
    funext w
    rfl
  rw [hfun_eq, hquot.deriv, hlog, efbD1]
  ring

theorem EulerFactorDerivTwo (p : ℕ) (hp : p ≠ 0) (z : ℂ) (hz : (p : ℂ) ^ z ≠ 1) :
    deriv (fun w : ℂ => efbD1 p w) z = efbD2 p z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (by positivity)).symm
  have hz' : (p : ℂ) ^ z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpw : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * Complex.log (p : ℂ)) z := by
    have h := HasDerivAt.const_cpow (hasDerivAt_id z) (Or.inl hpC)
    simpa [mul_one] using h
  have hnum : HasDerivAt (fun w : ℂ => -(((Real.log (p : ℝ) : ℂ)) ^ 2) * (p : ℂ) ^ w)
      (-(((Real.log (p : ℝ) : ℂ)) ^ 2) * ((p : ℂ) ^ z * Complex.log (p : ℂ))) z :=
    hpw.const_mul _
  have hden : HasDerivAt (fun w : ℂ => ((p : ℂ) ^ w - 1) ^ 2)
      (2 * ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z * Complex.log (p : ℂ))) z := by
    have h1 : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w - 1) ((p : ℂ) ^ z * Complex.log (p : ℂ)) z :=
      hpw.sub_const 1
    have h2 : HasDerivAt (fun y : ℂ => y ^ 2) (2 * ((p : ℂ) ^ z - 1)) ((p : ℂ) ^ z - 1) := by
      simpa using hasDerivAt_pow 2 ((p : ℂ) ^ z - 1)
    exact h2.comp z h1
  have hquot := hnum.div hden (pow_ne_zero 2 hz')
  have hfun_eq : (fun w : ℂ => efbD1 p w)
      = ((fun w : ℂ => -(((Real.log (p : ℝ) : ℂ)) ^ 2) * (p : ℂ) ^ w)
          / (fun w : ℂ => ((p : ℂ) ^ w - 1) ^ 2)) := by
    funext w
    simp only [efbD1, Pi.div_apply]
  rw [hfun_eq, hquot.deriv, hlog, efbD2]
  field_simp
  ring

/-! ### Pointwise bounds -/

theorem EulerFactorValueBound (p : ℕ) (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1)‖ ≤ 2 * Real.log (p : ℝ) / (p : ℝ) := by
  obtain ⟨hX, hpX, hD, -, -, hlog⟩ := efb_facts hp hs
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact efb_abs_value hlog hX hpX hpR hD

theorem EulerFactorDerivBound (p : ℕ) (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖efbD1 p s‖ ≤ 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  obtain ⟨hX, hpX, hD, hnorm, -, hlog⟩ := efb_facts hp hs
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  simp only [efbD1, norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hlog, hnorm]
  exact efb_abs_deriv hlog hX hpX hpR hD

theorem EulerFactorDerivTwoBound (p : ℕ) (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖efbD2 p s‖ ≤ 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
  obtain ⟨hX, hpX, hD, hnorm, -, hlog⟩ := efb_facts hp hs
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hW : ‖(p : ℂ) ^ s + 1‖ ≤ (p : ℝ) ^ s.re + 1 := by
    have h := norm_add_le ((p : ℂ) ^ s) (1 : ℂ)
    simp only [norm_one] at h
    rw [hnorm] at h
    exact h
  have hW0 : (0 : ℝ) ≤ ‖(p : ℂ) ^ s + 1‖ := norm_nonneg _
  simp only [efbD2, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, hnorm]
  exact efb_abs_deriv2 hlog hX hpX hpR hD hW0 hW

/-! ### The main statement -/

theorem EulerFactorBounds (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1)‖
        ≤ ∑ p ∈ q.primeFactors, 2 * Real.log (p : ℝ) / (p : ℝ)
    ∧ ‖iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖
        ≤ ∑ p ∈ q.primeFactors, 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ)
    ∧ ‖iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖
        ≤ ∑ p ∈ q.primeFactors, 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
  classical
  have hpr : ∀ p ∈ q.primeFactors, Nat.Prime p := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hp2 : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (hpr p hp).two_le
  have hne : ∀ p ∈ q.primeFactors, (p : ℂ) ^ s ≠ 1 := by
    intro p hp hc
    have h1 : ‖(p : ℂ) ^ s‖ = (p : ℝ) ^ s.re :=
      efb_norm_prime_cpow p (le_trans (by norm_num) (hp2 p hp)) s
    rw [hc, norm_one] at h1
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ s.re := efb_two_le_rpow (hp2 p hp) hs
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := norm_sum_le q.primeFactors
      (fun p : ℕ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))
    exact le_trans h (Finset.sum_le_sum fun p hp => EulerFactorValueBound p (hp2 p hp) hs)
  · have hiter : iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s
        = ∑ p ∈ q.primeFactors, iteratedDeriv 1
            (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s := by
      refine iteratedDeriv_fun_sum (n := 1) (x := s) (I := q.primeFactors)
        (f := fun (p : ℕ) (z : ℂ) => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) ?_
      intro p hp
      exact EulerFactorContDiff p (Nat.Prime.ne_zero (hpr p hp)) s (hne p hp) 1
    rw [hiter]
    have h := norm_sum_le q.primeFactors (fun p : ℕ => iteratedDeriv 1
      (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s)
    refine le_trans h (Finset.sum_le_sum fun p hp => ?_)
    have hp0 : p ≠ 0 := Nat.Prime.ne_zero (hpr p hp)
    rw [iteratedDeriv_one, EulerFactorDeriv p hp0 s (hne p hp)]
    exact EulerFactorDerivBound p (hp2 p hp) hs
  · have hiter : iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
          (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s
        = ∑ p ∈ q.primeFactors, iteratedDeriv 2
            (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s := by
      refine iteratedDeriv_fun_sum (n := 2) (x := s) (I := q.primeFactors)
        (f := fun (p : ℕ) (z : ℂ) => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) ?_
      intro p hp
      exact EulerFactorContDiff p (Nat.Prime.ne_zero (hpr p hp)) s (hne p hp) 2
    rw [hiter]
    have h := norm_sum_le q.primeFactors (fun p : ℕ => iteratedDeriv 2
      (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s)
    refine le_trans h (Finset.sum_le_sum fun p hp => ?_)
    have hp0 : p ≠ 0 := Nat.Prime.ne_zero (hpr p hp)
    have hev : (deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)))
        =ᶠ[𝓝 s] (fun w : ℂ => efbD1 p w) := by
      have hev1 : ∀ᶠ w in 𝓝 s, (p : ℂ) ^ w ≠ 1 :=
        (continuousAt_const_cpow (by exact_mod_cast hp0)).tendsto.eventually_ne (hne p hp)
      filter_upwards [hev1] with w hw
      exact EulerFactorDeriv p hp0 w hw
    have h2eq : iteratedDeriv 2 (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s
        = deriv (fun w : ℂ => efbD1 p w) s := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
    rw [h2eq, EulerFactorDerivTwo p hp0 s (hne p hp)]
    exact EulerFactorDerivTwoBound p (hp2 p hp) hs

end Work.ZeroFreeTables.XY.PrincipalSigma
