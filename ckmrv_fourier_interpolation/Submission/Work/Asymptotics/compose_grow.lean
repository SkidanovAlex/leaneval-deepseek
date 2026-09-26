/-
# Polynomial growth of the derivatives of `r ↦ φ (π r² - a)`

This file proves `Work.Asymptotics.compose_grow`: if a `C^∞` function `φ : ℝ → ℂ` grows at most
like `A (1+|x|)^m` (together with all its derivatives up to order `l+1`), then the derivatives up
to order `l` of the composition `r ↦ φ (Real.pi * r ^ 2 - a)` grow at most like
`(1+|r|)^(2*m+l)`.

The mechanism is Faà di Bruno's formula in the form of the norm bound
`norm_iteratedFDeriv_comp_le` (the bound `n ! * C * D^n` for the `n`-th derivative of a
composition), applied with `f r = π r² - a`, whose derivatives are elementary: `f' = 2πr`,
`f'' = 2π` and `f⁽ᵏ⁾ = 0` for `k ≥ 3`.  The `2 * m` in the exponent comes from `|π r² - a|`
being quadratic in `r`, and the `+ l` from the Bell polynomial of order `j ≤ l` contributing at
most `j` powers of `r`.
-/
import Mathlib

noncomputable section

open scoped ContDiff

namespace Work.Asymptotics

/-! ### The derivatives of the quadratic `r ↦ π r² - a` -/

lemma iteratedDeriv_quad_formula (a : ℝ) (k : ℕ) (r : ℝ) :
    iteratedDeriv k (fun r : ℝ => Real.pi * r ^ 2 - a) r =
      Real.pi * ((Nat.descFactorial 2 k : ℝ) * r ^ (2 - k)) - (if k = 0 then a else 0) := by
  rw [show (fun r : ℝ => Real.pi * r ^ 2 - a)
        = (fun r : ℝ => Real.pi * r ^ 2) - (fun _ => a) from rfl,
    iteratedDeriv_sub (by fun_prop) (by fun_prop), iteratedDeriv_const_mul_field, iteratedDeriv_pow,
    iteratedDeriv_const]

lemma iteratedDeriv_quad_one (a r : ℝ) :
    iteratedDeriv 1 (fun r : ℝ => Real.pi * r ^ 2 - a) r = 2 * Real.pi * r := by
  rw [iteratedDeriv_quad_formula]
  norm_num [Nat.descFactorial]
  ring

lemma iteratedDeriv_quad_two (a r : ℝ) :
    iteratedDeriv 2 (fun r : ℝ => Real.pi * r ^ 2 - a) r = 2 * Real.pi := by
  rw [iteratedDeriv_quad_formula]
  norm_num [Nat.descFactorial]
  ring

lemma iteratedDeriv_quad_eq_zero (a r : ℝ) {k : ℕ} (hk : 3 ≤ k) :
    iteratedDeriv k (fun r : ℝ => Real.pi * r ^ 2 - a) r = 0 := by
  rw [iteratedDeriv_quad_formula, if_neg (by omega : ¬ k = 0),
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 2 < k)]
  ring

/-! ### Faà di Bruno: the derivative of the composition -/

/-- Faà di Bruno with explicit constants: if all derivatives of `φ` up to order `j` at the point
`π r² - a` are bounded by `A (1 + |π r² - a|)^m`, then the `j`-th derivative of
`r ↦ φ (π r² - a)` is bounded by `j! · A (1 + |π r² - a|)^m · (2π(1+|r|))^j`.

The choice `D = 2π (1 + |r|)` for the derivative bound of the quadratic is what makes the
statement uniform in `r``. -/
lemma norm_iteratedDeriv_comp_quad_le (φ : ℝ → ℂ) (a A : ℝ) (m j : ℕ)
    (hφ : ContDiff ℝ ∞ φ)
    (h : ∀ i ≤ j, ∀ x : ℝ, ‖iteratedDeriv i φ x‖ ≤ A * (1 + |x|) ^ m)
    (r : ℝ) :
    ‖iteratedDeriv j (fun r : ℝ => φ (Real.pi * r ^ 2 - a)) r‖ ≤
      (j.factorial : ℝ) * A * (1 + |Real.pi * r ^ 2 - a|) ^ m * (2 * Real.pi * (1 + |r|)) ^ j := by
  have huc : ContDiff ℝ ∞ (fun r : ℝ => Real.pi * r ^ 2 - a) := by fun_prop
  have hn : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hC : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i φ (Real.pi * r ^ 2 - a)‖ ≤ A * (1 + |Real.pi * r ^ 2 - a|) ^ m := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact h i hi _
  have hD : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i (fun r : ℝ => Real.pi * r ^ 2 - a) r‖
        ≤ (2 * Real.pi * (1 + |r|)) ^ i := by
    intro i hi1 hij
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    match i with
    | 0 => omega
    | 1 =>
      rw [pow_one, iteratedDeriv_quad_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      have := abs_nonneg r
      nlinarith [Real.pi_pos]
    | 2 =>
      rw [iteratedDeriv_quad_two, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      have h1 : (1 : ℝ) ≤ 2 * Real.pi * (1 + |r|) := by
        nlinarith [Real.pi_gt_three, abs_nonneg r]
      have h2 : 2 * Real.pi ≤ 2 * Real.pi * (1 + |r|) := by
        nlinarith [abs_nonneg r, Real.pi_pos]
      calc 2 * Real.pi ≤ 2 * Real.pi * (1 + |r|) := h2
        _ ≤ (2 * Real.pi * (1 + |r|)) ^ 2 := by
            conv_rhs => rw [pow_two]
            exact le_mul_of_one_le_left (by positivity) h1
    | (k + 3) =>
      rw [iteratedDeriv_quad_eq_zero a r (by omega), norm_zero]
      positivity
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := φ)
      (f := fun r : ℝ => Real.pi * r ^ 2 - a)
      (n := j) (N := ∞) hφ huc hn r
      (C := A * (1 + |Real.pi * r ^ 2 - a|) ^ m) (D := 2 * Real.pi * (1 + |r|)) hC hD
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at key
  have hfun : φ ∘ (fun r : ℝ => Real.pi * r ^ 2 - a)
      = fun r : ℝ => φ (Real.pi * r ^ 2 - a) := rfl
  rw [hfun] at key
  simpa only [mul_assoc, mul_comm, mul_left_comm] using key

/-! ### Converting `1 + |π r² - a| ≤ (1 + π + |a|) (1 + |r|)²` -/

lemma one_add_abs_quad_le (a r : ℝ) :
    1 + |Real.pi * r ^ 2 - a| ≤ (1 + Real.pi + |a|) * (1 + |r|) ^ 2 := by
  have h1 : |Real.pi * r ^ 2 - a| ≤ Real.pi * r ^ 2 + |a| := by
    calc |Real.pi * r ^ 2 - a| ≤ |Real.pi * r ^ 2| + |a| := abs_sub _ _
      _ = Real.pi * r ^ 2 + |a| := by rw [abs_of_nonneg (by positivity)]
  have h3 : (1 : ℝ) + r ^ 2 ≤ (1 + |r|) ^ 2 := by
    nlinarith [abs_nonneg r, sq_abs r]
  have hK : (0 : ℝ) ≤ 1 + Real.pi + |a| := by positivity
  nlinarith [h1, h3, hK, Real.pi_pos, abs_nonneg a, sq_nonneg r,
    mul_le_mul_of_nonneg_left h3 hK]

/-! ### The main statement -/

theorem compose_grow (φ : ℝ → ℂ) (a : ℝ) (l : ℕ) (A : ℝ) (m : ℕ) (hA : 0 ≤ A)
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (h : ∀ j ≤ l + 1, ∀ x : ℝ, ‖iteratedDeriv j φ x‖ ≤ A * (1 + |x|) ^ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ l, ∀ r : ℝ,
      ‖iteratedDeriv j (fun r : ℝ => φ (Real.pi * r ^ 2 - a)) r‖ ≤ C * (1 + |r|) ^ (2 * m + l) := by
  refine ⟨(l.factorial : ℝ) * A * (1 + Real.pi + |a|) ^ m * (2 * Real.pi) ^ l, by positivity, ?_⟩
  intro j hj r
  have hbound := norm_iteratedDeriv_comp_quad_le φ a A m j hφ (fun i hi x => h i (by omega) x) r
  have hK : (1 + |Real.pi * r ^ 2 - a|) ^ m
      ≤ (1 + Real.pi + |a|) ^ m * (1 + |r|) ^ (2 * m) := by
    have h1 := one_add_abs_quad_le a r
    have h0 : (0 : ℝ) ≤ 1 + |Real.pi * r ^ 2 - a| := by positivity
    calc (1 + |Real.pi * r ^ 2 - a|) ^ m
        ≤ ((1 + Real.pi + |a|) * (1 + |r|) ^ 2) ^ m := pow_le_pow_left₀ h0 h1 m
      _ = (1 + Real.pi + |a|) ^ m * (1 + |r|) ^ (2 * m) := by rw [mul_pow, ← pow_mul]
  calc ‖iteratedDeriv j (fun r : ℝ => φ (Real.pi * r ^ 2 - a)) r‖
      ≤ (j.factorial : ℝ) * A * (1 + |Real.pi * r ^ 2 - a|) ^ m
          * (2 * Real.pi * (1 + |r|)) ^ j := hbound
    _ ≤ (j.factorial : ℝ) * A * ((1 + Real.pi + |a|) ^ m * (1 + |r|) ^ (2 * m))
          * ((2 * Real.pi) ^ j * (1 + |r|) ^ j) := by
        rw [mul_pow]
        gcongr
    _ = ((j.factorial : ℝ) * A * (1 + Real.pi + |a|) ^ m * (2 * Real.pi) ^ j)
          * (1 + |r|) ^ (2 * m + j) := by
        rw [pow_add]; ring
    _ ≤ ((l.factorial : ℝ) * A * (1 + Real.pi + |a|) ^ m * (2 * Real.pi) ^ l)
          * (1 + |r|) ^ (2 * m + l) := by
        have hf : (j.factorial : ℝ) ≤ (l.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le hj
        have hp : (2 * Real.pi) ^ j ≤ (2 * Real.pi) ^ l :=
          pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hj
        have hq : (1 + |r|) ^ (2 * m + j) ≤ (1 + |r|) ^ (2 * m + l) :=
          pow_le_pow_right₀ (by have := abs_nonneg r; linarith) (by omega)
        have hK0 : (0 : ℝ) ≤ (1 + Real.pi + |a|) ^ m := by positivity
        have h1 : (j.factorial : ℝ) * A ≤ (l.factorial : ℝ) * A :=
          mul_le_mul_of_nonneg_right hf hA
        have h2 : (j.factorial : ℝ) * A * (1 + Real.pi + |a|) ^ m
            ≤ (l.factorial : ℝ) * A * (1 + Real.pi + |a|) ^ m :=
          mul_le_mul_of_nonneg_right h1 hK0
        have h3 := mul_le_mul h2 hp (by positivity) (by positivity)
        exact mul_le_mul h3 hq (by positivity) (by positivity)

end Work.Asymptotics
