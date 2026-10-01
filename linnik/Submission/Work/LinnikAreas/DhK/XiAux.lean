import Mathlib
import Submission.Work.LinnikAreas.DhK.Defs

/-!
# `Work.LinnikAreas.DhK.XiAux`

Elementary analytic API for the entire completion `Ξ = Xi` of the Riemann zeta function, in the
scaled form used by the partial-fraction expansion of `(Ξ'/Ξ)^{(k)}`:

* `xiL A = log (A + 2) + 2` plays the role of `L_N 1` of the `P₃` engine (`xiL_eq_LN_one`);
* `Xi` is entire (`Xi_differentiable`, `Xi_analyticOnNhd`, `Xi_meromorphicOn`);
* its ball divisors are nonnegative with finite support and vanish exactly on the zeros
  (`Xi_divisor_nonneg`, `Xi_divisor_support_finite`, `Xi_divisor_ne_zero_is_zero`);
* the two neutral analytic inputs of `xiE_circle_growth` / `xiE_zeroCount`, restated in the
  `xiL` scale (`Xi_growth_L`, `Xi_zeroCount_L`), and the zero-free small ball
  `xiE_noZero_ball` restated as a lower bound for the modulus of the zeros (`Xi_zero_ge_delta`).
-/

open scoped Classical BigOperators
open Filter Metric
noncomputable section

namespace Work.LinnikAreas.DhK

/-- The logarithmic scale of the Riemann `Ξ`: `xiL A = log (A + 2) + 2`.  It is the special
case `N = 1` of `Commons.NumberTheory.Linnik.L_N`. -/
def xiL (A : ℝ) : ℝ := Real.log (A + 2) + 2

lemma xiL_eq_LN_one (A : ℝ) : xiL A = Commons.NumberTheory.Linnik.L_N 1 A := by
  simp [xiL, Commons.NumberTheory.Linnik.L_N]

lemma xiL_ge_two {A : ℝ} (hA : 0 ≤ A) : 2 ≤ xiL A := by
  rw [xiL_eq_LN_one]; exact Commons.NumberTheory.Linnik.pf_L_ge_two (N := 1) hA

lemma xiL_pos {A : ℝ} (hA : 0 ≤ A) : 0 < xiL A := by
  rw [xiL_eq_LN_one]; exact Commons.NumberTheory.Linnik.pf_L_pos (N := 1) hA

lemma xiL_mono {A B : ℝ} (hA : 0 ≤ A) (h : A ≤ B) : xiL A ≤ xiL B := by
  rw [xiL_eq_LN_one, xiL_eq_LN_one]
  exact Commons.NumberTheory.Linnik.pf_L_mono (N := 1) hA h

lemma xiL_log_le {A : ℝ} (hA : 0 ≤ A) : Real.log (xiL A) ≤ xiL A := by
  rw [xiL_eq_LN_one]
  exact Commons.NumberTheory.Linnik.pf_log_L_le_L (N := 1) hA

lemma xiL_two_mul_le {A : ℝ} (hA : 1 ≤ A) : xiL (2 * A) ≤ 2 * xiL A := by
  rw [xiL_eq_LN_one, xiL_eq_LN_one]
  exact Commons.NumberTheory.Linnik.pf_L_two_mul_le (N := 1) hA

lemma xiL_sq_div_self_tendsto_zero :
    Tendsto (fun A : ℝ => (xiL A) ^ 2 / A) atTop (nhds 0) := by
  have h := Commons.NumberTheory.Linnik.pf_L_sq_div_self_tendsto_zero (N := 1)
  refine h.congr' ?_
  filter_upwards with A
  rw [xiL_eq_LN_one]

lemma xiL_div_self_tendsto_zero : Tendsto (fun A : ℝ => xiL A / A) atTop (nhds 0) := by
  have h := Commons.NumberTheory.Linnik.log_add_two_add_const_div_self_tendsto_zero (2 : ℝ)
  refine h.congr' ?_
  filter_upwards with A
  simp only [xiL]

/-! ## `Ξ` and its ball divisors -/

lemma Xi_differentiable : Differentiable ℂ Xi := by
  unfold Xi
  exact (differentiable_const (1 / 2 : ℂ)).add
    ((by fun_prop : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1))).mul
      differentiable_completedZeta₀)

lemma Xi_analyticOnNhd (U : Set ℂ) : AnalyticOnNhd ℂ Xi U := fun z _ => Xi_differentiable.analyticAt z

lemma Xi_meromorphicOn (U : Set ℂ) : MeromorphicOn Xi U := (Xi_analyticOnNhd U).meromorphicOn

/-- Ball divisors of the entire function `Ξ` are nonnegative. -/
lemma Xi_divisor_nonneg (R : ℝ) (u : ℂ) :
    (0 : ℤ) ≤ MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) R) u := by
  by_cases h : u ∈ Metric.closedBall (0 : ℂ) R
  · exact Commons.NumberTheory.Linnik.divisor_nonneg_of_analyticOnNhd (Xi_analyticOnNhd _) h
  · rw [Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem h]

/-- Ball divisors of `Ξ` have finite support. -/
lemma Xi_divisor_support_finite (R : ℝ) :
    (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) R) u)).Finite :=
  MeromorphicOn.divisor_support_finite_of_subset (f := Xi)
    (V := Metric.closedBall (0 : ℂ) R) (Xi_meromorphicOn _)
    (isCompact_closedBall (0 : ℂ) R) (by simp)

/-- A nonzero ball-divisor coefficient of `Ξ` sits at a zero of `Ξ`. -/
lemma Xi_divisor_ne_zero_is_zero {R : ℝ} {u : ℂ}
    (h : MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) R) u ≠ 0) : Xi u = 0 := by
  by_contra hfu
  have hu : u ∈ Metric.closedBall (0 : ℂ) R := by
    by_contra hout
    exact h (Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem hout)
  exact h (Commons.NumberTheory.Linnik.divisor_zero_of_analytic_ne_zero
    (Xi_analyticOnNhd _) hu hfu)

/-! ## The neutral analytic inputs, in the `xiL` scale -/

/-- **Circle growth of `Ξ` in the `xiL` scale**: for some `c ≥ 0`, on every circle `|z| = R`
with `R ≥ 2`, `‖Ξ z‖ ≤ exp (c · R · xiL R)`. -/
lemma Xi_growth_L :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖Xi z‖ ≤ Real.exp (c * R * xiL R) := by
  obtain ⟨c0, hc0⟩ := Commons.NumberTheory.Zeta.xiE_circle_growth
  refine ⟨max c0 0, le_max_right _ _, ?_⟩
  intro R hR z hz
  have h := hc0 R hR z hz
  have hR0 : 0 ≤ R := by linarith
  have hT0 : 0 ≤ Real.log (R + 2) + 2 := by
    have h1 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    linarith
  have hle : ‖Xi z‖ ≤ Real.exp (c0 * R * (Real.log (R + 2) + 2)) := h
  refine le_trans hle (Real.exp_le_exp.mpr ?_)
  have hcc : c0 * R ≤ max c0 0 * R :=
    mul_le_mul_of_nonneg_right (le_max_left c0 0) hR0
  calc c0 * R * (Real.log (R + 2) + 2) = (c0 * R) * (Real.log (R + 2) + 2) := by ring
    _ ≤ (max c0 0 * R) * (Real.log (R + 2) + 2) := mul_le_mul_of_nonneg_right hcc hT0
    _ = max c0 0 * R * xiL R := by rw [xiL]

/-- **Zero count of `Ξ` in the `xiL` scale**: for some `c ≥ 0`, the total (nonnegative)
divisor mass of `Ξ` over the closed ball of radius `R ≥ 2` is at most `c · R · xiL R`. -/
lemma Xi_zeroCount_L :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ))
        ≤ c * R * xiL R := by
  obtain ⟨c0, hc0⟩ := Commons.NumberTheory.Zeta.xiE_zeroCount
  refine ⟨max c0 0, le_max_right _ _, ?_⟩
  intro R hR
  have h := hc0 R hR
  have hR0 : 0 ≤ R := by linarith
  have hT0 : 0 ≤ Real.log (R + 2) + 2 := by
    have h1 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    linarith
  have hle : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi
      (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤ c0 * R * (Real.log (R + 2) + 2) := h
  refine le_trans hle ?_
  have hcc : c0 * R ≤ max c0 0 * R :=
    mul_le_mul_of_nonneg_right (le_max_left c0 0) hR0
  calc c0 * R * (Real.log (R + 2) + 2) = (c0 * R) * (Real.log (R + 2) + 2) := by ring
    _ ≤ (max c0 0 * R) * (Real.log (R + 2) + 2) := mul_le_mul_of_nonneg_right hcc hT0
    _ = max c0 0 * R * xiL R := by rw [xiL]

/-- **No zeros of `Ξ` near the origin**: there is `δ₀ > 0` with `δ₀ ≤ ‖u‖` for every zero
`u` of `Ξ`. -/
lemma Xi_zero_ge_delta : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ u : ℂ, Xi u = 0 → δ₀ ≤ ‖u‖ := by
  obtain ⟨δ₀, hδ₀pos, -, hδ₀⟩ := Commons.NumberTheory.Zeta.xiE_noZero_ball
  refine ⟨δ₀, hδ₀pos, fun u hu => ?_⟩
  by_contra hlt
  exact hδ₀ u (lt_of_not_ge hlt) hu

end Work.LinnikAreas.DhK
