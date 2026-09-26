import Mathlib
import Submission.Work.Asymptotics.highPartDefs
import Submission.Work.Asymptotics.psi1_contDiff_omega
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Analysis.ParamIntegral.iteratedDeriv_intervalIntegral_of_cont

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

/-!
# The iterated derivatives of the regularising factor `psi1`

`psi1 x = 2 ∫_0^1 (1 - u) cos (u x) du` is a parametric integral with a completely explicit
integrand, so every iterated derivative is again such an integral and is bounded uniformly:

  `‖(psi1)^{(m)}(x)‖ ≤ 2 ∫_0^1 (1-u) u^m du ≤ 2`.

The proof has two halves:

* `norm_iteratedDeriv_mul_cos` — for real `c`, `u` and every `j`, the `j`-th derivative of
  `x ↦ c cos (u x)` (as a `ℂ`-valued function) is bounded by `|c| |u|^j`; this is the explicit
  `j`-th derivative formula `x ↦ (a cos (u x) + b sin (u x))` obtained by induction, with the
  norms of `cos` and `sin` bounded by `1`.
* `psi1_iteratedDeriv_bound` — differentiation under the integral sign
  (`Work.Analysis.ParamIntegral.iteratedDeriv_intervalIntegral_of_cont`) turns the `m`-th
  derivative of `psiC` into the integral of the `m`-th derivative of the integrand, whose norm
  is at most `2` on `[0,1]`; the integral over an interval of length `1` is then at most `2`.
-/

/-- The integrand of the integral representation of `psi1`: `psi1 r = ∫_0^1 k r u du` with
`k r u = 2 (1-u) cos (u r)`. -/
def psiCIntegrand (r u : ℝ) : ℂ := ((2 * (1 - u) * Real.cos (u * r) : ℝ) : ℂ)

/-- Every iterated derivative of `x ↦ c cos (u x)` (promoted to `ℂ`) is bounded by
`|c| * |u|^j`.  The `j`-th derivative is `x ↦ a cos (u x) + b sin (u x)` with
`‖a‖ + ‖b‖ ≤ |c| |u|^j`, proved by induction using `(cos (u x))' = -u sin (u x)` and
`(sin (u x))' = u cos (u x)`. -/
theorem norm_iteratedDeriv_mul_cos (c u : ℝ) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (fun y : ℝ => ((c * Real.cos (u * y) : ℝ) : ℂ)) x‖ ≤ |c| * |u| ^ j := by
  have hcosd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ((Real.cos (u * z) : ℝ) : ℂ))
      (-((u : ℂ) * ((Real.sin (u * y) : ℝ) : ℂ))) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => Real.cos (u * z)) (-(Real.sin (u * y)) * u) y :=
      (Real.hasDerivAt_cos (u * y)).comp y (by simpa using (hasDerivAt_id y).const_mul u)
    have h2 := h1.ofReal_comp
    have heq : ((↑(-(Real.sin (u * y)) * u) : ℝ) : ℂ)
        = -((u : ℂ) * ((Real.sin (u * y) : ℝ) : ℂ)) := by push_cast; ring
    rwa [heq] at h2
  have hsind : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ((Real.sin (u * z) : ℝ) : ℂ))
      ((u : ℂ) * ((Real.cos (u * y) : ℝ) : ℂ)) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => Real.sin (u * z)) (Real.cos (u * y) * u) y :=
      (Real.hasDerivAt_sin (u * y)).comp y (by simpa using (hasDerivAt_id y).const_mul u)
    have h2 := h1.ofReal_comp
    have heq : ((↑(Real.cos (u * y) * u) : ℝ) : ℂ)
        = (u : ℂ) * ((Real.cos (u * y) : ℝ) : ℂ) := by push_cast; ring
    rwa [heq] at h2
  have hcos1 : ∀ y : ℝ, ‖((Real.cos (u * y) : ℝ) : ℂ)‖ ≤ 1 := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsin1 : ∀ y : ℝ, ‖((Real.sin (u * y) : ℝ) : ℂ)‖ ≤ 1 := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have huC : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have key : ∀ j : ℕ, ∃ a b : ℂ, ‖a‖ + ‖b‖ ≤ |c| * |u| ^ j ∧
      iteratedDeriv j (fun y : ℝ => ((c * Real.cos (u * y) : ℝ) : ℂ))
        = fun y : ℝ => a * ((Real.cos (u * y) : ℝ) : ℂ)
            + b * ((Real.sin (u * y) : ℝ) : ℂ) := by
    intro j
    induction j with
    | zero =>
      refine ⟨(c : ℂ), 0, ?_, ?_⟩
      · rw [norm_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one]
      · funext y
        rw [iteratedDeriv_zero]
        show ((c * Real.cos (u * y) : ℝ) : ℂ)
            = (c : ℂ) * ((Real.cos (u * y) : ℝ) : ℂ) + 0 * ((Real.sin (u * y) : ℝ) : ℂ)
        push_cast; ring
    | succ k ih =>
      obtain ⟨a, b, hbnd, hfun⟩ := ih
      refine ⟨b * (u : ℂ), -(a * (u : ℂ)), ?_, ?_⟩
      · have h1 : ‖b * (u : ℂ)‖ + ‖-(a * (u : ℂ))‖ = (‖a‖ + ‖b‖) * |u| := by
          rw [norm_mul, norm_neg, norm_mul, huC]; ring
        rw [h1]
        calc (‖a‖ + ‖b‖) * |u| ≤ (|c| * |u| ^ k) * |u| :=
              mul_le_mul_of_nonneg_right hbnd (abs_nonneg u)
          _ = |c| * |u| ^ (k + 1) := by rw [pow_succ]; ring
      · rw [iteratedDeriv_succ, hfun]
        funext y
        have hd : HasDerivAt
            (fun z : ℝ => a * ((Real.cos (u * z) : ℝ) : ℂ)
              + b * ((Real.sin (u * z) : ℝ) : ℂ))
            (a * (-((u : ℂ) * ((Real.sin (u * y) : ℝ) : ℂ)))
              + b * ((u : ℂ) * ((Real.cos (u * y) : ℝ) : ℂ))) y :=
          ((hcosd y).const_mul a).add ((hsind y).const_mul b)
        rw [hd.deriv]
        ring
  obtain ⟨a, b, hbnd, hfun⟩ := key j
  rw [hfun]
  have hcx := hcos1 x
  have hsx := hsin1 x
  calc ‖a * ((Real.cos (u * x) : ℝ) : ℂ) + b * ((Real.sin (u * x) : ℝ) : ℂ)‖
      ≤ ‖a * ((Real.cos (u * x) : ℝ) : ℂ)‖ + ‖b * ((Real.sin (u * x) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ = ‖a‖ * ‖((Real.cos (u * x) : ℝ) : ℂ)‖ + ‖b‖ * ‖((Real.sin (u * x) : ℝ) : ℂ)‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * 1 + ‖b‖ * 1 := by
        have h1 := mul_le_mul_of_nonneg_left hcx (norm_nonneg a)
        have h2 := mul_le_mul_of_nonneg_left hsx (norm_nonneg b)
        linarith
    _ = ‖a‖ + ‖b‖ := by ring
    _ ≤ |c| * |u| ^ j := hbnd

theorem psi1_iteratedDeriv_bound (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m Work.Asymptotics.psiC x‖ ≤ 2 := by
  have hfun : Work.Asymptotics.psiC = fun r : ℝ => ∫ u in (0 : ℝ)..1, psiCIntegrand r u := by
    funext r
    rw [psiC, psi1]
    have h1 : ((2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * r) : ℝ) : ℂ)
        = (2 : ℂ) * ((∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * r) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1]
    rw [← intervalIntegral.integral_ofReal]
    rw [← intervalIntegral.integral_const_mul (2 : ℂ)
      (fun s : ℝ => (((1 - s) * Real.cos (s * r) : ℝ) : ℂ))]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [psiCIntegrand]
    push_cast
    ring
  have hbound2 : ∀ j : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ,
      ‖iteratedDeriv j (fun r' => psiCIntegrand r' u) r‖ ≤ 2 := by
    intro j u hu r
    have hle := norm_iteratedDeriv_mul_cos (2 * (1 - u)) u j r
    have hcast : ‖iteratedDeriv j (fun r' => psiCIntegrand r' u) r‖
        = ‖iteratedDeriv j (fun y : ℝ => ((2 * (1 - u) * Real.cos (u * y) : ℝ) : ℂ)) r‖ := rfl
    rw [hcast]
    refine le_trans hle ?_
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have h1u : 0 ≤ 1 - u := by linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 - u)), abs_of_nonneg hu0]
    have hupow : u ^ j ≤ 1 := pow_le_one₀ hu0 hu1
    have h2 : 2 * (1 - u) ≤ 2 := by linarith
    have h3 : (0:ℝ) ≤ u ^ j := pow_nonneg hu0 j
    calc 2 * (1 - u) * u ^ j ≤ 2 * u ^ j := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left hupow (by norm_num)
      _ = 2 := by ring
  have hk_cont : ∀ r : ℝ, Continuous (fun u : ℝ => psiCIntegrand r u) := by
    intro r
    unfold psiCIntegrand
    fun_prop
  have hk_smooth : ∀ u : ℝ, ContDiff ℝ Work.RadialSpace.Smooth
      (fun r : ℝ => psiCIntegrand r u) := by
    intro u
    unfold psiCIntegrand
    have h : ContDiff ℝ ∞ (fun r : ℝ => (2 * (1 - u) * Real.cos (u * r) : ℝ)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  obtain ⟨hcont, hform⟩ :=
    Work.Analysis.ParamIntegral.iteratedDeriv_intervalIntegral_of_cont psiCIntegrand
      hk_cont hk_smooth (fun j => ⟨2, by norm_num, hbound2 j⟩)
  rw [hfun, hform m x]
  have hb : ‖∫ u in (0 : ℝ)..1, iteratedDeriv m (fun r' => psiCIntegrand r' u) x‖
      ≤ 2 * |1 - (0 : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
      have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by
        rwa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact hbound2 m u ⟨le_of_lt huIoc.1, huIoc.2⟩ x)
  simpa using hb

end Work.Asymptotics
