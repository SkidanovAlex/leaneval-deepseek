import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_directional_deriv

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace
open scoped Topology
open Filter

noncomputable section

/-- First Fréchet derivative of `z ↦ 2 * log (9 - ‖z‖ ^ 2)` at a point of the ball of
radius `3`: it is `-(4 / (9 - ‖y‖ ^ 2)) • innerSL ℝ y`. -/
private lemma hasFDerivAt_twoLog_logRho {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y : E) (hy : ‖y‖ < 3) :
    HasFDerivAt (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2))
      (-(4 / (9 - ‖y‖ ^ 2)) • innerSL ℝ y) y := by
  have hy2 : (9 : ℝ) - ‖y‖ ^ 2 ≠ 0 := by
    have h : ‖y‖ ^ 2 < 9 := by nlinarith [norm_nonneg y, hy]
    linarith
  have h1 : HasFDerivAt (fun z : E => ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 : HasFDerivAt (fun z : E => 9 - ‖z‖ ^ 2) (-(2 • innerSL ℝ y)) y :=
    h1.const_sub 9
  have h3 := h2.log hy2
  have h4 := h3.const_mul (2 : ℝ)
  have heq : (2 : ℝ) • ((9 - ‖y‖ ^ 2)⁻¹ • (-(2 • innerSL ℝ y)))
      = -(4 / (9 - ‖y‖ ^ 2)) • innerSL ℝ y := by
    ext u
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, neg_apply]
    rw [div_eq_mul_inv]
    ring
  rw [heq] at h4
  exact h4

/-- Pointwise form of the first derivative of `z ↦ 2 * log (9 - ‖z‖ ^ 2)`. -/
private lemma fderiv_twoLog_logRho_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y : E) (hy : ‖y‖ < 3) (u : E) :
    fderiv ℝ (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2)) y u =
      -4 * ⟪y, u⟫ / (9 - ‖y‖ ^ 2) := by
  rw [(hasFDerivAt_twoLog_logRho y hy).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The directional derivative at `x` in direction `a` of `y ↦ -4 * ⟪y, a⟫ / (9 - ‖y‖ ^ 2)`. -/
private lemma fderiv_neg_four_inner_div_logRho {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x a : E) (hx : ‖x‖ < 3) (ha : ⟪a, a⟫ = 1) :
    fderiv ℝ (fun y : E => -4 * ⟪y, a⟫ / (9 - ‖y‖ ^ 2)) x a
      = -4 / (9 - ‖x‖ ^ 2) - 8 * ⟪x, a⟫ ^ 2 / (9 - ‖x‖ ^ 2) ^ 2 := by
  have hb : (9 : ℝ) - ‖x‖ ^ 2 ≠ 0 := by
    have h : ‖x‖ ^ 2 < 9 := by nlinarith [norm_nonneg x, hx]
    linarith
  have hq : HasFDerivAt (fun y : E => 9 - ‖y‖ ^ 2) (-(2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 9
  have hinner : HasFDerivAt (fun y : E => ⟪y, a⟫) (innerSL ℝ a) x := by
    have h := (innerSL ℝ a).hasFDerivAt (x := x)
    rw [show (⇑(innerSL ℝ a) : E → ℝ) = fun y => ⟪y, a⟫ from by
      funext y; rw [innerSL_apply_apply, real_inner_comm]] at h
    exact h
  have hnum : HasFDerivAt (fun y : E => -4 * ⟪y, a⟫) ((-4 : ℝ) • innerSL ℝ a) x :=
    hinner.const_mul (-4)
  have hinv : HasFDerivAt (fun y : E => (9 - ‖y‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((9 - ‖x‖ ^ 2) ^ 2)⁻¹)) ∘SL
        (-(2 • innerSL ℝ x))) x :=
    (hasFDerivAt_inv hb).comp x hq
  have hmul := hnum.mul hinv
  have hfun : (fun y : E => -4 * ⟪y, a⟫ / (9 - ‖y‖ ^ 2))
      = fun y : E => (-4 * ⟪y, a⟫) * (9 - ‖y‖ ^ 2)⁻¹ := by
    funext y; rw [div_eq_mul_inv]
  rw [hfun]
  change (fderiv ℝ ((fun y : E => -4 * ⟪y, a⟫) * fun y : E => (9 - ‖y‖ ^ 2)⁻¹) x) a = _
  rw [hmul.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply, innerSL_apply_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [ha]
  field_simp
  ring

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem iteratedFDeriv_two_log_rho_diag {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (x : E)
    (hx : ‖x‖ < 3) (i : ι) :
    (iteratedFDeriv ℝ 2 (fun z => 2 * Real.log (9 - ‖z‖ ^ 2)) x) ![v i, v i] =
      -4 / (9 - ‖x‖ ^ 2) - 8 * (⟪x, v i⟫) ^ 2 / (9 - ‖x‖ ^ 2) ^ 2 := by
  classical
  set a : E := v i with ha_def
  have ha : ⟪a, a⟫ = 1 := by
    rw [ha_def, orthonormal_iff_ite.mp v.orthonormal i i]
    simp
  have hs : IsOpen (Metric.ball (0 : E) 3) := Metric.isOpen_ball
  have hxs : x ∈ Metric.ball (0 : E) 3 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hx
  have hf : ContDiffOn ℝ 2 (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2))
      (Metric.ball (0 : E) 3) := by
    have hq : ContDiffOn ℝ 2 (fun z : E => 9 - ‖z‖ ^ 2) (Metric.ball (0 : E) 3) :=
      contDiffOn_const.sub (contDiff_norm_sq ℝ).contDiffOn
    have hlog : ContDiffOn ℝ 2 (fun z : E => Real.log (9 - ‖z‖ ^ 2)) (Metric.ball (0 : E) 3) :=
      hq.log (fun z hz => by
        have hz' : ‖z‖ < 3 := by
          rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
        have h2 : ‖z‖ ^ 2 < 9 := by nlinarith [norm_nonneg z, hz']
        linarith)
    exact contDiffOn_const.mul hlog
  have hbridge : (iteratedFDeriv ℝ 2 (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2)) x) ![a, a]
      = fderiv ℝ (fun y : E => fderiv ℝ (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2)) y a) x a := by
    have h := iteratedFDeriv_directional_deriv (s := Metric.ball (0 : E) 3) hs hxs
      (n := 1) hf ![a] a
    rw [show (![a, a] : Fin 2 → E) = Fin.cons a ![a] from by
      funext j; fin_cases j <;> simp] at *
    rw [← h]
    have hfun2 : (fun y : E => (iteratedFDeriv ℝ 1 (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2)) y) ![a])
        = fun y : E => fderiv ℝ (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2)) y a := by
      funext y; simp
    rw [hfun2]
  rw [hbridge]
  have hball : ∀ᶠ y in 𝓝 x, ‖y‖ < 3 := by
    have : Metric.ball (0 : E) 3 ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hxs
    filter_upwards [this] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy; exact hy
  have hg : (fun y : E => fderiv ℝ (fun z : E => 2 * Real.log (9 - ‖z‖ ^ 2)) y a)
      =ᶠ[𝓝 x] (fun y : E => -4 * ⟪y, a⟫ / (9 - ‖y‖ ^ 2)) := by
    filter_upwards [hball] with y hy
    exact fderiv_twoLog_logRho_apply y hy a
  rw [hg.fderiv_eq]
  exact fderiv_neg_four_inner_div_logRho x a hx ha

end

end Commons.Analysis.Calculus.FDeriv