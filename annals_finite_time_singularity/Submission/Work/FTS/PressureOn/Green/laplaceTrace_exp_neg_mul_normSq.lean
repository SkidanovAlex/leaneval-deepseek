import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green

/-- The first derivative of the Gaussian profile `y ↦ exp (-(c‖y‖²))`.  It is
`-2c·exp(-(c‖z‖²))·⟪z,·⟫`; here the linear functional is written as
`Real.exp (-(c‖z‖²)) • ((-c) • (2 • innerSL ℝ z))` so that no rewriting is needed in the
second-derivative computation. -/
theorem hasFDerivAt_exp_neg_mul_normSq (c : ℝ) (z : Work.FTS.PressureOn.R3) :
    HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2)))
      (Real.exp (-(c * ‖z‖ ^ 2)) • ((-c) • (2 • innerSL ℝ z))) z := by
  have h1 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => c * ‖y‖ ^ 2)
      (c • (2 • innerSL ℝ z)) z :=
    h1.const_mul c
  have h3 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => -(c * ‖y‖ ^ 2))
      (-(c • (2 • innerSL ℝ z))) z :=
    h2.neg
  have h4 := h3.exp
  convert h4 using 1
  rw [neg_smul]

/-- The diagonal entry `∂ᵢ∂ᵢ` of the Hessian of the Gaussian profile, in the standard basis
`FiniteTimeSingularity.e`:
`∂ᵢ∂ᵢ (exp(-(c‖·‖²))) z = -2c·exp(-(c‖z‖²)) + 4c²·exp(-(c‖z‖²))·(zᵢ)²`. -/
theorem fderiv_fderiv_exp_neg_mul_normSq_diag (c : ℝ) (z : Work.FTS.PressureOn.R3) (i : Fin 3) :
    fderiv ℝ (fun w : Work.FTS.PressureOn.R3 =>
        fderiv ℝ (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2))) w
          (FiniteTimeSingularity.e i)) z (FiniteTimeSingularity.e i)
      = -2 * c * Real.exp (-(c * ‖z‖ ^ 2))
        + 4 * c ^ 2 * Real.exp (-(c * ‖z‖ ^ 2)) * (z i) ^ 2 := by
  -- The first derivative, as an explicit function of the base point.
  have hfun : (fun w : Work.FTS.PressureOn.R3 =>
        fderiv ℝ (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2))) w
          (FiniteTimeSingularity.e i))
      = fun w : Work.FTS.PressureOn.R3 =>
          Real.exp (-(c * ‖w‖ ^ 2)) * ((-2 * c) * (innerSL ℝ (FiniteTimeSingularity.e i)) w) := by
    funext w
    have h1 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => ‖y‖ ^ 2) (2 • innerSL ℝ w) w :=
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt
    have h2 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => c * ‖y‖ ^ 2)
        (c • (2 • innerSL ℝ w)) w :=
      h1.const_mul c
    have h3 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => -(c * ‖y‖ ^ 2))
        (-(c • (2 • innerSL ℝ w))) w :=
      h2.neg
    rw [(h3.exp).fderiv]
    simp only [neg_apply, smul_apply, innerSL_apply_apply]
    rw [real_inner_comm (FiniteTimeSingularity.e i) w]
    ring
  rw [hfun]
  -- Product rule for `w ↦ exp(-(c‖w‖²)) · ((-2c)·⟪eᵢ,w⟫)`.
  have hA : HasFDerivAt (fun w : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖w‖ ^ 2)))
      (Real.exp (-(c * ‖z‖ ^ 2)) • ((-c) • (2 • innerSL ℝ z))) z :=
    hasFDerivAt_exp_neg_mul_normSq c z
  have hB : HasFDerivAt
      (fun w : Work.FTS.PressureOn.R3 => (-2 * c) * (innerSL ℝ (FiniteTimeSingularity.e i)) w)
      ((-2 * c) • innerSL ℝ (FiniteTimeSingularity.e i)) z :=
    (ContinuousLinearMap.hasFDerivAt (innerSL ℝ (FiniteTimeSingularity.e i))).const_mul (-2 * c)
  have hprod : HasFDerivAt (fun w : Work.FTS.PressureOn.R3 =>
        Real.exp (-(c * ‖w‖ ^ 2)) * ((-2 * c) * (innerSL ℝ (FiniteTimeSingularity.e i)) w))
      (Real.exp (-(c * ‖z‖ ^ 2)) • ((-2 * c) • innerSL ℝ (FiniteTimeSingularity.e i))
        + (-2 * c * (innerSL ℝ (FiniteTimeSingularity.e i)) z) •
          (Real.exp (-(c * ‖z‖ ^ 2)) • ((-c) • (2 • innerSL ℝ z)))) z := hA.mul hB
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply]
  have hee : inner ℝ (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e i) = 1 := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hze : inner ℝ z (FiniteTimeSingularity.e i) = z i := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hez : inner ℝ (FiniteTimeSingularity.e i) z = z i := by
    rw [real_inner_comm, hze]
  rw [hee, hze, hez]
  ring

/-- **The Laplacian of the Gaussian profile**: for the Gaussian `y ↦ exp(-(c‖y‖²))` the trace of
the Hessian (in the standard basis of `ℝ³`) is `(4c²‖z‖² - 6c)·exp(-(c‖z‖²))`.

This is the one-dimensional-in-`r` computation `Δ exp(-cr²) = (4c²r² - 6c) exp(-cr²)` written in
`ℝ³`: the three diagonal entries `-2c·exp + 4c²·exp·zᵢ²` sum to `-6c·exp + 4c²·exp·‖z‖²`. -/
theorem laplaceTrace_exp_neg_mul_normSq (c : ℝ) (z : Work.FTS.PressureOn.R3) :
    Work.FTS.PressureOn.laplaceTrace (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2))) z
      = (4 * c ^ 2 * ‖z‖ ^ 2 - 6 * c) * Real.exp (-(c * ‖z‖ ^ 2)) := by
  have hsum : ∑ i : Fin 3, (z i) ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [Work.FTS.PressureOn.laplaceTrace]
  rw [Finset.sum_congr rfl (fun i _ => fderiv_fderiv_exp_neg_mul_normSq_diag c z i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  norm_num
  ring

end Work.FTS.PressureOn.Green
