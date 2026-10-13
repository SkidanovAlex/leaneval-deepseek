import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv

namespace Work.WilE7.Endgame

theorem fderiv_prod_eq_jac_prod {M r : ℕ} (S : WilkiesDesign.E.Stratum 0 M)
    (A : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (y : Fin (0 + M) → ℝ) :
    (fderiv ℝ (fun w : Fin (0 + M) → ℝ =>
        ((fun a : Fin S.j => WilkiesDesign.E.eaEval S.X.c (S.h a) w),
         (LinearMap.toContinuousLinearMap A) w)) y)
      = (((Work.WilE7.MainDesign.jac S y).prod A).toContinuousLinearMap) := by
  -- The map `w ↦ (a ↦ eaEval c (S.h a) w, A w)` is a pair of maps, so its Fréchet derivative is
  -- the product of the two derivatives: the Jacobian of the equations of `S` and `A` itself.
  have hd1 : DifferentiableAt ℝ (fun w : Fin (0 + M) → ℝ => fun a : Fin S.j =>
      WilkiesDesign.E.eaEval S.X.c (S.h a) w) y :=
    differentiableAt_pi.mpr fun a =>
      (Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) y).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun w : Fin (0 + M) → ℝ =>
      (LinearMap.toContinuousLinearMap A) w) y :=
    (LinearMap.toContinuousLinearMap A).differentiableAt
  have h1 : (fderiv ℝ (fun w : Fin (0 + M) → ℝ => fun a : Fin S.j =>
      WilkiesDesign.E.eaEval S.X.c (S.h a) w) y)
      = (Work.WilE7.MainDesign.jac S y).toContinuousLinearMap := by
    rw [← ContinuousLinearMap.coe_inj, LinearMap.coe_toContinuousLinearMap]
    exact (Work.WilE7.DimAPI.jac_eq_fderiv S y).symm
  have h2 : (fderiv ℝ (fun w : Fin (0 + M) → ℝ =>
      (LinearMap.toContinuousLinearMap A) w) y) = A.toContinuousLinearMap := by
    rw [ContinuousLinearMap.fderiv]
  rw [DifferentiableAt.fderiv_prodMk hd1 hd2, h1, h2]
  rfl

end Work.WilE7.Endgame
