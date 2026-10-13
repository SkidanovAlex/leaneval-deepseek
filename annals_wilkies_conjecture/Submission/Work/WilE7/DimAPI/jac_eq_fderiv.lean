import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval

set_option autoImplicit false
noncomputable section

open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.DimAPI

/-- The Fréchet derivative of the vector valued map `w ↦ (a ↦ eaEval c (h a) w)` identifies with the
matrix `(a,l) ↦ eaEval c (eaD c l (h a)) z` acting by matrix-vector multiplication: component `a`
of the derivative is `∑ i, eaEval c (eaD c i (h a)) z * v i`. -/
theorem fderiv_pi_eaEval_eq_mulVecLin {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (z : Fin k → ℝ) :
    ((fderiv ℝ (fun w : Fin k → ℝ => fun a : Fin j => eaEval c (h a) w) z :
        (Fin k → ℝ) →L[ℝ] (Fin j → ℝ)) : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ))
      = (Matrix.of fun (a : Fin j) (l : Fin k) => eaEval c (eaD c l (h a)) z).mulVecLin := by
  have hpt : ∀ v a, ((ContinuousLinearMap.pi fun a : Fin j =>
      ∑ i : Fin k, (eaEval c (eaD c i (h a)) z) • ContinuousLinearMap.proj i) :
        (Fin k → ℝ) →L[ℝ] (Fin j → ℝ)) v a
      = (Matrix.of fun (a : Fin j) (l : Fin k) => eaEval c (eaD c l (h a)) z).mulVecLin v a := by
    intro v a
    rw [ContinuousLinearMap.pi_apply, sum_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]
  have hpi : HasFDerivAt (fun w : Fin k → ℝ => fun a : Fin j => eaEval c (h a) w)
      (ContinuousLinearMap.pi fun a : Fin j =>
        ∑ i : Fin k, (eaEval c (eaD c i (h a)) z) • ContinuousLinearMap.proj i) z :=
    hasFDerivAt_pi.mpr fun a => Work.WilE5.Calc.hasFDerivAt_eaEval c (h a) z
  rw [hpi.fderiv]
  apply LinearMap.ext
  intro v
  funext a
  exact hpt v a

theorem jac_eq_fderiv {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (z : Fin (p + q) → ℝ) :
    (Work.WilE7.MainDesign.jac S z : (Fin (p + q) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ))
      = ((fderiv ℝ (fun w : Fin (p + q) → ℝ => fun a : Fin S.j =>
            WilkiesDesign.E.eaEval S.X.c (S.h a) w) z :
          (Fin (p + q) → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
        (Fin (p + q) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)) := by
  rw [fderiv_pi_eaEval_eq_mulVecLin S.X.c S.h z]
  rfl

end Work.WilE7.DimAPI
