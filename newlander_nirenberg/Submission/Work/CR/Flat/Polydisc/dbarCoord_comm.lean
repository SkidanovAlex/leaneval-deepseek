import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The continuous linear map `L ↦ (1/2)(L e_j + i·L(i·e_j))` on `(ℂⁿ →L[ℝ] ℂ)`; composing it
with `fderiv ℝ u` gives `dbarCoord j u`. -/
noncomputable def dbarCoordPhi {n : ℕ} (j : Fin n) : ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (1/2 : ℂ)).comp
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j 1)
      + (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
          (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)))

lemma dbarCoord_eq_comp {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) :
    dbarCoord j u = dbarCoordPhi j ∘ (fderiv ℝ u) := by
  funext x
  simp only [dbarCoordPhi, Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, dbarCoord, ContinuousLinearMap.mul_apply']

/-- The derivative of `dbarCoord j u` at `z`, in terms of the second derivative of `u`. -/
lemma fderiv_dbarCoord {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : ContDiffAt ℝ 2 u z) (v : Fin n → ℂ) :
    fderiv ℝ (dbarCoord j u) z v
      = (1/2 : ℂ) * (((fderiv ℝ (fderiv ℝ u) z) v) (Pi.single j 1)
          + Complex.I * (((fderiv ℝ (fderiv ℝ u) z) v) (Pi.single j Complex.I))) := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [dbarCoord_eq_comp j u, fderiv_comp z (dbarCoordPhi j).differentiableAt hdu,
    ContinuousLinearMap.fderiv]
  simp only [dbarCoordPhi, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply']

/-- The flat `∂̄`-operators on `ℂⁿ` commute: `∂̄_k ∂̄_j u = ∂̄_j ∂̄_k u` for `u` twice
real-differentiable.  Equivalently, the `(0,1)`-form `∂̄u` is closed, which is the
flat form of `∂̄² = 0` (compare the general `J`-version in
`Submission/Work/Dbar/sq_zero.lean`). -/
theorem dbarCoord_comm {n : ℕ} (j k : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : ContDiffAt ℝ 2 u z) :
    dbarCoord k (dbarCoord j u) z = dbarCoord j (dbarCoord k u) z := by
  have hsymm : ∀ a b : Fin n → ℂ,
      ((fderiv ℝ (fderiv ℝ u) z) a) b = ((fderiv ℝ (fderiv ℝ u) z) b) a :=
    fun a b => (hu.isSymmSndFDerivAt (by simp)).eq a b
  change (1/2 : ℂ) * (fderiv ℝ (dbarCoord j u) z (Pi.single k 1)
        + Complex.I * fderiv ℝ (dbarCoord j u) z (Pi.single k Complex.I))
      = (1/2 : ℂ) * (fderiv ℝ (dbarCoord k u) z (Pi.single j 1)
        + Complex.I * fderiv ℝ (dbarCoord k u) z (Pi.single j Complex.I))
  rw [fderiv_dbarCoord j u z hu (Pi.single k 1),
      fderiv_dbarCoord j u z hu (Pi.single k Complex.I),
      fderiv_dbarCoord k u z hu (Pi.single j 1),
      fderiv_dbarCoord k u z hu (Pi.single j Complex.I),
      hsymm (Pi.single k 1) (Pi.single j 1),
      hsymm (Pi.single k 1) (Pi.single j Complex.I),
      hsymm (Pi.single k Complex.I) (Pi.single j 1),
      hsymm (Pi.single k Complex.I) (Pi.single j Complex.I)]
  ring

end Work.CR.Flat.Polydisc
