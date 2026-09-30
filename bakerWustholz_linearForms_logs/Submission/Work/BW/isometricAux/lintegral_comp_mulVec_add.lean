import Mathlib
import Submission.Work.BW.measurePreservingOrthogonal
import Submission.Work.BW.orthogonalParameterization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.isometricAux

open MeasureTheory Matrix

/-- Change of variables: if `B` and `Bp` have orthonormal columns which are mutually
orthogonal, then `(x, y) ↦ B.mulVec x + Bp.mulVec y` is a measure-preserving
parameterisation of `ℝⁿ`, so it can be used to compute the outer integral. -/
theorem lintegral_comp_mulVec_add {n k : ℕ} (hk : k ≤ n) (B : Matrix (Fin n) (Fin k) ℝ)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ)
    (hB : B.transpose * B = 1) (hBp : Bp.transpose * Bp = 1) (hBBp : B.transpose * Bp = 0)
    (F : (Fin n → ℝ) → ENNReal) (hF : Measurable F) :
    ∫⁻ u, F u
      = ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n - k) → ℝ, F (B.mulVec x + Bp.mulVec y) := by
  have hMP : MeasurePreserving (fun u : Fin n → ℝ => (Work.BW.orthoParamM hk B Bp).mulVec u)
      (volume : Measure (Fin n → ℝ)) (volume : Measure (Fin n → ℝ)) :=
    Work.BW.measurePreservingOrthogonal _
      (Work.BW.orthoParamM_transpose_mul_self hk B Bp hB hBp hBBp)
  have hV := Work.BW.orthoParamV_measurePreserving hk
  have hmul := Work.BW.orthoParamM_mulVec hk B Bp
  have hBc : Continuous (fun x : Fin k → ℝ => B.mulVec x) := by
    rw [show (fun x : Fin k → ℝ => B.mulVec x) =
        (⇑(toLin' B) : (Fin k → ℝ) → (Fin n → ℝ)) from by funext x; rw [toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hBpc : Continuous (fun y : Fin (n - k) → ℝ => Bp.mulVec y) := by
    rw [show (fun y : Fin (n - k) → ℝ => Bp.mulVec y) =
        (⇑(toLin' Bp) : (Fin (n - k) → ℝ) → (Fin n → ℝ)) from by funext y; rw [toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hG : Measurable (fun p : (Fin k → ℝ) × (Fin (n - k) → ℝ) =>
      F (B.mulVec p.1 + Bp.mulVec p.2)) :=
    hF.comp ((hBc.comp continuous_fst).add (hBpc.comp continuous_snd)).measurable
  calc ∫⁻ u, F u ∂(volume : Measure (Fin n → ℝ))
      = ∫⁻ u, F ((Work.BW.orthoParamM hk B Bp).mulVec u)
          ∂(volume : Measure (Fin n → ℝ)) :=
        (hMP.lintegral_comp hF).symm
    _ = ∫⁻ u, F (B.mulVec (Work.BW.orthoParamV hk u).1 +
            Bp.mulVec (Work.BW.orthoParamV hk u).2)
          ∂(volume : Measure (Fin n → ℝ)) :=
        lintegral_congr (fun u => by rw [hmul u])
    _ = ∫⁻ p : (Fin k → ℝ) × (Fin (n - k) → ℝ),
          F (B.mulVec p.1 + Bp.mulVec p.2)
          ∂(volume : Measure ((Fin k → ℝ) × (Fin (n - k) → ℝ))) :=
        hV.lintegral_comp hG
    _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n - k) → ℝ, F (B.mulVec x + Bp.mulVec y) :=
        (lintegral_lintegral (μ := (volume : Measure (Fin k → ℝ)))
          (ν := (volume : Measure (Fin (n - k) → ℝ)))
          (f := fun x y => F (B.mulVec x + Bp.mulVec y)) hG.aemeasurable).symm

end Work.BW.isometricAux
