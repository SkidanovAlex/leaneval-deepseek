import Mathlib
import Submission.Work.Drive.TripleMeetDefs

/-!
# `TripleCommonDir` is invariant under composing with a continuous linear equivalence

`Work.Drive.TripleCommonDir f₀ f₁ f₂ v` (`Submission/Work/Drive/TripleMeetDefs.lean`) says that the
three vectors `fᵢ (v i)` coincide: a triple in the kernel direction of the difference map of the
three `3`-chains.  Post-composing the three maps with a continuous linear equivalence `L` of the
target (a change of linear coordinates, the linear part of a chart) conjugates the condition: since
`L` is injective, `L (f₀ v₀) = L (fᵢ vᵢ)` holds exactly when `f₀ v₀ = fᵢ vᵢ` does.

This is the chart-independence of `TripleCommonDir`, companion to
`Work.Drive.tripleTransverse_comp_continuousLinearEquiv` for `TripleTransverse`.
-/

namespace Work.Drive

theorem tripleCommonDir_comp_continuousLinearEquiv
    (L : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    Work.Drive.TripleCommonDir ((L : _ →L[ℝ] _).comp f₀) ((L : _ →L[ℝ] _).comp f₁)
      ((L : _ →L[ℝ] _).comp f₂) v ↔ Work.Drive.TripleCommonDir f₀ f₁ f₂ v := by
  unfold Work.Drive.TripleCommonDir
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  constructor
  · -- the three `L`-images coincide, and `L` is injective
    rintro ⟨h1, h2⟩
    exact ⟨L.injective h1, L.injective h2⟩
  · -- the three original vectors coincide, so their `L`-images do too
    rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], by rw [h2]⟩

end Work.Drive
