import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The reflection of the half-space is a `C^∞` local diffeomorphism

`Work.ThomBordism.CofAtlas.reflOph` is the reflection of `EuclideanHalfSpace 9` negating the
tangential coordinate `1` (`reflHom.toOpenPartialHomeomorph`).  It is the conjugate of the linear
reflection `reflLin` of `ℝ⁹` by the half-space chart `𝓡∂ 9`, so in the coordinates of `𝓡∂ 9` it is
the (linear, hence `C^∞`) map `reflLin`; hence it lies in the `C^∞` structure groupoid
`contDiffGroupoid ∞ (𝓡∂ 9)`.
-/

open Set Function
open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.CofAtlas

/-- In the `𝓡∂ 9`-coordinates, `reflOph` is `reflLin`. -/
theorem reflOph_coord (y : EuclideanHalfSpace 9) :
    (𝓡∂ 9) (reflOph y) = reflLin ((𝓡∂ 9) y) :=
  reflOph_toFun_val y

/-- In the `𝓡∂ 9`-coordinates, `reflOph.symm` is (also) `reflLin`. -/
theorem reflOph_symm_coord (y : EuclideanHalfSpace 9) :
    (𝓡∂ 9) (reflOph.symm y) = reflLin ((𝓡∂ 9) y) :=
  rfl

theorem reflOph_mem_contDiffGroupoid :
    Work.ThomBordism.CofAtlas.reflOph ∈
      contDiffGroupoid ((⊤ : ENat) : WithTop ENat)
        (modelWithCornersEuclideanHalfSpace 9) := by
  have h1 : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      ((𝓡∂ 9) ∘ ⇑reflOph ∘ (𝓡∂ 9).symm) (range (𝓡∂ 9)) := by
    refine ContDiffOn.congr ((reflE : E9 →L[ℝ] E9).contDiff.contDiffOn) ?_
    intro x hx
    have hx' : (𝓡∂ 9) ((𝓡∂ 9).symm x) = x := (𝓡∂ 9).right_inv hx
    show (𝓡∂ 9) (reflOph ((𝓡∂ 9).symm x)) = (reflE : E9 →L[ℝ] E9) x
    rw [reflOph_coord ((𝓡∂ 9).symm x), hx']
    rfl
  have h2 : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      ((𝓡∂ 9) ∘ ⇑reflOph.symm ∘ (𝓡∂ 9).symm) (range (𝓡∂ 9)) := by
    refine ContDiffOn.congr ((reflE : E9 →L[ℝ] E9).contDiff.contDiffOn) ?_
    intro x hx
    have hx' : (𝓡∂ 9) ((𝓡∂ 9).symm x) = x := (𝓡∂ 9).right_inv hx
    show (𝓡∂ 9) (reflOph.symm ((𝓡∂ 9).symm x)) = (reflE : E9 →L[ℝ] E9) x
    rw [reflOph_symm_coord ((𝓡∂ 9).symm x), hx']
    rfl
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  exact ⟨h1.mono (inter_subset_right), h2.mono (inter_subset_right)⟩

end Work.ThomBordism.CofAtlas
