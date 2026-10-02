import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- Conjugation on `ℂ` is `C¹` as a real map: it is the real continuous linear
equivalence `Complex.conjCLE`. -/
theorem contDiff_one_star : ContDiff ℝ 1 (star : ℂ → ℂ) := by
  have h : ContDiff ℝ 1 (fun z : ℂ => Complex.conjCLE z) :=
    ContinuousLinearEquiv.contDiff (Complex.conjCLE) (𝕜 := ℝ) (n := 1)
  have h2 : (fun z : ℂ => Complex.conjCLE z) = (star : ℂ → ℂ) := by
    funext z
    exact Complex.conjCLE_apply z
  rwa [h2] at h

/-- An antiholomorphic function is real `C¹`: if `star ∘ f` is complex
differentiable then `f = star ∘ (star ∘ f)` is the composite of a holomorphic
(hence real `C^∞`) map with the real-`C¹` conjugation. -/
theorem contDiff_one_of_antiholo {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f)) :
    ContDiff ℝ 1 f := by
  -- `star ∘ f` is holomorphic, hence smooth over `ℂ`, hence over `ℝ`
  have hgr : ContDiff ℝ 1 (star ∘ f) :=
    ContDiff.restrict_scalars ℝ (hf.contDiff (n := 1))
  -- `f = star ∘ (star ∘ f)` because conjugation is an involution
  have hkey : star ∘ (star ∘ f) = f := by
    funext z
    simp [Function.comp_apply]
  rw [← hkey]
  exact contDiff_one_star.comp hgr

end Work.MRMT.Found
