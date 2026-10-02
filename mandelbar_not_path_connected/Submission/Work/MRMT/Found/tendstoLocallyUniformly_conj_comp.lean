import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.tendstoLocallyUniformly_comp_comp
import Submission.Work.MRMT.Found.tendstoLocallyUniformly_conj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

theorem tendstoLocallyUniformly_conj_comp {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ)
    {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    TendstoLocallyUniformly
      (fun n => star ∘ (d.Fn n : ℂ → ℂ) ∘ f ∘ (((d.Fn n).symm : ℂ ≃ₜ ℂ) : ℂ → ℂ))
      (star ∘ (d.φ : ℂ → ℂ) ∘ f ∘ (((d.φ).symm : ℂ ≃ₜ ℂ) : ℂ → ℂ)) Filter.atTop := by
  exact tendstoLocallyUniformly_conj d (ContDiff.continuous hf)

end Work.MRMT.Found
