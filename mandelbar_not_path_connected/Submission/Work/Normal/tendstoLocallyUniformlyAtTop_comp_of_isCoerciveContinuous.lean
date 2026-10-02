import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

/-- Post-composing a sequence that tends locally uniformly to `∞` with a coercive continuous map
keeps it tending locally uniformly to `∞`. -/
theorem tendstoLocallyUniformlyAtTop_comp_of_isCoerciveContinuous {u : ℕ → ℂ → ℂ} {e : ℂ → ℂ}
    {U : Set ℂ} (he : IsCoerciveContinuous e) (hu : TendstoLocallyUniformlyAtTop u U) :
    TendstoLocallyUniformlyAtTop (fun n => e ∘ u n) U := by
  intro K hKU hK R
  obtain ⟨S, hS⟩ := he.2 R
  obtain ⟨N, hN⟩ := hu K hKU hK S
  exact ⟨N, fun n hn z hz => hS (u n z) (hN n hn z hz)⟩

end Work.Normal
