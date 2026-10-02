/-
Work.MRMT.Found — formerly a *copy* of `Work.MRMT.QC.eq_zero_of_beltrami_of_decay` (its
helpers plus the headline theorem under the name `…_aux`).  The copy duplicated 55 helper
declarations and collided with the original, so this module is now a thin re-export: the
helpers come from the original module, and the historical name `…_aux` is kept as an alias.
-/
import Submission.Work.MRMT.QC.eq_zero_of_beltrami_of_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function

namespace Work.MRMT.QC

theorem eq_zero_of_beltrami_of_decay_aux {h : ℂ → ℂ} {μ : ℂ → ℂ} {k : ℝ}
    (hf : Continuous h) (hW : Work.MRMT.HasW12LocOn h Set.univ) (hk : k < 1)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Work.MRMT.dzbar h z = μ z * Work.MRMT.dz h z)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) :
    h = 0 :=
  eq_zero_of_beltrami_of_decay hf hW hk hb hrel hdec

end Work.MRMT.QC
