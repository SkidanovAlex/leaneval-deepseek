import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Slice Fubini on the merged analysis box (`slice_fubini`)

For an integrable `G` on the centred `(N₁+N₂)`-box, the block-split of
`abox (N₁+N₂) s` into `abox N₁ s × abox N₂ s` (`blockSplitEquiv`,
`aboxSplit_measurePreserving_restrict`, `Submission.Work.AboxBlockSplit`) turns
the integral of `G` into an iterated integral of `G ∘ mergeBlock`, in *both*
orders, and the partial integrals are integrable on the corresponding block
box.

* the two integrability claims are `Integrable.integral_prod_right` applied to
  the measure-transported integrability `abox_prod_integrable` (in the second
  order, after `Integrable.swap`);
* the two identities are exactly `aboxFubini` / `aboxFubini_swapped`.

This is the analytic input the `SlotSplit`-engine consumes: it makes the slice
integrals in the block decomposition of a word meaningful.
-/

namespace Work.KinPSuperadd

open MeasureTheory
open Submission BoseGases

theorem slice_fubini {N1 N2 : ℕ} (s : ℝ) {G : Submission.BoseGases.X (N1 + N2) → ℝ}
    (hG : MeasureTheory.IntegrableOn G (Submission.BoseGases.abox (N1 + N2) s) MeasureTheory.volume) :
    (MeasureTheory.IntegrableOn
        (fun w : Submission.BoseGases.X N2 => ∫ u in Submission.BoseGases.abox N1 s,
          G (Submission.BoseGases.mergeBlock N1 N2 (u, w)))
        (Submission.BoseGases.abox N2 s) MeasureTheory.volume)
    ∧ (MeasureTheory.IntegrableOn
        (fun u : Submission.BoseGases.X N1 => ∫ w in Submission.BoseGases.abox N2 s,
          G (Submission.BoseGases.mergeBlock N1 N2 (u, w)))
        (Submission.BoseGases.abox N1 s) MeasureTheory.volume)
    ∧ (∫ w in Submission.BoseGases.abox N2 s, ∫ u in Submission.BoseGases.abox N1 s,
          G (Submission.BoseGases.mergeBlock N1 N2 (u, w))
        = ∫ x in Submission.BoseGases.abox (N1 + N2) s, G x)
    ∧ (∫ u in Submission.BoseGases.abox N1 s, ∫ w in Submission.BoseGases.abox N2 s,
          G (Submission.BoseGases.mergeBlock N1 N2 (u, w))
        = ∫ x in Submission.BoseGases.abox (N1 + N2) s, G x) := by
  have hGe : Integrable (fun p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2 =>
      G (Submission.BoseGases.mergeBlock N1 N2 p))
      ((volume.restrict (Submission.BoseGases.abox N1 s)).prod
        (volume.restrict (Submission.BoseGases.abox N2 s))) :=
    Submission.BoseGases.abox_prod_integrable s G hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hGe.integral_prod_right
  · have hQ : Integrable
        (fun q : Submission.BoseGases.X N2 × Submission.BoseGases.X N1 =>
          G (Submission.BoseGases.mergeBlock N1 N2 q.swap))
        ((volume.restrict (Submission.BoseGases.abox N2 s)).prod
          (volume.restrict (Submission.BoseGases.abox N1 s))) := by
      simpa [Function.comp_def, Prod.swap_prod_mk] using hGe.swap
    exact hQ.integral_prod_right
  · exact Submission.BoseGases.aboxFubini_swapped s G hG
  · exact Submission.BoseGases.aboxFubini s G hG

end Work.KinPSuperadd
