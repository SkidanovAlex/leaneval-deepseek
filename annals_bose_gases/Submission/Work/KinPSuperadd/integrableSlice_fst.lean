import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

open MeasureTheory
open Submission BoseGases

/-- **First-block slice integrability of the squared `Qⱼ` field.**

For a continuous `Φ : X (N₁+N₂) → ℝ`, the function of the *second* block

    w ↦ ∫_{u ∈ abox N₁ s} (Qⱼ Φ (mergeBlock N₁ N₂ (u,w)))²

is integrable over the centred box `abox N₂ s` (the index `j` living in the
*first* block, `i = Fin.castAdd N₂ j`).

This is the slice-integrability hypothesis (`SlotSplit.int₁`) in the case where
the slicing coordinate belongs to the first block.  The proof is the
measure-preserving block split of `abox (N₁+N₂) s`: `QⱼΦ²` is integrable over
the full centred box (`integrableOn_sq_aQ`), the block split
`aboxSplit_measurePreserving_restrict` carries this to the product of the two
block boxes, and Fubini for integrable functions
(`Integrable.integral_prod_right`) integrates out the first block. -/
theorem integrableSlice_fst {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) (j : Fin N1)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun w : Submission.BoseGases.X N2 =>
      ∫ u in Submission.BoseGases.abox N1 s,
        (@Submission.BoseGases.aQ s (N1 + N2) (Fin.castAdd N2 j) Φ
          (Submission.BoseGases.mergeBlock N1 N2 (u, w)))^2)
      (Submission.BoseGases.abox N2 s) MeasureTheory.volume := by
  have hGint : IntegrableOn
      (fun x : X (N1 + N2) =>
        (@aQ s (N1 + N2) (Fin.castAdd N2 j) Φ x) ^ 2)
      (abox (N1 + N2) s) volume :=
    integrableOn_sq_aQ hs (Fin.castAdd N2 j) hΦ
  have hmp := aboxSplit_measurePreserving_restrict N1 N2 s
  have hGe : Integrable
      (fun p : X N1 × X N2 =>
        (@aQ s (N1 + N2) (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 p)) ^ 2)
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
    apply (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding).mp
    refine hGint.congr ?_
    filter_upwards with x
    simp [Function.comp_apply, blockSplitEquiv_apply, mergeBlock_eq]
  exact hGe.integral_prod_right

end Work.KinPSuperadd
