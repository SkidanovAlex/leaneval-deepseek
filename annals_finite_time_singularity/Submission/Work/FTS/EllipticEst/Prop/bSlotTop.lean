/-
Work module for the Elgindi finite-time singularity project.

# `Prop.bSlotTop`: the `∂_θθΨ`-slot of the `ℋ^k` induction step

This is the clean-cone copy of the `B`-half of `remov.EllEstUnif_top_core` (the paper's
§"General `ℋ^k` case", the top angular slot of `∂_θθΨ`), the last input of `Prop.step`
(see `Submission/Work/FTS/EllipticEst/Prop/NOTES_propHk_assembly.md`).

The proof is `BSlotTop.B_slot_bound_fts`, the mirrored copy of
`Work.FTS.EllipticEst.remov.TopCoreB.B_slot_bound_clean` in which the two `sorry`-carrying
inputs are replaced by proved siblings:

* `remov.TopCoreB.srcBound` ⟶ `BSlotTop.srcBoundFts` (the source slot bound,
  `Submission/Work/FTS/EllipticEst/Prop/BSlotTop/SrcBoundFts.lean`), whose proof rests on the
  `D_θ`-slot recursion `BSlotTop.slotRecAll1` — the variant of `remov.TopCoreB.slotRecAll`
  without the spurious `∂_θ^0` term (the exact expansion
  `D_θ^m f = Σ_{r ≤ m} dthCoef m r ∂_θ^r f` has `dthCoef m 0 = 0` for `m ≥ 1`, so no `f`
  itself is needed), whose surviving summands are all *mixed* slots of `HkIntegrand`;
* `remov.TopCoreB.slice_ang_far` ⟶ `BSlotTop.sliceAngGenFts` (the one-dimensional angular
  estimate, `.../BSlotTop/SliceAngGenFts.lean`), used through `BSlotTop.oneDFts`.  That
  estimate is assembled from the proved `remov.slice_ang_v_outer`, the proved far-half chain
  `remov.slice_ang_v_far_live_of_top` ∘ `remov.farTopXAuxLive_of_top` ∘
  `remov.EllFarTopDiv.sinWeight_xDivX_top_le'` (the top divided slot in the reflected
  variable), and the proved `BSlotTop.sliceAngGenFinalFts`.

Everything else is a proved declaration with a clean import cone (`TT.ESW.*`,
`remov.high_slice_chain_slots`, `remov.TopCoreB.ATopClean`, `TT.ESW.U_le_of_1d`, ...).
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

theorem bSlotTop (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkNorm α k F :=
  Work.FTS.EllipticEst.Prop.BSlotTop.B_slot_bound_fts D hD

end Work.FTS.EllipticEst.Prop
