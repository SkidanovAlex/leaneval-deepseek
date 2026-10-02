import Mathlib
import Submission.Work.Serre.SPC.One.Pieces
import Submission.Work.Serre.SPC.One.discPairStrong
import Submission.Work.Serre.SPC.One.ModelCompress
import Submission.Work.Serre.SPC.One.pieceTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.SPC.One

theorem pieceChainMap_strong (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → ContinuousMap Work.Serre.SPC.cellS0 Y)
    (X : Type) [TopologicalSpace X] (q : ContinuousMap X (Work.Serre.SPC.attachOneCells Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (hfib : ∀ y : Work.Serre.SPC.attachOneCells Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.Serre.SPC.attachOneCells Y ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ)))
    (i : ι) :
    (∀ m : ℕ, m < 1 + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.One.pieceChainMap Y ι f q i) m)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.One.pieceChainMap Y ι f q i) (1 + φ)).hom := by
  have hmodel := pmMapOne_punctDisc_strong q hq (oneCellMap Y ι f i) φ
    (fun y j hj hjφ => hfib (oneCellMap Y ι f i y) j hj hjφ)
    (fun y => h0 (oneCellMap Y ι f i y))
  exact ⟨fun m hm =>
      (pieceChainMap_iso_iff_model (f := f) (q := q) i m).mpr (hmodel.1 m hm),
    (pieceChainMap_surjective_iff_model (f := f) (q := q) i (1 + φ)).mpr hmodel.2⟩

end Work.Serre.SPC.One
