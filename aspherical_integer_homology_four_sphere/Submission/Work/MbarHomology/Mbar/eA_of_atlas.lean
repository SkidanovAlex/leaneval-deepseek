import Mathlib
import Submission.Work.MbarHomology.Mbar.Assemble
import Submission.Work.MbarHomology.CellAtlas.zMap_quasiIso
import Submission.Work.HomologyIso.Gen.Models
import Submission.Work.PieceHomology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.Mbar

/-- **The homology of `M̄`, as the `eA` input of `Work.PieceHomology.cuspData_of_concrete`**
(work package W7 of `Submission/Work/NOTES_LEAD_eA.md`).

Assembly from the ingredients of this area:

* `CellAtlas.zMap_quasiIso A hdd haug hsp h : QuasiIso (A.zMap h)` compares the `Δ`-chain complex
  of `mbarSd` with `Gen.mbarCx`;
* `Work.HomologyIso.Gen.mbarCx_homology_modelA k : Nonempty (mbarCx.homology k ≅ ModelA (k:ℤ))`
  gives the other half, so `mbarSd.chain.homology k ≅ ModelA (k:ℤ)`;
* `Work.PieceHomology.DeltaModel.ofHatcher mbarReal (…)` (Hatcher 2.27, already delivered) turns
  the realization `mbarReal` (`Mbar/Assemble.lean`) into the identification with
  `LeanEval.Topology.intHomology k (TopCat.of Work.FoldInst.Mbar)`.

Note `Work.RTInstance.assemblyOf` sets `Mbar := Work.FoldInst.Mbar`, so this is exactly the `hmbar`
argument of `Work.PieceHomology.cuspData_of_concrete`. -/
theorem eA_of_atlas (A : Work.MbarHomology.CellAtlas Work.MbarHomology.mbarSd Work.MbarHomology.QbarCW Work.HomologyIso.Gen.mbarCx) (hdd : Work.MbarHomology.QbarCW.HasDdZero) (haug : Work.MbarHomology.QbarCW.HasAugZero) (hsp : Work.MbarHomology.QbarCW.LocallySpherical hdd haug) (h : A.BoundaryCompat) (k : ℕ) : Nonempty (Work.HomologyIso.ModelA (k : ℤ) ≅ LeanEval.Topology.intHomology k (TopCat.of Work.FoldInst.Mbar)) := by
  -- The atlas comparison `A.zMap h : Gen.mbarCx.toChainComplex ⟶ mbarSd.chain` is a
  -- quasi-isomorphism, so it is an isomorphism on homology in every degree.
  have hq := Work.MbarHomology.CellAtlas.zMap_quasiIso A hdd haug hsp h
  -- The homology of the `Δ`-chain complex of `mbarSd`, computed through `Gen.mbarCx`.
  have e : (k : ℕ) → Work.MbarHomology.mbarSd.chain.homology k
      ≅ Work.HomologyMV.freeMod (Work.HomologyIso.rankA (k : ℤ)) :=
    fun k => (CategoryTheory.asIso
        (HomologicalComplex.homologyMap (A.zMap h) k)).symm
      ≪≫ (Work.HomologyIso.Gen.mbarCx_homology_modelA k).some
  -- Hatcher 2.27 (via the realization `mbarReal`) turns this into the identification with
  -- the singular homology of `M̄`.
  exact ⟨(Work.PieceHomology.DeltaModel.ofHatcher Work.MbarHomology.mbarReal e).iso k⟩

end Work.MbarHomology.Mbar
