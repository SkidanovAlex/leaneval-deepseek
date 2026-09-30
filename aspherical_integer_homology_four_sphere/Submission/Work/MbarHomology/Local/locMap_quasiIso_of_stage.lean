/-
# The stage criterion for the local map of a cell

For a `PolyCW` `P`, a cell `a` and a *stage* `T` of `a` (`PolyCW.IsStage`, `SupportCx.lean`), the
subdivision restricted to the stage `T` and to the stage `insert a T = T ∪ {a}` are related by the
five lemma to the local map of `a`: if the subdivision is a quasi-isomorphism on the smaller stage
`T` and on the larger stage `insert a T`, then it is one on the piece of the new cell, i.e. the
local map `locMap P hdd haug a` is a quasi-isomorphism.

This is the converse of the stage step `PolyCW.stage_step` (`StageInduction.lean`), which produces
the quasi-isomorphism on `insert a T` from the quasi-isomorphism on `T` and the local condition at
`a`.  It is the direction in which the cell-by-cell induction over the localized (star) filtration
is turned into the local condition on every cell, cf. `LocallySpherical`.
-/
import Mathlib
import Submission.Work.MbarHomology.Local.SupportCx
import Submission.Work.MbarHomology.Local.StageCx
import Submission.Work.MbarHomology.Local.StageInduction
import Submission.Work.MbarHomology.Local.stageQuotMap_eq_locMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.MbarHomology.Local

/-- **The stage criterion for the local map.**  If the subdivision is a quasi-isomorphism on a
stage `T` for the cell `a` and on the stage `insert a T` obtained by adjoining `a`, then the local
map of `a` is a quasi-isomorphism.

The proof is the five lemma `quasiIso_quotMap_of_sub` applied to the map on the pieces of the stage
step: the restriction of the subdivided piece to the previous stage is a quasi-isomorphism by
naturality of the transport isomorphisms (`comapChainIso_restrictMap_comm`) applied to the
quasi-isomorphism on `T`, and the map on `insert a T` is one by hypothesis; hence the induced map on
the quotient of the pieces is one.  By `stageQuotMap_eq_locMap` that quotient map differs from the
local map `locMap P hdd haug a` by isomorphisms of its source and target, so the local map is a
quasi-isomorphism as well. -/
theorem locMap_quasiIso_of_stage (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero)
    {T : Finset P.Cell} (a : P.Cell) (h : Work.Subdivision.PolyCW.IsStage P a T)
    (hS : QuasiIso (Work.Subdivision.PolyCW.stageMap P hdd haug T h.lower))
    (hI : QuasiIso (Work.Subdivision.PolyCW.stageMap P hdd haug (insert a T) h.insert_lower)) :
    QuasiIso (Work.Subdivision.PolyCW.locMap P hdd haug a) := by
  have hpieceSub : ∀ m, (Work.Subdivision.PolyCW.cellPieceS P hdd a h).sub m ≤
      ((Work.Subdivision.PolyCW.sdPieceS P a h).sub m).comap
        ((Work.Subdivision.PolyCW.levelMapS P hdd haug a h).f m).hom :=
    Work.Subdivision.PolyCW.cellPieceS_hf P hdd haug a h
  have hlevel : QuasiIso (Work.Subdivision.PolyCW.levelMapS P hdd haug a h) := hI
  -- The restriction of the subdivided piece to the previous stage is a quasi-isomorphism.
  have h₁ : QuasiIso ((Work.Subdivision.PolyCW.cellPieceS P hdd a h).restrictMap
      (Work.Subdivision.PolyCW.sdPieceS P a h) (Work.Subdivision.PolyCW.levelMapS P hdd haug a h)
      hpieceSub) :=
    Work.Subdivision.quasiIso_of_iso_square
      (Work.Subdivision.SubData.comapChainIso
        (Work.Subdivision.PolyCW.cellS P hdd (insert a T) h.insert_lower)
        (Work.Subdivision.PolyCW.cellSMod P hdd T)
        (fun m => Work.Subdivision.PolyCW.cellSMod_mono P hdd (Finset.subset_insert a T) m)
        (Work.Subdivision.PolyCW.cellS P hdd T h.lower).d_mem)
      (Work.Subdivision.SubData.comapChainIso (Work.Subdivision.PolyCW.sdS P (insert a T))
        (Work.Subdivision.PolyCW.sdSMod P T)
        (fun m => Work.Subdivision.PolyCW.sdSMod_mono P (Finset.subset_insert a T) m)
        (Work.Subdivision.PolyCW.sdS P T).d_mem)
      ((Work.Subdivision.PolyCW.cellS P hdd T h.lower).restrictMap
        (Work.Subdivision.PolyCW.sdS P T) (Work.Subdivision.PolyCW.subdiv P hdd haug)
        (Work.Subdivision.PolyCW.subdivCpt_mem_S P hdd haug h.lower))
      ((Work.Subdivision.PolyCW.cellPieceS P hdd a h).restrictMap
        (Work.Subdivision.PolyCW.sdPieceS P a h)
        (Work.Subdivision.PolyCW.levelMapS P hdd haug a h) hpieceSub)
      (Work.Subdivision.comapChainIso_restrictMap_comm
        (Work.Subdivision.PolyCW.cellS P hdd (insert a T) h.insert_lower)
        (Work.Subdivision.PolyCW.cellSMod P hdd T)
        (fun m => Work.Subdivision.PolyCW.cellSMod_mono P hdd (Finset.subset_insert a T) m)
        (Work.Subdivision.PolyCW.cellS P hdd T h.lower).d_mem
        (Work.Subdivision.PolyCW.sdS P (insert a T))
        (Work.Subdivision.PolyCW.sdSMod P T)
        (fun m => Work.Subdivision.PolyCW.sdSMod_mono P (Finset.subset_insert a T) m)
        (Work.Subdivision.PolyCW.sdS P T).d_mem
        (Work.Subdivision.PolyCW.subdiv P hdd haug)
        (Work.Subdivision.PolyCW.subdivCpt_mem_S P hdd haug h.insert_lower)
        (Work.Subdivision.PolyCW.subdivCpt_mem_S P hdd haug h.lower))
      hS
  -- The five lemma: the map on the relative quotient of the pieces is a quasi-isomorphism.
  have h₃ : QuasiIso ((Work.Subdivision.PolyCW.cellPieceS P hdd a h).quotMap
      (Work.Subdivision.PolyCW.sdPieceS P a h) (Work.Subdivision.PolyCW.levelMapS P hdd haug a h)
      hpieceSub) :=
    Work.Subdivision.quasiIso_quotMap_of_sub _ _ _ hpieceSub (Work.Subdivision.incl_proj _)
      (Work.Subdivision.incl_proj _) h₁ hlevel
  -- The quotient map on the pieces is the local map of `a` up to isomorphisms of the models.
  obtain ⟨Φ, Ψ, hsq⟩ := Work.MbarHomology.Local.stageQuotMap_eq_locMap P hdd haug a h
  have hL : Work.Subdivision.PolyCW.locMap P hdd haug a =
      Φ.inv ≫ (Work.Subdivision.PolyCW.stageQuotMap P hdd haug a h ≫ Ψ.hom) := by
    rw [hsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hs : Φ.inv ≫ Work.Subdivision.PolyCW.stageQuotMap P hdd haug a h =
      Work.Subdivision.PolyCW.locMap P hdd haug a ≫ Ψ.inv := by
    rw [hL]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact Work.Subdivision.quasiIso_of_iso_square Φ.symm Ψ.symm
    (Work.Subdivision.PolyCW.stageQuotMap P hdd haug a h) (Work.Subdivision.PolyCW.locMap P hdd haug a)
    hs h₃

end Work.MbarHomology.Local
