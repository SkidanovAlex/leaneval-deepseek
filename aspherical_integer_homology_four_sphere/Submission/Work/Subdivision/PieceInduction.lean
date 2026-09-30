/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.LevelMap
import Submission.Work.Subdivision.PieceSquare
import Submission.Work.Subdivision.SubDataEq
import Submission.Work.Subdivision.ComapChainIso
import Submission.Work.Subdivision.comapChain_comm
import Submission.Work.Subdivision.SubDataQuasiIso
import Submission.Work.Subdivision.SkelInduction

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cell-by-cell induction for the refined filtrations

This file proves that the subdivision restricted to the refined filtrations
(`PolyCW.levelMap`) is a quasi-isomorphism for every finite set `E` of `(n+1)`-cells
of a `PolyCW`, assuming the per-cell condition `LocallySpherical`.  The induction
is on `E`: adjoining a cell `a` splits the maps by the five lemma
(`Work.Subdivision.quasiIso_of_sub_quot`) into the statement for the smaller set
(the induction hypothesis, transported through `SubData.comapChainIso`) and the
map on the successive quotients, which is the local map of `a`
(`PolyCW.cellPiece_quotMap_eq_locMap`) and hence a quasi-isomorphism by
`PolyCW.LocallySpherical`.  The two endpoints `E = ∅` and `E = P.faces (n+1)`
are the skeletal restrictions `subdivSkel n` and `subdivSkel (n+1)`
(`LevelMap.quasiIso_levelMap_empty_iff`, `LevelMap.quasiIso_levelMap_faces_iff`).
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

section

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

/-- **Naturality of the transport isomorphisms of `SubData.comapChain`.**
The restriction of a chain map to relative subcomplexes is intertwined with the
canonical isomorphism identifying a `comapChain` with its base subcomplex. -/
theorem comapChainIso_restrictMap_comm (S : SubData C) (T : ∀ k, Submodule ℤ (C.X k))
    (hT : ∀ k, T k ≤ S.sub k)
    (hTd : ∀ k (x : C.X (k + 1)), x ∈ T (k + 1) → (C.d (k + 1) k).hom x ∈ T k)
    (S' : SubData C') (T' : ∀ k, Submodule ℤ (C'.X k))
    (hT' : ∀ k, T' k ≤ S'.sub k)
    (hT'd : ∀ k (x : C'.X (k + 1)), x ∈ T' (k + 1) → (C'.d (k + 1) k).hom x ∈ T' k)
    (f : C ⟶ C') (hfS : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (hf : ∀ k, T k ≤ (T' k).comap (f.f k).hom) :
    (S.comapChainIso T hT hTd).hom ≫
        (SubData.mk T hTd).restrictMap (SubData.mk T' hT'd) f hf =
      (S.comapChain T hT hTd).restrictMap (S'.comapChain T' hT' hT'd)
          (S.restrictMap S' f hfS)
          (fun k x hx => by
            show (((S.restrictMap S' f hfS).f k x : ↥(S'.sub k)) : C'.X k) ∈ T' k
            exact hf k (Submodule.mem_comap.mp hx)) ≫
        (S'.comapChainIso T' hT' hT'd).hom := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [show (S.comapChainIso T hT hTd).hom.f k = ModuleCat.ofHom
      ((Submodule.comapSubtypeEquivOfLe (hT k)).toLinearMap :
        ↥((S.comapChain T hT hTd).sub k) →ₗ[ℤ] ↥(T k)) from rfl]
  rw [show (S'.comapChainIso T' hT' hT'd).hom.f k = ModuleCat.ofHom
      ((Submodule.comapSubtypeEquivOfLe (hT' k)).toLinearMap :
        ↥((S'.comapChain T' hT' hT'd).sub k) →ₗ[ℤ] ↥(T' k)) from rfl]
  show (f.f k) ((Submodule.comapSubtypeEquivOfLe (hT k)) x : C.X k) =
    (f.f k) (x : C.X k)
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe]


end

namespace PolyCW

variable (P : PolyCW.{u})

/-- The comap-chain presentation of the cellular piece. -/
noncomputable abbrev cellPieceComap (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell)
    (a : P.Cell) : SubData ((cellTop P hdd n (insert a E)).chain) :=
  SubData.comapChain (cellTop P hdd n (insert a E)) (cellTopMod P hdd n E)
    (fun k => cellTopMod_mono P hdd n (Finset.subset_insert a E) k)
    (cellTop P hdd n E).d_mem

/-- The comap-chain presentation of the subdivided piece. -/
noncomputable abbrev sdPieceComap (n : ℕ) (E : Finset P.Cell)
    (a : P.Cell) : SubData ((sdTop P n (insert a E)).chain) :=
  SubData.comapChain (sdTop P n (insert a E)) (sdTopMod P n E)
    (fun k => sdTopMod_mono P n (Finset.subset_insert a E) k)
    (sdTop P n E).d_mem

theorem cellPiece_eq_comap (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell) :
    cellPieceComap P hdd n E a = cellPiece P hdd n E a :=
  SubData.ext fun k => rfl

theorem sdPiece_eq_comap (n : ℕ) (E : Finset P.Cell) (a : P.Cell) :
    sdPieceComap P n E a = sdPiece P n E a :=
  SubData.ext fun k => rfl

/-- **The induction step of the cell-by-cell induction.**  If the subdivision is
a quasi-isomorphism on the refined filtration of `E`, and the local condition
holds, then it is one on the refined filtration of `insert a E`. -/
theorem quasiIso_levelMap_insert (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1) (hE : a ∉ E)
    (ih : QuasiIso (levelMap P hdd haug n E)) (hsp : LocallySpherical P hdd haug) :
    QuasiIso (levelMap P hdd haug n (insert a E)) := by
  have hlevel : QuasiIso ((SubData.mk (cellTopMod P hdd n E) (cellTop P hdd n E).d_mem).restrictMap
      (SubData.mk (sdTopMod P n E) (sdTop P n E).d_mem) (subdiv P hdd haug)
      (levelHf P hdd haug n E)) := ih
  have hpiece : QuasiIso ((cellPieceComap P hdd n E a).restrictMap
      (sdPieceComap P n E a) (levelMap P hdd haug n (insert a E))
      (cellPiece_hf P hdd haug n E a ha)) :=
    quasiIso_of_iso_square
      (SubData.comapChainIso (cellTop P hdd n (insert a E)) (cellTopMod P hdd n E)
        (fun k => cellTopMod_mono P hdd n (Finset.subset_insert a E) k)
        (cellTop P hdd n E).d_mem)
      (SubData.comapChainIso (sdTop P n (insert a E)) (sdTopMod P n E)
        (fun k => sdTopMod_mono P n (Finset.subset_insert a E) k)
        (sdTop P n E).d_mem)
      ((SubData.mk (cellTopMod P hdd n E) (cellTop P hdd n E).d_mem).restrictMap
        (SubData.mk (sdTopMod P n E) (sdTop P n E).d_mem) (subdiv P hdd haug)
        (levelHf P hdd haug n E))
      ((cellPieceComap P hdd n E a).restrictMap (sdPieceComap P n E a)
        (levelMap P hdd haug n (insert a E)) (cellPiece_hf P hdd haug n E a ha))
      (comapChainIso_restrictMap_comm (cellTop P hdd n (insert a E)) (cellTopMod P hdd n E)
        (fun k => cellTopMod_mono P hdd n (Finset.subset_insert a E) k)
        (cellTop P hdd n E).d_mem
        (sdTop P n (insert a E)) (sdTopMod P n E)
        (fun k => sdTopMod_mono P n (Finset.subset_insert a E) k)
        (sdTop P n E).d_mem
        (subdiv P hdd haug) (levelHf P hdd haug n (insert a E)) (levelHf P hdd haug n E))
      hlevel
  have h₁ : QuasiIso ((cellPiece P hdd n E a).restrictMap (sdPiece P n E a)
      (levelMap P hdd haug n (insert a E)) (cellPiece_hf P hdd haug n E a ha)) :=
    (SubData.quasiIso_of_sub_data_eq (cellPiece P hdd n E a) (cellPieceComap P hdd n E a)
      (sdPiece P n E a) (sdPieceComap P n E a) (cellPiece_eq_comap P hdd n E a).symm
      (sdPiece_eq_comap P n E a).symm (levelMap P hdd haug n (insert a E))
      (cellPiece_hf P hdd haug n E a ha) (cellPiece_hf P hdd haug n E a ha)).mpr hpiece
  have h₃ : QuasiIso ((cellPiece P hdd n E a).quotMap (sdPiece P n E a)
      (levelMap P hdd haug n (insert a E)) (cellPiece_hf P hdd haug n E a ha)) :=
    quasiIso_of_iso_square (cellPieceIso P hdd n E a ha hE) (sdPieceIso P n E a ha hE)
      (locMapAux P hdd haug (n + 1) ⟨a, ha⟩)
      ((cellPiece P hdd n E a).quotMap (sdPiece P n E a) (levelMap P hdd haug n (insert a E))
        (cellPiece_hf P hdd haug n E a ha))
      (cellPiece_quotMap_eq_locMap P hdd haug n E a ha hE).symm
      (locMapAux_quasiIso P hdd haug hsp (n + 1) ⟨a, ha⟩)
  exact quasiIso_of_sub_quot (cellPiece P hdd n E a) (sdPiece P n E a)
    (levelMap P hdd haug n (insert a E)) (cellPiece_hf P hdd haug n E a ha)
    (incl_proj _) (incl_proj _) h₁ h₃

/-- **The cell-by-cell induction.**  Assuming the per-cell local condition, the
restriction of the subdivision to the refined filtrations of `E` is a
quasi-isomorphism for every set `E` of `(n+1)`-cells. -/
theorem quasiIso_levelMap_of_local (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (hsp : LocallySpherical P hdd haug) (ih : QuasiIso (subdivSkel P hdd haug n)) :
    ∀ E : Finset P.Cell, E ⊆ P.faces (n + 1) → QuasiIso (levelMap P hdd haug n E) := by
  intro E
  refine Finset.induction_on E ?_ ?_
  · intro _
    exact (quasiIso_levelMap_empty_iff P hdd haug n).mp ih
  · intro a E hE ih hsub
    have hsub' : E ⊆ P.faces (n + 1) := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have ha : P.dim a = n + 1 := (P.mem_faces (n + 1) a).1 (hsub (Finset.mem_insert_self a E))
    exact quasiIso_levelMap_insert P hdd haug n E a ha hE (ih hsub') hsp

/-- **The skeletal induction.**  Assumning the per-cell local condition, the
subdivision is a quasi-isomorphism on every skeleton. -/
theorem subdivSkel_quasiIso_of_local (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (hsp : LocallySpherical P hdd haug) :
    ∀ n : ℕ, QuasiIso (subdivSkel P hdd haug n) := by
  intro n
  induction n with
  | zero => exact subdivSkel_zero P hdd haug
  | succ n ih =>
      exact (quasiIso_levelMap_faces_iff P hdd haug n).mpr
        (quasiIso_levelMap_of_local P hdd haug n hsp ih (P.faces (n + 1)) (fun _ hx => hx))

/-- **The subdivision chain map is a quasi-isomorphism**, derived from the
per-cell local condition `LocallySpherical`. -/
theorem subdiv_quasiIso_of_local (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (hsp : LocallySpherical P hdd haug) : QuasiIso (subdiv P hdd haug) :=
  quasiIso_subdiv_of_maxDim P hdd haug (subdivSkel_quasiIso_of_local P hdd haug hsp P.maxDim)

end PolyCW

end

end Work.Subdivision
