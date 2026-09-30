/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.LevelMap
import Submission.Work.Subdivision.PieceIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The piece maps are the local maps of the cells

The quotient of the refined cellular filtration by the previous stage is the
one-dimensional model complex `unitCx (n+1)` (`PolyCW.cellPieceIso`) and the
quotient of the refined subdivided filtration is the local complex `locCx P a`
(`PolyCW.sdPieceIso`).  This file identifies the map induced by the subdivision
on these quotients with the local map `locMap P hdd haug a` of the cell — the
statement that the subdivision of the new cell generates the top homology of its
local complex.

The proof reduces, by `HomologicalComplex.from_single_hom_ext`, to a single
computation in degree `n+1` on the generator of the model complex, and uses the
fact that `spanMap x ≫ g = spanMap (g x)` (`Work.Subdivision.spanMap_comp`).
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

set_option allowUnsafeReducibility true
attribute [local reducible] PolyCW.cellTop PolyCW.sdTop
attribute [local reducible] PolyCW.cellPiece PolyCW.sdPiece
attribute [local reducible] SubData.quot SubData.quotOf SubData.quotCptMap SubData.quotDcpt
attribute [local reducible] SubData.chain


/-- The generator map is natural in its generator: `spanMap x ≫ g = spanMap (g x)`. -/
theorem spanMap_comp {M N : ModuleCat ℤ} (x : M) (g : M ⟶ N) :
    PolyCW.spanMap x ≫ g = PolyCW.spanMap (M := N) (g x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  show g.hom ((LinearMap.toSpanSingleton (R := ℤ) (M := ↥M) x)
      ((ULift.moduleEquiv (M := ℤ)) z)) =
    (LinearMap.toSpanSingleton (R := ℤ) (M := ↥N) (g x)) ((ULift.moduleEquiv (M := ℤ)) z)
  rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply]
  exact LinearMap.map_smul g.hom ((ULift.moduleEquiv (M := ℤ)) z) x

/-- The value of the map induced on the quotients of a compatible chain map. -/
theorem quotMap_apply_mk {C C' : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C) (S' : SubData C')
    (f : C ⟶ C') (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) (x : C.X k) :
    ((S.quotMap S' f hf).f k) (Submodule.Quotient.mk x : ↥(S.quot.X k)) =
      (Submodule.Quotient.mk ((f.f k) x) : ↥(S'.quot.X k)) :=
  Submodule.mapQ_apply (S.sub k) (S'.sub k) (f.f k).hom (h := hf k) x

namespace PolyCW

variable (P : PolyCW.{u})

/-- The subdivision chain of `a` lies in the refined subdivided filtration at the
stage `insert a E`. -/
theorem subdivCell_mem_sdTopMod_insert (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1) :
    subdivCell P (n + 1) ⟨a, ha⟩ ∈ sdTopMod P n (insert a E) (n + 1) := by
  refine SdTopModInf.mem_of_support P n (insert a E) fun σ hσ => ?_
  have hle := subdivCell_support P (n + 1) ⟨a, ha⟩ σ hσ
  by_cases htop : P.dim (σ (Fin.last (n + 1))) ≤ n
  · exact Or.inl fun i =>
      le_trans (P.dim_le (σ.strictMono.monotone (Fin.le_last i))) htop
  · push_neg at htop
    have hdim : P.dim (σ (Fin.last (n + 1))) = n + 1 := by
      have h := P.dim_le (hle (Fin.last (n + 1)))
      rw [ha] at h
      omega
    refine Or.inr ⟨?_, hdim⟩
    have heq : σ (Fin.last (n + 1)) = a := by
      by_contra hne
      have hlt := P.dim_lt (hle (Fin.last (n + 1))) hne
      rw [hdim, ha] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [heq]
    exact Finset.mem_insert_self a E

/-- The value of the quotient map on the class of the new cell. -/
theorem quotMap_gen (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) (E : Finset P.Cell)
    (a : P.Cell) (ha : P.dim a = n + 1) :
    (((cellPiece P hdd n E a).quotMap (sdPiece P n E a) (levelMap P hdd haug n (insert a E))
        (cellPiece_hf P hdd haug n E a ha)).f (n + 1)) (cellPieceGen P hdd n E ha) =
      (sdPieceMap P n E a ha).f (n + 1)
        (Submodule.Quotient.mk (⟨subdivCell P (n + 1) ⟨a, ha⟩,
          subdivCell_mem_leSub P (n + 1) ⟨a, ha⟩⟩ : ↥(leSub P a (n + 1)))) := by
  have hgen : cellPieceGen P hdd n E ha =
      (Submodule.Quotient.mk (⟨cellElem P hdd (n + 1) ⟨a, ha⟩,
        cellElem_mem_cellTopMod P hdd n (insert a E) (n + 1) ⟨a, ha⟩
          (Finset.mem_insert_self a E) ha⟩ :
        ↑((cellTop P hdd n (insert a E)).chain.X (n + 1))) :
        ↥((cellPiece P hdd n E a).quot.X (n + 1))) := rfl
  rw [hgen, Work.Subdivision.quotMap_apply_mk]
  rw [sdPieceMap_f]
  simp only [ModuleCat.hom_ofHom]
  rw [sdPieceMapLin_apply]
  congr 1
  apply Subtype.ext
  rw [sdInc_apply]
  exact subdiv_apply_single P hdd haug (n + 1) ⟨a, ha⟩

/-- The `n+1`-degree component of a local map, in the form used below. -/
theorem locMapAux_f_eq (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (e : {e : P.Cell // P.dim e = n}) :
    (locMapAux P hdd haug n e).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) n unitMod).hom ≫
        PolyCW.spanMap (locClsAux P n e) := by
  unfold locMapAux
  exact HomologicalComplex.mkHomFromSingle_f _ _

/-- The value of the subdivided piece isomorphism on the class of `subdivCell a`. -/
theorem sdPieceIso_gen (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1)
    (hE : a ∉ E) :
    ((sdPieceIso P n E a ha hE).hom.f (n + 1))
      ((sdPieceMap P n E a ha).f (n + 1)
        (Submodule.Quotient.mk (⟨subdivCell P (n + 1) ⟨a, ha⟩,
          subdivCell_mem_leSub P (n + 1) ⟨a, ha⟩⟩ : ↥(leSub P a (n + 1))))) =
      locClsAux P (n + 1) ⟨a, ha⟩ :=
  sdPieceIso_apply P n E a ha hE (n + 1) _

/-- The element computation underlying
`PolyCW.cellPiece_quotMap_eq_locMap`. -/
theorem quotMap_gen_trans (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) (E : Finset P.Cell)
    (a : P.Cell) (ha : P.dim a = n + 1) (hE : a ∉ E) :
    (sdPieceIso P n E a ha hE).hom.f (n + 1)
      ((((cellPiece P hdd n E a).quotMap (sdPiece P n E a) (levelMap P hdd haug n (insert a E))
        (cellPiece_hf P hdd haug n E a ha)).f (n + 1)) (cellPieceGen P hdd n E ha)) =
      locClsAux P (n + 1) ⟨a, ha⟩ := by
  rw [quotMap_gen P hdd haug n E a ha]
  exact sdPieceIso_gen P n E a ha hE

/-- **The piece map is the local map of the new cell.**  Up to the
identifications `cellPieceIso` and `sdPieceIso`, the map induced by the
subdivision on the successive quotients is `locMapAux` of the new cell. -/
theorem cellPiece_quotMap_eq_locMap (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1) (hE : a ∉ E) :
    ((cellPiece P hdd n E a).quotMap (sdPiece P n E a) (levelMap P hdd haug n (insert a E))
        (cellPiece_hf P hdd haug n E a ha)) ≫ (sdPieceIso P n E a ha hE).hom =
      (cellPieceIso P hdd n E a ha hE).hom ≫ locMapAux P hdd haug (n + 1) ⟨a, ha⟩ := by
  have key : cellPieceMap P hdd n E a ha ≫
      (((cellPiece P hdd n E a).quotMap (sdPiece P n E a) (levelMap P hdd haug n (insert a E))
        (cellPiece_hf P hdd haug n E a ha)) ≫ (sdPieceIso P n E a ha hE).hom) =
      locMapAux P hdd haug (n + 1) ⟨a, ha⟩ := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cellPieceMap_f_succ,
      locMapAux_f_eq, Category.assoc]
    congr 1
    rw [cellPieceCoeffF]
    rw [spanMap_comp]
    congr 1
    rw [ModuleCat.comp_apply]
    exact quotMap_gen_trans P hdd haug n E a ha hE
  calc ((cellPiece P hdd n E a).quotMap (sdPiece P n E a) (levelMap P hdd haug n (insert a E))
        (cellPiece_hf P hdd haug n E a ha)) ≫ (sdPieceIso P n E a ha hE).hom
      = ((cellPieceIso P hdd n E a ha hE).hom ≫ (cellPieceIso P hdd n E a ha hE).inv) ≫
          (((cellPiece P hdd n E a).quotMap (sdPiece P n E a)
            (levelMap P hdd haug n (insert a E))
            (cellPiece_hf P hdd haug n E a ha)) ≫ (sdPieceIso P n E a ha hE).hom) := by
        rw [Iso.hom_inv_id, Category.id_comp]
    _ = (cellPieceIso P hdd n E a ha hE).hom ≫
          (cellPieceMap P hdd n E a ha ≫
            (((cellPiece P hdd n E a).quotMap (sdPiece P n E a)
              (levelMap P hdd haug n (insert a E))
              (cellPiece_hf P hdd haug n E a ha)) ≫ (sdPieceIso P n E a ha hE).hom)) := by
        rw [cellPieceIso_inv, Category.assoc]
    _ = (cellPieceIso P hdd n E a ha hE).hom ≫ locMapAux P hdd haug (n + 1) ⟨a, ha⟩ := by
        rw [key]

end PolyCW

end

end Work.Subdivision
