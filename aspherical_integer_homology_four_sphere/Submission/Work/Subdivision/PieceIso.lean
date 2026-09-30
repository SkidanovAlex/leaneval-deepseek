/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.PieceQuot
import Submission.Work.Subdivision.sdPieceMapLin_bijective
import Submission.Work.Subdivision.sdPieceMapLin_comm
import Submission.Work.Subdivision.cellPieceCoeffF_bijective
import Submission.Work.Subdivision.subdivCpt_mem_top
import Submission.Work.Subdivision.SkelLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The pieces of a skeletal level as chain complexes

The two piece quotient maps of `PieceQuot.lean`
(`sdPieceMapLin`, `cellPieceCoeffF`) assemble, degree by degree, into chain maps

* `PolyCW.sdPieceMap : locCx P a ⟶ (sdPiece P n E a).quot`, whose value on the
  class of a chain supported below `a` is again that class, and
* `PolyCW.cellPieceMap : unitCx (n+1) ⟶ (cellPiece P hdd n E a).quot`, sending the
  generator to the class of the new cell `a`.

Each has invertible components, hence is an isomorphism; this is the level-wise
form of the decomposition of the graded piece of the subdivision as the direct
sum, over the `(n+1)`-cells, of the local complexes `locCx P a`.

The cell side is built with `HomologicalComplex.mkHomFromSingle`, so that its
value on the generator in degree `n+1` is computed by
`HomologicalComplex.mkHomFromSingle_f`, and the factor
`HomologicalComplex.singleObjXSelf` is only ever applied to elements of the
special form `singleObjXSelf.inv y`.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The subdivided piece -/

/-- The identification of the subdivided piece with the local complex, as a chain
map. -/
noncomputable def sdPieceMap (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1) :
    locCx P a ⟶ (sdPiece P n E a).quot :=
  ChainComplex.ofHom (fun k => ModuleCat.ofHom (sdPieceMapLin P n E ha k))
    (fun k => sdPieceMapLin_comm P n E ha k)

@[simp] theorem sdPieceMap_f (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1)
    (k : ℕ) : (sdPieceMap P n E a ha).f k = ModuleCat.ofHom (sdPieceMapLin P n E ha k) := rfl

theorem sdPieceMap_isIso (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1)
    (hE : a ∉ E) : IsIso (sdPieceMap P n E a ha) := by
  haveI hf : ∀ k, IsIso ((sdPieceMap P n E a ha).f k) := fun k => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact sdPieceMapLin_bijective P n E ha hE k
  exact HomologicalComplex.Hom.isIso_of_components (sdPieceMap P n E a ha)

/-- **The subdivided piece is the local complex of the new cell.** -/
noncomputable def sdPieceIso (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1)
    (hE : a ∉ E) : (sdPiece P n E a).quot ≅ locCx P a := by
  haveI := sdPieceMap_isIso P n E a ha hE
  exact (asIso (sdPieceMap P n E a ha)).symm

@[simp] theorem sdPieceIso_inv (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1)
    (hE : a ∉ E) : (sdPieceIso P n E a ha hE).inv = sdPieceMap P n E a ha := rfl

/-- The value of `sdPieceIso` on the image of the forward map. -/
theorem sdPieceIso_apply (n : ℕ) (E : Finset P.Cell) (a : P.Cell) (ha : P.dim a = n + 1)
    (hE : a ∉ E) (k : ℕ) (x : (locCx P a).X k) :
    (sdPieceIso P n E a ha hE).hom.f k ((sdPieceMap P n E a ha).f k x) = x := by
  have h : (sdPieceIso P n E a ha hE).inv.f k ≫ (sdPieceIso P n E a ha hE).hom.f k =
      (𝟙 ((locCx P a).X k) : (locCx P a).X k ⟶ (locCx P a).X k) := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [← sdPieceIso_inv P n E a ha hE, ← ModuleCat.comp_apply, h, ModuleCat.id_apply]

/-! ### The cellular piece -/

/-- The inclusion of the one-dimensional model complex into the cellular piece,
sending the generator to the class of the new cell. -/
noncomputable def cellPieceMap (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    (ha : P.dim a = n + 1) : unitCx (n + 1) ⟶ (cellPiece P hdd n E a).quot :=
  HomologicalComplex.mkHomFromSingle (K := (cellPiece P hdd n E a).quot) (j := n + 1)
    (A := unitMod) (cellPieceCoeffF P hdd n E ha)
    (fun k hk => by
      haveI : Subsingleton ((cellPiece P hdd n E a).quot.X k) :=
        cellPiece_subsingleton P hdd n E a (by
          have h2 : k + 1 = n + 1 := hk
          omega)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)

/-- In degree `n+1` the cellular piece map is `singleObjXSelf.hom` composed with
the coefficient map. -/
theorem cellPieceMap_f_succ (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    (ha : P.dim a = n + 1) :
    (cellPieceMap P hdd n E a ha).f (n + 1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) (n + 1) unitMod).hom ≫
        cellPieceCoeffF P hdd n E ha :=
  HomologicalComplex.mkHomFromSingle_f _ _

theorem cellPieceMap_isIso (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    (ha : P.dim a = n + 1) (hE : a ∉ E) : IsIso (cellPieceMap P hdd n E a ha) := by
  have coeff : IsIso (cellPieceCoeffF P hdd n E ha) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact cellPieceCoeffF_bijective P hdd n E ha hE
  haveI hf : ∀ k, IsIso ((cellPieceMap P hdd n E a ha).f k) := fun k => by
    by_cases hk : k = n + 1
    · rw [hk, cellPieceMap_f_succ]
      infer_instance
    · rw [ConcreteCategory.isIso_iff_bijective]
      haveI : Subsingleton ((unitCx (n + 1)).X k) := unitCx_subsingleton hk
      haveI : Subsingleton ((cellPiece P hdd n E a).quot.X k) :=
        cellPiece_subsingleton P hdd n E a hk
      refine ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components (cellPieceMap P hdd n E a ha)

/-- **The cellular piece is the one-dimensional model complex.** -/
noncomputable def cellPieceIso (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    (ha : P.dim a = n + 1) (hE : a ∉ E) : (cellPiece P hdd n E a).quot ≅ unitCx (n + 1) := by
  haveI := cellPieceMap_isIso P hdd n E a ha hE
  exact (asIso (cellPieceMap P hdd n E a ha)).symm

@[simp] theorem cellPieceIso_inv (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    (ha : P.dim a = n + 1) (hE : a ∉ E) :
    (cellPieceIso P hdd n E a ha hE).inv = cellPieceMap P hdd n E a ha := rfl

/-- The value of `cellPieceIso` on the image of the forward map. -/
theorem cellPieceIso_apply (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (a : P.Cell)
    (ha : P.dim a = n + 1) (hE : a ∉ E) (k : ℕ) (x : (unitCx (n + 1)).X k) :
    (cellPieceIso P hdd n E a ha hE).hom.f k ((cellPieceMap P hdd n E a ha).f k x) = x := by
  have h : (cellPieceIso P hdd n E a ha hE).inv.f k ≫
      (cellPieceIso P hdd n E a ha hE).hom.f k =
        (𝟙 ((unitCx (n + 1)).X k) : (unitCx (n + 1)).X k ⟶ (unitCx (n + 1)).X k) := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [← cellPieceIso_inv P hdd n E a ha hE, ← ModuleCat.comp_apply, h, ModuleCat.id_apply]

end PolyCW

end

end Work.Subdivision
