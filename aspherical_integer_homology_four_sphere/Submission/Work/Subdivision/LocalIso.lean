/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.PieceInduction

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Isomorphic local structures of two cells

The per-cell local condition `PolyCW.LocallySpherical` is a statement about the
*local structure* of a cell: its face lattice `Iic e`, the incidence numbers of
its facets, and the subdivision chains built from them by the cone recursion.
Consequently it is invariant under an isomorphism of that local structure, which
is what lets a certificate be proved once per **face-lattice type** and then
transported to every cell of that type.

This file sets up the two ingredients:

* `PolyCW.starLM φ k` — for an order isomorphism `φ : Iic e ≃o Iic f` of face
  lattices, the induced linear map on the `k`-chains of the order complex:
  simplices all of whose vertices are `≤ e` are mapped vertexwise through `φ`, all
  other simplices to `0`; it commutes with the differential (`starLM_D`) and
  preserves both `leSub` and `ltSub`;
* `PolyCW.LocalIso P e f` — an isomorphism of local structures: an order
  isomorphism of the face lattices preserving the dimension function and the
  incidence numbers of facets, the hypothesis of the transport
  `PolyCW.LocallySpherical.of_localIso`.
-/

/-- The map underlying the restriction of an order isomorphism to a principal
down-set. -/
noncomputable def iicMap {α β : Type*} [Preorder α] [Preorder β] (φ : α ≃o β) (a : α) :
    Set.Iic a → Set.Iic (φ a) := fun x => ⟨φ x.1, φ.monotone x.2⟩

theorem iicMap_apply {α β : Type*} [Preorder α] [Preorder β] (φ : α ≃o β) (a : α)
    (x : Set.Iic a) : (iicMap φ a x).1 = φ x.1 := rfl

/-- An order isomorphism of posets restricts to an order isomorphism of the
principal down-sets. -/
noncomputable def OrderIso.subIic {α β : Type*} [Preorder α] [Preorder β] (φ : α ≃o β) (a : α) :
    Set.Iic a ≃o Set.Iic (φ a) where
  toFun := iicMap φ a
  invFun y := ⟨φ.symm y.1, by
    have h : y.1 ≤ φ a := y.2
    simpa using φ.symm.monotone h⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  map_rel_iff' := by intro x y; exact φ.le_iff_le

@[simp] theorem OrderIso.subIic_apply {α β : Type*} [Preorder α] [Preorder β] (φ : α ≃o β) (a : α)
    (x : Set.Iic a) : (φ.subIic a x).1 = φ x.1 := rfl

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The induced map on chains -/

/-- The simplex obtained by mapping the vertices of a simplex all of whose
vertices are `≤ e` through an order isomorphism of face lattices. -/
noncomputable def Simplex.congrIic {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) {k : ℕ}
    (σ : Simplex P.Cell k) (hσ : ∀ i, σ i ≤ e) : Simplex P.Cell k where
  toFun i := (φ ⟨σ i, hσ i⟩ : Set.Iic f).1
  strictMono := fun i j hij => φ.strictMono (σ.strictMono hij)

@[simp] theorem Simplex.congrIic_apply {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) {k : ℕ}
    (σ : Simplex P.Cell k) (hσ : ∀ i, σ i ≤ e) (i : Fin (k + 1)) :
    Simplex.congrIic P φ σ hσ i = (φ ⟨σ i, hσ i⟩ : Set.Iic f).1 := rfl

theorem Simplex.congrIic_le {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) {k : ℕ}
    (σ : Simplex P.Cell k) (hσ : ∀ i, σ i ≤ e) : ∀ i, Simplex.congrIic P φ σ hσ i ≤ f :=
  fun i => (φ ⟨σ i, hσ i⟩).2

/-- The induced linear map on the `k`-chains: simplices all of whose vertices are
`≤ e` are mapped vertexwise through `φ`, all others to `0`. -/
noncomputable def starLM {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    chainMod P.Cell k →ₗ[ℤ] chainMod P.Cell k :=
  Finsupp.linearCombination ℤ fun σ : Simplex P.Cell k =>
    if h : ∀ i, σ i ≤ e then Finsupp.single (Simplex.congrIic P φ σ h) 1 else 0

theorem starLM_single {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) {k : ℕ} (σ : Simplex P.Cell k)
    (h : ∀ i, σ i ≤ e) :
    starLM P φ k (Finsupp.single σ 1) =
      Finsupp.single (Simplex.congrIic P φ σ h) 1 := by
  rw [starLM, Finsupp.linearCombination_apply]
  simp [h]

/-- The face maps commute with the vertexwise map. -/
theorem Simplex.congrIic_face {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) {k : ℕ}
    (σ : Simplex P.Cell (k + 1)) (hσ : ∀ i, σ i ≤ e) (i : Fin (k + 2)) :
    Simplex.congrIic P φ (Simplex.face i σ) (fun j => hσ (i.succAbove j)) =
      Simplex.face i (Simplex.congrIic P φ σ hσ) := by
  ext t
  rfl

/-- `starLM` commutes with the differential of the order complex. -/
theorem starLM_D {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) {x : chainMod P.Cell (k + 1)}
    (hx : x ∈ leSub P e (k + 1)) :
    starLM P φ k (D (α := P.Cell) k x) = D (α := P.Cell) k (starLM P φ (k + 1) x) := by
  refine Submodule.span_induction (p := fun x _ => starLM P φ k (D (α := P.Cell) k x) =
      D (α := P.Cell) k (starLM P φ (k + 1) x)) ?_ ?_ ?_ ?_ hx
  · intro σ hσ
    obtain ⟨σ, hσ, rfl⟩ := hσ
    rw [starLM_single P φ σ hσ, D_single, D_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, starLM_single P φ (Simplex.face i σ) (fun j => hσ (i.succAbove j)),
      Simplex.congrIic_face]
  · simp
  · intro x y hx hy ihx ihy
    simp only [map_add]
    rw [ihx, ihy]
  · intro a x hx ih
    simp only [map_smul]
    rw [ih]

/-- `starLM` maps chains supported below `e` to chains supported below `f`. -/
theorem starLM_mem_leSub {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    leSub P e k ≤ Submodule.comap (starLM P φ k) (leSub P f k) := by
  rw [leSub, Submodule.span_le]
  rintro x ⟨σ, hσ, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  rw [starLM_single P φ σ hσ]
  exact sdElem_mem_leSub P (Simplex.congrIic_le P φ σ hσ)

/-- `starLM` maps chains supported strictly below `e` to chains supported strictly
below `f`. -/
theorem starLM_mem_ltSub {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) :
    ltSub P e k ≤ Submodule.comap (starLM P φ k) (ltSub P f k) := by
  rw [ltSub, Submodule.span_le]
  rintro x ⟨σ, hσ, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  rw [starLM_single P φ σ (fun i => le_of_lt (hσ i))]
  refine sdElem_mem_ltSub P fun i => ?_
  rw [Simplex.congrIic_apply]
  have h := φ.strictMono (show (⟨σ i, le_of_lt (hσ i)⟩ : Set.Iic e) < ⟨e, le_rfl⟩ from hσ i)
  have htop : (φ ⟨e, le_rfl⟩ : Set.Iic f).1 = f := congrArg Subtype.val (OrderIso.map_top φ)
  calc (φ ⟨σ i, le_of_lt (hσ i)⟩ : Set.Iic f).1 < (φ ⟨e, le_rfl⟩ : Set.Iic f).1 := h
    _ = f := htop

/-- The composite of the vertexwise maps of an order isomorphism and its inverse is
the identity on chains supported below `e`. -/
theorem starLM_symm_apply {e f : P.Cell} (φ : Set.Iic e ≃o Set.Iic f) (k : ℕ) {x : chainMod P.Cell k}
    (hx : x ∈ leSub P e k) :
    starLM P φ.symm k (starLM P φ k x) = x := by
  refine Submodule.span_induction (p := fun x _ => starLM P φ.symm k (starLM P φ k x) = x)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := hy
    rw [starLM_single P φ σ hσ,
      starLM_single P φ.symm (Simplex.congrIic P φ σ hσ) (Simplex.congrIic_le P φ σ hσ)]
    congr 2
    ext t
    simp only [Simplex.congrIic_apply]
    rw [OrderIso.symm_apply_apply]
  · simp
  · intro x y hx hy ihx ihy
    simp only [map_add]
    rw [ihx, ihy]
  · intro a x hx ih
    simp only [map_smul]
    rw [ih]

/-! ### Isomorphisms of local structure -/

/-- **An isomorphism of the local structures of two cells**: an order isomorphism
of their face lattices which preserves dimensions and the incidence numbers of
facets. -/
structure LocalIso (e f : P.Cell) where
  /-- The order isomorphism of the face lattices. -/
  toOrderIso : Set.Iic e ≃o Set.Iic f
  /-- The map on the top cell. -/
  map_top : (toOrderIso ⟨e, le_rfl⟩ : Set.Iic f).1 = f
  /-- It preserves dimensions. -/
  dim_eq : ∀ x : Set.Iic e, P.dim (toOrderIso x).1 = P.dim x.1
  /-- It preserves incidence numbers of facets. -/
  inc_eq : ∀ (x : Set.Iic e) {y : P.Cell} (hy : y ∈ P.facets x.1),
    P.inc x.1 y = P.inc (toOrderIso x).1
      (toOrderIso ⟨y, le_trans (le_of_lt (P.facet_lt hy)) x.2⟩).1

namespace LocalIso

variable {P} {e f : P.Cell}

/-- The underlying order isomorphism, as a function. -/
abbrev toFun (φ : LocalIso P e f) (x : Set.Iic e) : Set.Iic f := φ.toOrderIso x

@[simp] theorem toFun_apply (φ : LocalIso P e f) (x : Set.Iic e) :
    (φ.toFun x : Set.Iic f) = φ.toOrderIso x := rfl

@[simp] theorem toFun_top (φ : LocalIso P e f) : (φ.toFun ⟨e, le_rfl⟩).1 = f := φ.map_top

/-- Strict monotonicity, in the ambient cells. -/
theorem toFun_lt (φ : LocalIso P e f) {x y : Set.Iic e} (h : x < y) :
    (φ.toFun x).1 < (φ.toFun y).1 := φ.toOrderIso.strictMono h

/-- Monotonicity, in the ambient cells. -/
theorem toFun_le (φ : LocalIso P e f) {x y : Set.Iic e} (h : x ≤ y) :
    (φ.toFun x).1 ≤ (φ.toFun y).1 := φ.toOrderIso.monotone h

end LocalIso

variable {e f : P.Cell}

/-- The vertexwise map induced by an isomorphism of local structures. -/
noncomputable abbrev LocalIso.congrIic (φ : LocalIso P e f) {k : ℕ} (σ : Simplex P.Cell k)
    (hσ : ∀ i, σ i ≤ e) : Simplex P.Cell k := PolyCW.Simplex.congrIic P φ.toOrderIso σ hσ

/-- The linear map on chains induced by an isomorphism of local structures. -/
noncomputable abbrev LocalIso.starLM (φ : LocalIso P e f) (k : ℕ) :
    chainMod P.Cell k →ₗ[ℤ] chainMod P.Cell k := PolyCW.starLM P φ.toOrderIso k

end PolyCW

end

end Work.Subdivision

