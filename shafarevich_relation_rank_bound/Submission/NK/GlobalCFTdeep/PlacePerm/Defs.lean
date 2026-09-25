/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.RepresentationTheory.GroupCohomology.piCohomology_injective

/-!
# The permutation module `ℤ[T]` over the fibres above a finite set of places

Let `L / K` be a finite Galois extension of number fields, `G = Gal(L/K)`, `S` a finite set of
places of `K` and `T` the (finite) set of places of `L` lying above the places in `S`.  This file
collects the vocabulary for the decomposition of the permutation module

  `ℤ[T] = Hom(T, ℤ) = ∏_{w ∈ T} ℤ`

(`NK.GlobalCFTdeep.placeFunRep`) along the fibres of the map "place below":

* `fibreSet T v` — the places of `T` lying over `v`;
* `fibreRep T hT v` — `ℤ[fibreSet T v]` as a `ℤ[G]`-module;
* `smul_mem_fibreSet` — `G` preserves each fibre (the fibres are *not* permuted among each
  other, since `LiesOver` is `G`-invariant);
* `exists_smul_eq_of_mem_fibreSet` — `G` acts transitively on each fibre, so a fibre is a single
  orbit, with stabiliser the decomposition group of any of its places.

The two structural results that this vocabulary feeds are proved in the companion files
`PlacePerm/fibreRep_iso_coind.lean` (a single fibre is the coinduced trivial module of its
decomposition group, Shapiro) and `PlacePerm/placeFunRep_iso_piRep.lean` (a function on the
disjoint union `T` of the fibres is a tuple of functions on the fibres), which together give the
Herbrand quotient `∏_{v ∈ S} |D_{w_v}|` in `PlacePerm/herbrandEq_placeFunRep.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.PlacePerm

open NK.GlobalCFT
open NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The fibre of a set of places `T` above the place `v`**: the places of `T` lying over `v`. -/
def fibreSet (T : Set (Place L)) (v : Place K) : Set (Place L) :=
  {w | w ∈ T ∧ Place.LiesOver w v}

theorem mem_fibreSet {T : Set (Place L)} {v : Place K} {w : Place L} :
    w ∈ fibreSet T v ↔ w ∈ T ∧ Place.LiesOver w v := Iff.rfl

/-- The decomposition group of a place `w` is its stabiliser in `Gal(L/K)`. -/
theorem decompositionSubgroup_eq_stabilizer (w : Place L) :
    decompositionSubgroup (K := K) (L := L) w = MulAction.stabilizer (L ≃ₐ[K] L) w := rfl

/-- A `Gal(L/K)`-stable set of places has stable fibres: the action preserves the place below. -/
theorem smul_mem_fibreSet {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (v : Place K) {σ : L ≃ₐ[K] L} {w : Place L} (hw : w ∈ fibreSet T v) :
    σ • w ∈ fibreSet T v :=
  ⟨hT σ hw.1, (Place.liesOver_smul_iff (σ := σ)).mpr hw.2⟩

/-- The place of `K` below a place of `L` is unique, so two fibres of the same set meet only if
they are the same fibre. -/
theorem liesOver_unique_of_mem_fibreSet {T : Set (Place L)} {v v' : Place K} {w : Place L}
    (h : w ∈ fibreSet T v) (h' : w ∈ fibreSet T v') : v = v' :=
  Inclusion.globalCFT_liesOver_unique h.2 h'.2

/-- **The fibre of `T` above `v` as a `ℤ[Gal(L/K)]`-module**: functions on the fibre with the
permutation action. -/
noncomputable def fibreRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (v : Place K) :
    Rep ℤ (L ≃ₐ[K] L) :=
  placeFunRep (K := K) (L := L) (fibreSet T v) (fun σ w hw => smul_mem_fibreSet hT v hw)

theorem fibreRep_def (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (v : Place K) :
    fibreRep T hT v =
      placeFunRep (K := K) (L := L) (fibreSet T v)
        (fun σ w hw => smul_mem_fibreSet hT v hw) := rfl

/-- **The Herbrand quotient is invariant under isomorphisms of representations**: an isomorphism
of `ℤ[G]`-modules induces identifications of both Tate cohomology groups. -/
theorem herbrandEq_of_iso {G : Type} [Group G] [Fintype G] {M N : Rep ℤ G} (e : M ≅ N)
    {m : ℕ} (h : HerbrandEq N m) : HerbrandEq M m := by
  have h0 : Nat.card (tateCohomology M 0) = Nat.card (tateCohomology N 0) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      ((tateCohomologyFunctor (R := ℤ) (G := G) 0).mapIso e)).toEquiv
  have h1 : Nat.card (tateCohomology M 1) = Nat.card (tateCohomology N 1) :=
    Nat.card_congr (CategoryTheory.Iso.toLinearEquiv
      ((tateCohomologyFunctor (R := ℤ) (G := G) 1).mapIso e)).toEquiv
  rw [HerbrandEq, hZero_def, hOne_def] at h ⊢
  rw [h0, h1, h]

section Orbit

variable [FiniteDimensional K L] [IsGalois K L]

/-- The chosen place `w v` above `v ∈ S` does lie in `T`. -/
theorem mem_T_of_liesOver {S : Finset (Place K)} {T : Set (Place L)}
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    {v : Place K} {w₀ : Place L} (hv : v ∈ S) (hw₀ : Place.LiesOver w₀ v) : w₀ ∈ T :=
  (hTS w₀).mpr ⟨v, hv, hw₀⟩

/-- **The action of `Gal(L/K)` on a fibre is transitive**: a fibre of `T` is a single orbit. -/
theorem exists_smul_eq_of_mem_fibreSet {T : Set (Place L)}
    {v : Place K} {w₀ : Place L} (hw₀ : Place.LiesOver w₀ v) {w : Place L}
    (hw : w ∈ fibreSet T v) : ∃ σ : L ≃ₐ[K] L, σ • w₀ = w :=
  Inclusion.globalCFT_exists_smul_eq_of_liesOver hw₀ hw.2

/-- The stabiliser of a place `w₀` (its decomposition group) acts trivially on `w₀`. -/
theorem smul_eq_self_of_mem_decompositionSubgroup {w₀ : Place L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ decompositionSubgroup (K := K) (L := L) w₀) : σ • w₀ = w₀ := hσ

/-- Membership of the decomposition group is fixing the place. -/
theorem mem_decompositionSubgroup_of_smul_eq {w₀ : Place L} {σ : L ≃ₐ[K] L}
    (hσ : σ • w₀ = w₀) : σ ∈ decompositionSubgroup (K := K) (L := L) w₀ := hσ

end Orbit

end NK.GlobalCFTdeep.PlacePerm
