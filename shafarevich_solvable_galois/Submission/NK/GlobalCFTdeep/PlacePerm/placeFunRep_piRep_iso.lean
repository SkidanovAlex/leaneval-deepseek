import Mathlib
import Submission.NK.GlobalCFTdeep.PlacePerm.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ℤ[T]` is the product of its fibre modules

Let `L / K` be an extension of number fields, `G = Gal(L/K)`, `S` a finite set of places of `K`
and `T` a `G`-stable set of places of `L` consisting exactly of the places above the places in
`S`.  Since the place of `K` below a place of `L` is unique
(`NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`), `T` is the *disjoint* union of the fibres

  `fibreSet T v = {w ∈ T | LiesOver w v}`,  `v ∈ S`,

and `G` preserves each fibre individually (`Place.liesOver_smul_iff`).  Hence a function on the
disjoint union `T` is the same thing as a tuple of functions on the parts:

  `ℤ[T] = Hom(T, ℤ) ≅ ∏_{v ∈ S} Hom(fibreSet T v, ℤ)`   as `ℤ[G]`-modules,

the action on the right hand side being the pointwise (diagonal) one.  This is the module-level
input to the computation of the Herbrand quotient of `ℤ[T]` (Milne, *Class Field Theory*,
Proposition 3.1), see `PlacePerm/herbrandEq_placeFunRep.lean`.

## Implementation

The two `ℤ`-linear maps are the obvious ones:

* `toFuns`: `f ↦ (v ↦ (w ↦ f w))`, using the inclusion `fibreSet T v ⊆ T`;
* `ofFuns`: a tuple of functions on the fibres is evaluated at `w ∈ T` using the chosen place
  `placeBelow S T hTS w ∈ S` below `w`.

They are inverse because the place below a place is unique (`toFuns_ofFuns_pt`), and both are
`G`-equivariant because `G` preserves every fibre (`placeFunEquiv_intertwines_pt`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.PlacePerm

open NK.GlobalCFT NK.GlobalCFTdeep NK.RepresentationTheory.GroupCohomology

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- The auxiliary constructions used in the proof of `placeFunRep_piRep_iso`, kept in their own
-- namespace so that they cannot clash with the vocabulary of other files.
namespace PlaceFunRepPiRepIso

/-- **A place of `S` below a place of `T`**: any place of `S` below `w`, chosen from the
hypothesis `hTS` by `Classical.choose` (it is unique by `globalCFT_liesOver_unique`). -/
noncomputable def placeBelow (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) (w : ↥T) : ↥S :=
  ⟨Classical.choose ((hTS w.1).mp w.2), (Classical.choose_spec ((hTS w.1).mp w.2)).1⟩

/-- The chosen place of `S` below `w ∈ T` really lies below `w`. -/
theorem placeBelow_liesOver (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) (w : ↥T) :
    Place.LiesOver (w : Place L) (placeBelow S T hTS w : Place K) :=
  (Classical.choose_spec ((hTS w.1).mp w.2)).2

/-- The place of `S` chosen below an element of the fibre of `v` is `v` itself (uniqueness of the
place below a place). -/
theorem placeBelow_eq (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    {v : ↥S} (w : ↥(fibreSet T (v : Place K))) :
    placeBelow S T hTS ⟨(w : Place L), w.2.1⟩ = v := by
  refine Subtype.ext ?_
  exact Inclusion.globalCFT_liesOver_unique
    (placeBelow_liesOver S T hTS ⟨(w : Place L), w.2.1⟩) w.2.2

/-- **A function on `T` gives a tuple of functions on the fibres.** -/
noncomputable def toFuns (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    (↥T → ℤ) →ₗ[ℤ] (∀ v : ↥S, ↥(fibreSet T (v : Place K)) → ℤ) where
  toFun f := fun _ w => f ⟨(w : Place L), w.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A tuple of functions on the fibres gives a function on `T`**: evaluate the tuple at the
fibre of the place below `w`. -/
noncomputable def ofFuns (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    (∀ v : ↥S, ↥(fibreSet T (v : Place K)) → ℤ) →ₗ[ℤ] (↥T → ℤ) where
  toFun x := fun w => x (placeBelow S T hTS w) ⟨w.1, w.2, placeBelow_liesOver S T hTS w⟩
  map_add' x y := by funext w; rfl
  map_smul' c x := by funext w; rfl

/-- `ofFuns` is a left inverse of `toFuns`. -/
theorem ofFuns_toFuns (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    (ofFuns S T hTS).comp (toFuns S T hTS) = LinearMap.id := by
  ext f
  rfl

/-- The key computation for the other round trip: the chosen place below an element of a fibre is
the index of that fibre, so evaluating a tuple at the chosen place recovers the tuple. -/
theorem toFuns_ofFuns_pt (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (x : ∀ v : ↥S, ↥(fibreSet T (v : Place K)) → ℤ)
    (v : ↥S) (w : Place L) (hw : w ∈ T) (hwv : Place.LiesOver w (v : Place K)) :
    x (placeBelow S T hTS ⟨w, hw⟩) ⟨w, hw, placeBelow_liesOver S T hTS ⟨w, hw⟩⟩
      = x v ⟨w, hw, hwv⟩ := by
  have h : placeBelow S T hTS ⟨w, hw⟩ = v :=
    Subtype.ext (Inclusion.globalCFT_liesOver_unique (placeBelow_liesOver S T hTS ⟨w, hw⟩) hwv)
  cases h
  rfl

/-- `toFuns` is a left inverse of `ofFuns`. -/
theorem toFuns_ofFuns (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    (toFuns S T hTS).comp (ofFuns S T hTS) = LinearMap.id := by
  ext x v w
  exact toFuns_ofFuns_pt S T hTS x v (w : Place L) w.2.1 w.2.2

/-- **The underlying linear equivalence**: `ℤ[T] ≃ ∏_{v ∈ S} ℤ[fibre above v]`. -/
noncomputable def placeFunEquiv (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    (↥T → ℤ) ≃ₗ[ℤ] (∀ v : ↥S, ↥(fibreSet T (v : Place K)) → ℤ) :=
  LinearEquiv.ofLinearMap (toFuns S T hTS) (ofFuns S T hTS)
    (toFuns_ofFuns S T hTS) (ofFuns_toFuns S T hTS)

/-- The action of `Gal(L/K)` on the permutation module `ℤ[T]`, unfolded. -/
theorem placeFunRep_ρ_apply {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (f : ↥T → ℤ) (w : ↥T) :
    ((placeFunRep (K := K) (L := L) T hT).ρ σ f) w
      = f ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩ := rfl

/-- **`placeFunEquiv` is `Gal(L/K)`-equivariant**, pointwise form.  Both sides send `f` to the
function on the fibre of `v` given by `w ↦ f (σ⁻¹ • w)`: the isomorphism respects the fibres
because `Gal(L/K)` preserves the place below a place. -/
theorem placeFunEquiv_intertwines_pt (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (σ : L ≃ₐ[K] L) (f : ↥T → ℤ) (v : ↥S)
    (w : ↥(fibreSet T (v : Place K))) :
    toFuns S T hTS ((placeFunRep (K := K) (L := L) T hT).ρ σ f) v w
      = (piRep (fun v : ↥S => fibreRep (K := K) (L := L) T hT (v : Place K))).ρ σ
          (toFuns S T hTS f) v w := by
  have hL : toFuns S T hTS ((placeFunRep (K := K) (L := L) T hT).ρ σ f) v w
      = ((placeFunRep (K := K) (L := L) T hT).ρ σ f) ⟨(w : Place L), w.2.1⟩ := rfl
  have h1 : ((placeFunRep (K := K) (L := L) T hT).ρ σ f) ⟨(w : Place L), w.2.1⟩
      = f ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2.1⟩ :=
    placeFunRep_ρ_apply (K := K) (L := L) (T := T) hT σ f ⟨(w : Place L), w.2.1⟩
  have hR : f ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2.1⟩
      = (piRep (fun v : ↥S => fibreRep (K := K) (L := L) T hT (v : Place K))).ρ σ
          (toFuns S T hTS f) v w := rfl
  exact hL.trans (h1.trans hR)

/-- The `ℤ[Gal(L/K)]`-linearity of `placeFunEquiv`: it is an isomorphism of `ℤ[Gal(L/K)]`-modules
from `ℤ[T]` to the pointwise product of the fibre modules. -/
theorem placeFunEquiv_intertwines (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) (σ : L ≃ₐ[K] L) :
    (placeFunEquiv S T hTS : (↥T → ℤ) →ₗ[ℤ]
        (∀ v : ↥S, ↥(fibreSet T (v : Place K)) → ℤ)) ∘ₗ
        (placeFunRep (K := K) (L := L) T hT).ρ σ
      = (piRep (fun v : ↥S => fibreRep (K := K) (L := L) T hT (v : Place K))).ρ σ ∘ₗ
        (placeFunEquiv S T hTS : (↥T → ℤ) →ₗ[ℤ]
          (∀ v : ↥S, ↥(fibreSet T (v : Place K)) → ℤ)) := by
  apply LinearMap.ext
  intro f
  funext v w
  exact placeFunEquiv_intertwines_pt S T hT hTS σ f v w

end PlaceFunRepPiRepIso

open PlaceFunRepPiRepIso

-- The set `T` of places of `L` above a finite set `S` of places of `K` is the disjoint union of
-- its fibres `fibreSet T v` (`v ∈ S`), since the place of `K` below a place of `L` is unique, so a
-- function on `T` with values in `ℤ` is the same thing as a tuple of functions on the fibres.
-- `Gal(L/K)` preserves every fibre individually, so this is an isomorphism of `ℤ[Gal(L/K)]`-modules,
-- the action on the right-hand side being the pointwise (diagonal) one.
theorem placeFunRep_piRep_iso {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v) :
    Nonempty (NK.GlobalCFTdeep.placeFunRep (K := K) (L := L) T hT ≅
      NK.RepresentationTheory.GroupCohomology.piRep (fun v : ↥S =>
        NK.GlobalCFTdeep.PlacePerm.fibreRep (K := K) (L := L) T hT
          (v : NK.GlobalCFT.Place K))) := by
  exact ⟨Rep.mkIso (Representation.Equiv.mk (placeFunEquiv S T hTS)
    (fun σ => placeFunEquiv_intertwines S T hT hTS σ))⟩

end NK.GlobalCFTdeep.PlacePerm
