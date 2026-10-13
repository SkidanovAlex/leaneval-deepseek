import Mathlib
import Submission.Work.DSCOH.Norm.SemiOrd
import Submission.Work.DSCOH.Norm.Maps
import Submission.Work.DSCOH.Norm.cechComplexFunctor_d_comp
import Submission.Work.DSCOH.Norm.semiD_ordD_comp
import Submission.Work.DSCOH.Norm.del_eq_of_monotone_of_eq
import Submission.Work.DSCOH.Norm.strictMono_del_apply_eq
import Submission.Work.DSCOH.Norm.strictMono_del_congr
import Submission.Work.DSCOH.Norm.exists_adjacent_repeat
import Submission.Work.DSCOH.Norm.sum_dite_vanish
import Submission.Work.DSCOH.Norm.semiProj_chain
import Submission.Work.DSCOH.Norm.ordProj_chain

namespace Work.DSCOH.Norm

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [LinearOrder ι] [HasProducts (ModuleCat A)]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-! ## Component formulas

The first six lemmas are the definitional unfolding of the maps as `Pi.lift`s:  the composite of
a `Pi.lift` with a projection is the corresponding component. -/

/-- The `x`-th component of the semi-ordered Čech differential. -/
lemma semiD_comp_pi (n : ℕ) (x : SemiIdx ι (n + 1)) :
    semiD P U n ≫ Pi.π (fun z : SemiIdx ι (n + 1) => tupleMod P U z.val) x =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
        (Pi.π (fun z : SemiIdx ι n => tupleMod P U z.val)
            ⟨del x.val b, monotone_del x.val b x.property⟩ ≫ resDel P U x.val b) :=
  Pi.lift_comp_π _ _

/-- The `x`-th component of the ordered Čech differential. -/
lemma ordD_comp_pi (n : ℕ) (x : OrdIdx ι (n + 1)) :
    ordD P U n ≫ Pi.π (fun z : OrdIdx ι (n + 1) => tupleMod P U z.val) x =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
        (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val)
            ⟨del x.val b, strictMono_del x.val b x.property⟩ ≫ resDel P U x.val b) :=
  Pi.lift_comp_π _ _

/-- The `x`-th component of the projection onto the semi-ordered complex, `x` semi-ordered. -/
lemma semiProj_comp_pi (n : ℕ) (x : SemiIdx ι n) :
    semiProj P U n ≫ Pi.π (fun z : SemiIdx ι n => tupleMod P U z.val) x =
      Pi.π (fun z : Fin (n + 1) → ι => tupleMod P U z) x.val :=
  Pi.lift_comp_π _ _

/-- The `x`-th component of the projection onto the ordered complex, `x` ordered. -/
lemma ordProj_comp_pi (n : ℕ) (x : OrdIdx ι n) :
    ordProj P U n ≫ Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) x =
      Pi.π (fun z : SemiIdx ι n => tupleMod P U z.val) ⟨x.val, x.property.monotone⟩ :=
  Pi.lift_comp_π _ _

/-- The `y`-th component of `ordIncl`, `y` semi-ordered: the identity on strictly increasing
tuples and zero on the other ones. -/
lemma ordIncl_comp_pi (n : ℕ) (y : Fin (n + 1) → ι) (hy : Monotone y) :
    ordIncl P U n ≫ Pi.π (fun z : SemiIdx ι n => tupleMod P U z.val) ⟨y, hy⟩ =
      (if h : StrictMono y then
        (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨y, h⟩ :
          ordTerm P U n ⟶ tupleMod P U y) else 0) :=
  Pi.lift_comp_π _ _

/-- The `x`-th component of Mathlib's unnormalized Čech differential. -/
lemma cech_d_comp_pi (n : ℕ) (x : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫
        Pi.π (fun z : Fin (n + 2) → ι => tupleMod P U z) x =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
        (Pi.π (fun z : Fin (n + 1) → ι => tupleMod P U z) (del x b) ≫
          resDel P U x b) := by
  rw [cechComplexFunctor_d_comp P U n]
  exact Pi.lift_comp_π _ _

/-! ## Pushing a `dite` through a composition -/

/-- A `dite` whose branches are morphisms may be pushed through a composition on the right. -/
lemma dite_comp_aux {C : Type*} [Category C] [Preadditive C] {p : Prop} [Decidable p]
    {Y Z W : C}
    (f : p → (Y ⟶ Z)) (g : Z ⟶ W) :
    (dite p f (fun _ => 0)) ≫ g = dite p (fun h => f h ≫ g) (fun _ => 0) := by
  by_cases h : p
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h, zero_comp]

/-- A `dite` whose branches are morphisms may be pushed through a composition on the left. -/
lemma comp_dite_aux {C : Type*} [Category C] [Preadditive C] {p : Prop} [Decidable p]
    {Y Z W : C}
    (f : Z ⟶ Y) (g : p → (Y ⟶ W)) :
    f ≫ dite p g (fun _ => 0) = dite p (fun h => f ≫ g h) (fun _ => 0) := by
  by_cases h : p
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h, comp_zero]

/-! ## Comparing the two summands attached to a repeated value -/

/-- Two Čech components whose tuples are equal, with the two restrictions starting at one and
the same open, agree: the category of open subsets of `X` is thin.

The type ascriptions to `ordTerm P U n` (rather than to the product by which it is defined) are
there to pin down the universe of the module category, so that this lemma applies in the same
universe as the definitions of `Work.DSCOH.Norm`. -/
lemma pi_map_eq (n : ℕ) {z z' : OrdIdx ι n} (hz : z = z') {V : Opens X}
    (β : V ⟶ tupleOp U z.val) (β' : V ⟶ tupleOp U z'.val) :
    (Pi.π (fun w : OrdIdx ι n => tupleMod P U w.val) z :
        ordTerm P U n ⟶ tupleMod P U z.val) ≫ P.map β.op =
      (Pi.π (fun w : OrdIdx ι n => tupleMod P U w.val) z' :
        ordTerm P U n ⟶ tupleMod P U z'.val) ≫ P.map β'.op := by
  subst hz
  rw [Subsingleton.elim β β']

/-- The Čech component "delete the `b`-th entry and restrict" only depends on the tuple obtained
by deleting the `b`-th entry, whence deleting either of two positions carrying the same value
gives the same morphism. -/
lemma pi_resDel_congr (n : ℕ) {x : Fin (n + 2) → ι} (hx : Monotone x) {b b' : Fin (n + 2)}
    (h : x b = x b') (hb : StrictMono (del x b)) (hb' : StrictMono (del x b')) :
    (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨del x b, hb⟩ :
        ordTerm P U n ⟶ tupleMod P U (del x b)) ≫ resDel P U x b =
      (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨del x b', hb'⟩ :
        ordTerm P U n ⟶ tupleMod P U (del x b')) ≫ resDel P U x b' := by
  rw [resDel_eq, resDel_eq]
  exact pi_map_eq P U n (z := ⟨del x b, hb⟩) (z' := ⟨del x b', hb'⟩)
    (Subtype.ext (del_eq_of_monotone_of_eq hx h)) (opDel U x b) (opDel U x b')

/-! ## The `ordIncl` chain-map identity, componentwise -/

/-- Componentwise form of `ordIncl P U n ≫ semiD P U n = ordD P U n ≫ ordIncl P U (n+1)`. -/
theorem ordIncl_semiD_comp_pi (n : ℕ) (x : SemiIdx ι (n + 1)) :
    (ordIncl P U n ≫ semiD P U n) ≫
        Pi.π (fun z : SemiIdx ι (n + 1) => tupleMod P U z.val) x =
      (ordD P U n ≫ ordIncl P U (n + 1)) ≫
        Pi.π (fun z : SemiIdx ι (n + 1) => tupleMod P U z.val) x := by
  have hL : (ordIncl P U n ≫ semiD P U n) ≫
        Pi.π (fun z : SemiIdx ι (n + 1) => tupleMod P U z.val) x =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
        (dite (StrictMono (del x.val b))
          (fun h => Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨del x.val b, h⟩ ≫
            resDel P U x.val b)
          (fun _ => 0)) := by
    rw [Category.assoc, semiD_comp_pi, Preadditive.comp_sum]
    simp only [Preadditive.comp_zsmul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Category.assoc,
      ordIncl_comp_pi P U n (del x.val b) (monotone_del x.val b x.property), dite_comp_aux]
  by_cases hx : StrictMono x.val
  · have hR : (ordD P U n ≫ ordIncl P U (n + 1)) ≫
          Pi.π (fun z : SemiIdx ι (n + 1) => tupleMod P U z.val) x =
        ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
          (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val)
              ⟨del x.val b, strictMono_del x.val b hx⟩ ≫ resDel P U x.val b) := by
      rw [Category.assoc, ordIncl_comp_pi P U (n + 1) x.val x.property, comp_dite_aux,
        dite_eq_left hx, ordD_comp_pi]
    rw [hL, hR]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dite_eq_left (strictMono_del x.val b hx)]
  · have hR : (ordD P U n ≫ ordIncl P U (n + 1)) ≫
          Pi.π (fun z : SemiIdx ι (n + 1) => tupleMod P U z.val) x = 0 := by
      rw [Category.assoc, ordIncl_comp_pi P U (n + 1) x.val x.property, comp_dite_aux,
        dite_eq_right hx]
    have hG' : ∀ (b b' : Fin (n + 2)) (hb : StrictMono (del x.val b))
        (hb' : StrictMono (del x.val b')), x.val b = x.val b' →
        (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨del x.val b, hb⟩ ≫
            resDel P U x.val b) =
          (Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨del x.val b', hb'⟩ ≫
            resDel P U x.val b') := by
      intro b b' hb hb' h
      exact pi_resDel_congr (P := P) (U := U) (n := n) (x := x.val) x.property h hb hb'
    rw [hL, hR]
    exact sum_dite_vanish x.val x.property hx
      (G := fun b hb => Pi.π (fun z : OrdIdx ι n => tupleMod P U z.val) ⟨del x.val b, hb⟩ ≫
        resDel P U x.val b)
      hG'

/-- `ordIncl` is a chain map for the truncated Čech differentials. -/
theorem ordIncl_semiD (n : ℕ) :
    ordIncl P U n ≫ semiD P U n = ordD P U n ≫ ordIncl P U (n + 1) := by
  apply Pi.hom_ext (f := fun z : SemiIdx ι (n + 1) => tupleMod P U z.val)
  intro x
  exact ordIncl_semiD_comp_pi P U n x

/-- The three comparison maps of `Work.DSCOH.Norm` are chain maps for the Čech differentials:
`semiProj` (Mathlib's unnormalized Čech complex to the semi-ordered complex, differential
`semiD`), `ordProj` (semi-ordered to ordered) and `ordIncl` (ordered to semi-ordered).

This is the component computation matching the "delete the `b`-th entry and restrict" terms of
the differentials; it follows by `Pi.hom_ext` from
`Work.DSCOH.Norm.cechComplexFunctor_d_comp` and the definitional unfolding of `semiD`/`ordD` as
`Pi.lift`s.  For `ordIncl` the argument is the classical one: if `x` is nondecreasing but not
strictly increasing, the entries of `x` whose deletion is strict are the two copies of its
(single) adjacent repeat, and the two summands cancel because they are the same morphism with
opposite signs. -/
theorem projInclChain {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : Opposite (TopologicalSpace.Opens X) ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) :
    (∀ n : ℕ, Work.DSCOH.Norm.semiProj P U n ≫ Work.DSCOH.Norm.semiD P U n =
        ((cechComplexFunctor U).obj P).d n (n + 1) ≫ Work.DSCOH.Norm.semiProj P U (n + 1)) ∧
      (∀ n : ℕ, Work.DSCOH.Norm.ordProj P U n ≫ Work.DSCOH.Norm.ordD P U n =
        Work.DSCOH.Norm.semiD P U n ≫ Work.DSCOH.Norm.ordProj P U (n + 1)) ∧
        (∀ n : ℕ, Work.DSCOH.Norm.ordIncl P U n ≫ Work.DSCOH.Norm.semiD P U n =
          Work.DSCOH.Norm.ordD P U n ≫ Work.DSCOH.Norm.ordIncl P U (n + 1)) := by
  exact ⟨fun n => semiProj_chain P U n, fun n => ordProj_chain P U n,
    fun n => ordIncl_semiD P U n⟩

end Work.DSCOH.Norm
