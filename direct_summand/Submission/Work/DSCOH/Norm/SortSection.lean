/-
Area DSCOH (curric-46) — the normalization comparison: the sorting section `semiLift`.

The projection `semiProj : allT ⟶ semiT` (Mathlib's unnormalized Čech complex onto the complex of
nondecreasing tuples) has the "signed sorting" section `semiLift`, whose `x`-component is
`sign(σˣ) • s_{sorted x}` where `σˣ = Tuple.sort x` is the stable sorting permutation of `x`.
This file defines the data and proves that `semiLift` is a section of `semiProj`
(Stacks Project, Section 20.23, `01FG`).
-/
import Mathlib
import Submission.Work.DSCOH.Norm.Complexes

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [Fintype ι] [HasProducts (ModuleCat A)]

/-! ## The sorting data of a tuple -/

/-- The semi-ordered index attached to a tuple: the tuple itself, stably sorted. -/
noncomputable def sortIdx {n : ℕ} (x : Fin (n + 1) → ι) : SemiIdx ι n :=
  ⟨x ∘ Tuple.sort x, Tuple.monotone_sort x⟩

/-- The sign of the stable sorting permutation of a tuple. -/
noncomputable def sortSign {n : ℕ} (x : Fin (n + 1) → ι) : ℤ :=
  ((Equiv.Perm.sign (Tuple.sort x) : ℤˣ) : ℤ)

/-- The canonical morphism of opens `∏ᶜ (U ∘ x) ⟶ ∏ᶜ (U ∘ (x ∘ sort))`. -/
noncomputable def sortHom (U : ι → Opens X) {n : ℕ} (x : Fin (n + 1) → ι) :
    tupleOp U x ⟶ tupleOp U (x ∘ Tuple.sort x) :=
  Pi.lift fun a => Pi.π (fun b : Fin (n + 1) => U (x b)) (Tuple.sort x a)

/-- The canonical identification `tupleMod P U (x ∘ sort) ⟶ tupleMod P U x` of the sections over
the open of a tuple and over the open of its sorted version (they are the same open). -/
noncomputable def sortRes (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {n : ℕ}
    (x : Fin (n + 1) → ι) :
    tupleMod P U (x ∘ Tuple.sort x) ⟶ tupleMod P U x :=
  P.map (sortHom U x).op

/-- **The sorting section** `semiTerm P U n ⟶ (cechComplexFunctor U).obj P).X n`: the `x`-component
is `sign(σˣ) • s_{sorted x}` where `σˣ` is the stable sorting permutation of `x`. -/
noncomputable def semiLift (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    semiTerm P U n ⟶ ((cechComplexFunctor U).obj P).X n :=
  Pi.lift fun x : Fin (n + 1) → ι =>
    sortSign x • (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val) (sortIdx x) ≫
      sortRes P U x)

/-! ## Basic properties of the sorting data -/

@[simp]
lemma sortIdx_val {n : ℕ} (x : Fin (n + 1) → ι) : (sortIdx x).val = x ∘ Tuple.sort x := rfl

lemma sortIdx_of_monotone {n : ℕ} (x : Fin (n + 1) → ι) (hx : Monotone x) :
    sortIdx x = ⟨x, hx⟩ := by
  refine Subtype.ext ?_
  simp only [sortIdx_val, Tuple.sort_eq_refl_iff_monotone.mpr hx, Equiv.coe_refl, Function.comp_id]

@[simp]
lemma sortSign_of_monotone {n : ℕ} (x : Fin (n + 1) → ι) (hx : Monotone x) :
    sortSign x = 1 := by
  unfold sortSign
  rw [Tuple.sort_eq_refl_iff_monotone.mpr hx]
  simp

/-- When the tuple is already nondecreasing, the canonical identification `sortRes` is the identity
(and we record it in the `eqToHom` form, since the two module objects are only propositionally
equal). -/
lemma sortRes_of_monotone (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {n : ℕ}
    (x : Fin (n + 1) → ι) (hx : Monotone x) :
    sortRes P U x = eqToHom (congrArg (fun t : SemiIdx ι n => tupleMod P U t.val)
      (sortIdx_of_monotone x hx)) := by
  have hg : (fun t : SemiIdx ι n => (op (tupleOp U t.val) : (Opens X)ᵒᵖ)) (sortIdx x)
      = (fun t : SemiIdx ι n => (op (tupleOp U t.val) : (Opens X)ᵒᵖ)) ⟨x, hx⟩ :=
    congrArg (fun t : SemiIdx ι n => (op (tupleOp U t.val) : (Opens X)ᵒᵖ))
      (sortIdx_of_monotone x hx)
  have hmap : sortRes P U x = P.map (eqToHom hg) := by
    unfold sortRes
    congr 1
    exact Subsingleton.elim _ _
  rw [hmap, eqToHom_map]

/-- The `x`-component of the sorting section. -/
lemma semiLift_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ)
    (x : Fin (n + 1) → ι) :
    semiLift P U n ≫ Pi.π (fun y : Fin (n + 1) → ι => tupleMod P U y) x =
      sortSign x • (Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val) (sortIdx x) ≫
        sortRes P U x) := by
  rw [semiLift]
  exact Pi.lift_comp_π _ _

/-! ## `semiLift` is a section of `semiProj` -/

theorem semiLift_semiProj (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    semiLift P U n ≫ semiProj P U n = 𝟙 (semiTerm P U n) := by
  apply Pi.hom_ext
  intro s
  rw [Category.assoc]
  rw [show semiProj P U n ≫ Pi.π (fun s : SemiIdx ι n => tupleMod P U s.val) s =
      Pi.π (fun y : Fin (n + 1) → ι => tupleMod P U y) s.val from Pi.lift_comp_π _ _]
  rw [semiLift_comp, sortSign_of_monotone _ s.property, one_smul]
  have key := Pi.π_comp_eqToHom (f := fun t : SemiIdx ι n => tupleMod P U t.val)
    (j := sortIdx s.val) (j' := s) (sortIdx_of_monotone s.val s.property)
  rw [sortRes_of_monotone P U s.val s.property]
  rw [show eqToHom (by simp [sortIdx_of_monotone s.val s.property]) =
      eqToHom (congrArg (fun t : SemiIdx ι n => tupleMod P U t.val)
        (sortIdx_of_monotone s.val s.property)) from
    congrArg eqToHom (Subsingleton.elim _ _)] at key
  exact key

end Work.DSCOH.Norm
