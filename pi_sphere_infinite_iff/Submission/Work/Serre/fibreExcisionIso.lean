import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Thom.ATools
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.cappedPairMapIso
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.Serre.isIso_relCohMap_id_of_deformationRetract

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Excision for the union of the bottom copy and the fibre cone of a mapping cylinder

Let `p : C(E,B)` be a continuous map with mapping cylinder `cyl p`, bottom copy
`A = range (cylIncl p)` and fibre cone `Mb = (cylRetract p)⁻¹{b}`.  The union `C = A ∪ Mb` is the
pair `(C, A)`: the restriction

`H^{r+1}(C, A; ℚ) ⟶ H^{r+1}(Mb, Mb ∩ A; ℚ)`

is an isomorphism (in particular injective), for the following reason.  The collar
`U = C ∩ cylCollar p` of `cyl p` over the bottom copy is an open neighbourhood of `A` in `C`, and

* `H^n(C, A) ≅ H^n(C, U)`: the shrink homotopy `cylShrink p` retracts `U` onto `A` through maps
  which fix `A` pointwise, so the identity of pairs `(C,U) → (C,A)` is a homotopy equivalence;
* `H^n(C, U) ≅ H^n(Mb, U ∩ Mb)`: excision for the pair `(C, U)` with the excised set `C ∖ Mb`
  (whose closure is contained in the interior of `U`, because `C ∖ Mb ⊆ A` and `A` is a closed
  subset of the open collar);
* `H^n(Mb, U ∩ Mb) ≅ H^n(Mb, Mb ∩ A)`: the same shrink homotopy, now retracting the collar
  `U ∩ Mb` of the cone onto its base `Mb ∩ A`.

The three isomorphisms compose to the restriction map (functoriality of `relCohMap`), which is
therefore an isomorphism and in particular injective.

Only the injectivity is claimed, because it is all the caller needs; the proof here gives the
isomorphism.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]

/-! ## The sets -/

/-- The fibre cone `Mb = (cylRetract p)⁻¹{b}` of the mapping cylinder: the preimage of the point
`b` under the retraction. -/
def excM (p : C(E, B)) (b : B) : Set (cyl p) := (cylRetract p) ⁻¹' ({b} : Set B)

/-- The union `C = A ∪ Mb` of the bottom copy `A = range (cylIncl p)` and the fibre cone
`Mb = (cylRetract p)⁻¹{b}`. -/
def excC (p : C(E, B)) (b : B) : Set (cyl p) := cylBot p ∪ excM p b

theorem mem_excC_iff (p : C(E, B)) (b : B) (y : cyl p) :
    y ∈ excC p b ↔ y ∈ cylBot p ∨ y ∈ excM p b := Iff.rfl

theorem mem_excM_iff (p : C(E, B)) (b : B) (y : cyl p) :
    y ∈ excM p b ↔ cylRetract p y = b := Iff.rfl

theorem excM_subset_excC (p : C(E, B)) (b : B) : excM p b ⊆ excC p b := fun _ h => Or.inr h

theorem cylBot_subset_excC (p : C(E, B)) (b : B) : cylBot p ⊆ excC p b := fun _ h => Or.inl h

/-- The bottom copy inside `C`. -/
def excAc (p : C(E, B)) (b : B) : Set ↥(excC p b) := {x | (x : cyl p) ∈ cylBot p}

/-- The fibre cone inside `C`. -/
def excMc (p : C(E, B)) (b : B) : Set ↥(excC p b) := {x | (x : cyl p) ∈ excM p b}

/-- The collar of the mapping cylinder, inside `C`. -/
def excUc (p : C(E, B)) (b : B) : Set ↥(excC p b) := {x | (x : cyl p) ∈ cylCollar p}

/-- The collar of the mapping cylinder, inside the fibre cone `Mb`. -/
def excUb (p : C(E, B)) (b : B) : Set ↥(excM p b) := {x | (x : cyl p) ∈ cylCollar p}

/-- The bottom copy of the fibre cone, inside `Mb`. -/
def excAb (p : C(E, B)) (b : B) : Set ↥(excM p b) := {x | (x : cyl p) ∈ cylBot p}

theorem excAc_subset_excUc (p : C(E, B)) (b : B) : excAc p b ⊆ excUc p b :=
  fun x hx => cylBot_subset_cylCollar p hx

theorem excAb_subset_excUb (p : C(E, B)) (b : B) : excAb p b ⊆ excUb p b :=
  fun x hx => cylBot_subset_cylCollar p hx

/-! ## The bottom copy is closed, and the collar is open -/

/-- The collar coordinate vanishes exactly on the bottom copy. -/
theorem cylBot_eq_cylLam_zero (p : C(E, B)) : cylBot p = {y | cylLam p y = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hy
    induction y using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl q =>
        obtain ⟨x, t⟩ := q
        have hy' : cylLam p (cylMk p (Sum.inl (x, t))) = 0 := hy
        rw [cylLam_cylMk, cylLamFun_inl] at hy'
        exact ⟨x, by rw [hy']; rfl⟩
      | inr γ =>
        have hy' : cylLam p (cylMk p (Sum.inr γ)) = 0 := hy
        rw [cylLam_cylMk, cylLamFun_inr] at hy'
        exact absurd hy' one_ne_zero

/-- The bottom copy of the mapping cylinder is closed. -/
theorem isClosed_cylBot (p : C(E, B)) : IsClosed (cylBot p) := by
  rw [cylBot_eq_cylLam_zero]
  exact isClosed_singleton.preimage (cylLam p).continuous

theorem isOpen_excUc (p : C(E, B)) (b : B) : IsOpen (excUc p b) :=
  (isOpen_cylCollar p).preimage continuous_subtype_val

theorem isClosed_excAc (p : C(E, B)) (b : B) : IsClosed (excAc p b) :=
  (isClosed_cylBot p).preimage continuous_subtype_val

/-- The complement of the fibre cone `Mb` inside `C` is contained in the bottom copy. -/
theorem diff_excMc_subset_excAc (p : C(E, B)) (b : B) :
    {x : ↥(excC p b) | x ∉ excMc p b} ⊆ excAc p b := by
  intro x hx
  rcases x.2 with h | h
  · exact h
  · exact absurd h hx

/-- **The closure of the complement of `Mb` in `C` is contained in the interior of the collar.**
The complement is contained in the bottom copy `A`, which is closed, and `A` is contained in the
collar, which is open. -/
theorem closure_diff_excMc_subset (p : C(E, B)) (b : B) :
    closure {x : ↥(excC p b) | x ∉ excMc p b} ⊆ interior (excUc p b) := by
  calc closure {x : ↥(excC p b) | x ∉ excMc p b}
      ⊆ closure (excAc p b) := closure_mono (diff_excMc_subset_excAc p b)
    _ = excAc p b := (isClosed_excAc p b).closure_eq
    _ ⊆ excUc p b := excAc_subset_excUc p b
    _ = interior (excUc p b) := (isOpen_excUc p b).interior_eq.symm


/-! ## The collar inside `C` and inside `Mb` -/

/-- The collar `↥(cylCollar p)` as a subspace of `↥(excUc p b)`. -/
def toCollarC (p : C(E, B)) (b : B) : C(↥(excUc p b), ↥(cylCollar p)) where
  toFun y := ⟨y.1.1, y.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The collar `↥(cylCollar p)` as a subspace of `↥(excUb p b)`. -/
def toCollarM (p : C(E, B)) (b : B) : C(↥(excUb p b), ↥(cylCollar p)) where
  toFun y := ⟨y.1.1, y.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

@[simp] theorem toCollarC_apply (p : C(E, B)) (b : B) (y : ↥(excUc p b)) :
    (toCollarC p b y : cyl p) = (y : cyl p) := rfl

@[simp] theorem toCollarM_apply (p : C(E, B)) (b : B) (y : ↥(excUb p b)) :
    (toCollarM p b y : cyl p) = (y : cyl p) := rfl

/-- The shrink of the collar stays inside the union `C = A ∪ Mb`. -/
theorem cylShrink_mem_excC (p : C(E, B)) (b : B) (t : unitInterval) {y : ↥(cylCollar p)}
    (hy : (y : cyl p) ∈ excC p b) : (cylShrink p t y : cyl p) ∈ excC p b := by
  rcases hy with h | h
  · exact Or.inl (by rw [cylShrink_fixes_bot p t h]; exact h)
  · exact Or.inr (by
      rw [mem_excM_iff] at h ⊢
      rw [cylRetract_cylShrink]
      exact h)

/-- The shrink of the collar stays inside the fibre cone `Mb`. -/
theorem cylShrink_mem_excM (p : C(E, B)) (b : B) (t : unitInterval) {y : ↥(cylCollar p)}
    (hy : (y : cyl p) ∈ excM p b) : (cylShrink p t y : cyl p) ∈ excM p b := by
  rw [mem_excM_iff] at hy ⊢
  rw [cylRetract_cylShrink]
  exact hy

/-- The collar of the mapping cylinder as a subspace of `↥(excUc p b)`, with the shrink applied:
this is the joint shrink, as a continuous map into the collar. -/
theorem continuous_cylShrink_pairC (p : C(E, B)) (b : B) :
    Continuous fun q : unitInterval × ↥(excUc p b) =>
      (cylShrink p q.1 (toCollarC p b q.2) : ↥(cylCollar p)) := by
  have hEq : (fun q : unitInterval × ↥(excUc p b) =>
        (cylShrink p q.1 (toCollarC p b q.2) : ↥(cylCollar p)))
      = fun q => cylShrinkHomotopy p (q.1, toCollarC p b q.2) := by
    funext q
    exact cylShrinkHomotopy_apply p q.1 (toCollarC p b q.2)
  rw [hEq]
  exact (cylShrinkHomotopy p).continuous.comp
    ((ContinuousMap.prodMap (ContinuousMap.id unitInterval) (toCollarC p b)).continuous)

theorem continuous_cylShrink_pairM (p : C(E, B)) (b : B) :
    Continuous fun q : unitInterval × ↥(excUb p b) =>
      (cylShrink p q.1 (toCollarM p b q.2) : ↥(cylCollar p)) := by
  have hEq : (fun q : unitInterval × ↥(excUb p b) =>
        (cylShrink p q.1 (toCollarM p b q.2) : ↥(cylCollar p)))
      = fun q => cylShrinkHomotopy p (q.1, toCollarM p b q.2) := by
    funext q
    exact cylShrinkHomotopy_apply p q.1 (toCollarM p b q.2)
  rw [hEq]
  exact (cylShrinkHomotopy p).continuous.comp
    ((ContinuousMap.prodMap (ContinuousMap.id unitInterval) (toCollarM p b)).continuous)

/-- **The joint shrink of the collar, inside `C`.** -/
def shrinkPairC (p : C(E, B)) (b : B) :
    C(unitInterval × ↥(excUc p b), ↥(excUc p b)) where
  toFun q := ⟨⟨(cylShrink p q.1 (toCollarC p b q.2) : cyl p),
      cylShrink_mem_excC p b q.1 q.2.1.2⟩, (cylShrink p q.1 (toCollarC p b q.2)).2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp (continuous_cylShrink_pairC p b))
        (fun q => cylShrink_mem_excC p b q.1 q.2.1.2))
      (fun q => (cylShrink p q.1 (toCollarC p b q.2)).2)

/-- **The joint shrink of the collar, inside the fibre cone `Mb`.** -/
def shrinkPairM (p : C(E, B)) (b : B) :
    C(unitInterval × ↥(excUb p b), ↥(excUb p b)) where
  toFun q := ⟨⟨(cylShrink p q.1 (toCollarM p b q.2) : cyl p),
      cylShrink_mem_excM p b q.1 q.2.1.2⟩, (cylShrink p q.1 (toCollarM p b q.2)).2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp (continuous_cylShrink_pairM p b))
        (fun q => cylShrink_mem_excM p b q.1 q.2.1.2))
      (fun q => (cylShrink p q.1 (toCollarM p b q.2)).2)

/-- The shrink at a fixed time, inside `C`. -/
def shrinkC (p : C(E, B)) (b : B) (t : unitInterval) :
    C(↥(excUc p b), ↥(excUc p b)) :=
  (shrinkPairC p b).comp
    ⟨fun y => (t, y), continuous_const.prodMk continuous_id⟩

/-- The shrink at a fixed time, inside the fibre cone `Mb`. -/
def shrinkM (p : C(E, B)) (b : B) (t : unitInterval) :
    C(↥(excUb p b), ↥(excUb p b)) :=
  (shrinkPairM p b).comp
    ⟨fun y => (t, y), continuous_const.prodMk continuous_id⟩

@[simp] theorem shrinkC_apply (p : C(E, B)) (b : B) (t : unitInterval) (y : ↥(excUc p b)) :
    shrinkC p b t y = shrinkPairC p b (t, y) := rfl

@[simp] theorem shrinkM_apply (p : C(E, B)) (b : B) (t : unitInterval) (y : ↥(excUb p b)) :
    shrinkM p b t y = shrinkPairM p b (t, y) := rfl

@[simp] theorem shrinkPairC_coe (p : C(E, B)) (b : B) (q : unitInterval × ↥(excUc p b)) :
    ((shrinkPairC p b q : ↥(excUc p b)) : cyl p)
      = (cylShrink p q.1 (toCollarC p b q.2) : cyl p) := rfl

@[simp] theorem shrinkPairM_coe (p : C(E, B)) (b : B) (q : unitInterval × ↥(excUb p b)) :
    ((shrinkPairM p b q : ↥(excUb p b)) : cyl p)
      = (cylShrink p q.1 (toCollarM p b q.2) : cyl p) := rfl

/-! ## The shrink homotopies -/

/-- **The shrink homotopy of the collar inside `C`.** -/
def shrinkHomC (p : C(E, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(excUc p b)) (shrinkC p b 1) where
  toContinuousMap := shrinkPairC p b
  map_zero_left y := by
    refine Subtype.ext (Subtype.ext ?_)
    show (cylShrink p 0 (toCollarC p b y) : cyl p) = (y : cyl p)
    rw [← cylShrinkHomotopy_apply p 0 (toCollarC p b y)]
    exact congrArg Subtype.val ((cylShrinkHomotopy p).map_zero_left (toCollarC p b y))
  map_one_left y := rfl

/-- **The shrink homotopy of the collar inside the fibre cone `Mb`.** -/
def shrinkHomM (p : C(E, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(excUb p b)) (shrinkM p b 1) where
  toContinuousMap := shrinkPairM p b
  map_zero_left y := by
    refine Subtype.ext (Subtype.ext ?_)
    show (cylShrink p 0 (toCollarM p b y) : cyl p) = (y : cyl p)
    rw [← cylShrinkHomotopy_apply p 0 (toCollarM p b y)]
    exact congrArg Subtype.val ((cylShrinkHomotopy p).map_zero_left (toCollarM p b y))
  map_one_left y := rfl

/-- The shrink at time `1` lands in the bottom copy, inside `C`. -/
theorem shrinkC_one_mem (p : C(E, B)) (b : B) (y : ↥(excUc p b)) :
    ((shrinkC p b 1 y : ↥(excUc p b)) : cyl p) ∈ cylBot p := by
  rw [shrinkC_apply, shrinkPairC_coe]
  exact cylShrink_one_mem_cylBot p (toCollarC p b y)

/-- The shrink at time `1` lands in the bottom copy, inside `Mb`. -/
theorem shrinkM_one_mem (p : C(E, B)) (b : B) (y : ↥(excUb p b)) :
    ((shrinkM p b 1 y : ↥(excUb p b)) : cyl p) ∈ cylBot p := by
  rw [shrinkM_apply, shrinkPairM_coe]
  exact cylShrink_one_mem_cylBot p (toCollarM p b y)

/-- The shrink fixes the bottom copy, inside `C`. -/
theorem shrinkC_fixes (p : C(E, B)) (b : B) (t : unitInterval) {y : ↥(excUc p b)}
    (hy : (y : cyl p) ∈ cylBot p) : shrinkC p b t y = y := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [shrinkC_apply, shrinkPairC_coe, cylShrink_fixes_bot p t hy]
  rfl

/-- The shrink fixes the bottom copy, inside `Mb`. -/
theorem shrinkM_fixes (p : C(E, B)) (b : B) (t : unitInterval) {y : ↥(excUb p b)}
    (hy : (y : cyl p) ∈ cylBot p) : shrinkM p b t y = y := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [shrinkM_apply, shrinkPairM_coe, cylShrink_fixes_bot p t hy]
  rfl

/-- The shrink homotopy inside `C` fixes the bottom copy pointwise. -/
theorem shrinkHomC_fixes (p : C(E, B)) (b : B) (t : unitInterval) (y : ↥(excUc p b))
    (hy : (y : cyl p) ∈ cylBot p) : shrinkHomC p b (t, y) = y :=
  shrinkC_fixes p b t hy

/-- The shrink homotopy inside `Mb` fixes the bottom copy pointwise. -/
theorem shrinkHomM_fixes (p : C(E, B)) (b : B) (t : unitInterval) (y : ↥(excUb p b))
    (hy : (y : cyl p) ∈ cylBot p) : shrinkHomM p b (t, y) = y :=
  shrinkM_fixes p b t hy

/-- The shrink at time `1`, inside `C`, lands in `excAc`. -/
theorem shrinkC_one_mem_excAc (p : C(E, B)) (b : B) (y : ↥(excUc p b)) :
    ((shrinkC p b 1 y : ↥(excUc p b)) : ↥(excC p b)) ∈ excAc p b :=
  shrinkC_one_mem p b y

/-- The shrink at time `1`, inside `Mb`, lands in `excAb`. -/
theorem shrinkM_one_mem_excAb (p : C(E, B)) (b : B) (y : ↥(excUb p b)) :
    ((shrinkM p b 1 y : ↥(excUb p b)) : ↥(excM p b)) ∈ excAb p b :=
  shrinkM_one_mem p b y


/-! ## The inclusion of the fibre cone into the union, and the two shrink isomorphisms -/

/-- The inclusion of the fibre cone `Mb` into the union `C = A ∪ Mb`. -/
def inclMc (p : C(E, B)) (b : B) : C(↥(excM p b), ↥(excC p b)) where
  toFun x := ⟨(x : cyl p), Or.inr x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] theorem inclMc_apply (p : C(E, B)) (b : B) (x : ↥(excM p b)) :
    ((inclMc p b x : ↥(excC p b)) : cyl p) = (x : cyl p) := rfl

/-- The canonical homeomorphism identifying the fibre cone inside `C` with the fibre cone. -/
def mcHomeo (p : C(E, B)) (b : B) : ↥(excMc p b) ≃ₜ ↥(excM p b) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, Or.inr x.2⟩, x.2⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

@[simp] theorem mcHomeo_apply (p : C(E, B)) (b : B) (x : ↥(excMc p b)) :
    ((mcHomeo p b x : ↥(excM p b)) : cyl p) = (x : cyl p) := rfl

/-- **The shrink isomorphism `H^n(C, A) ≅ H^n(C, U)`.** -/
theorem isIso_shrinkC (p : C(E, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b))
      (excAc p b) (excUc p b) (fun x hx => excAc_subset_excUc p b hx) ℚ n) :=
  isIso_relCohMap_id_of_deformationRetract (excAc p b) (excUc p b) (excAc_subset_excUc p b)
    (shrinkC p b 1) (shrinkHomC p b)
    (fun t y hy => shrinkHomC_fixes p b t y hy)
    (fun y => shrinkC_one_mem_excAc p b y) n

/-- **The shrink isomorphism `H^n(Mb, Ab) ≅ H^n(Mb, Ub)`.** -/
theorem isIso_shrinkM (p : C(E, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excM p b))
      (excAb p b) (excUb p b) (fun x hx => excAb_subset_excUb p b hx) ℚ n) :=
  isIso_relCohMap_id_of_deformationRetract (excAb p b) (excUb p b) (excAb_subset_excUb p b)
    (shrinkM p b 1) (shrinkHomM p b)
    (fun t y hy => shrinkHomM_fixes p b t y hy)
    (fun y => shrinkM_one_mem_excAb p b y) n

/-! ## The excision isomorphism -/

/-- **Excision: the restriction `H^n(C, U) → H^n(Mb ∩ C, Mb ∩ C ∩ U)` is an isomorphism.** -/
theorem isIso_excision (p : C(E, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(excMc p b), ↥(excC p b)))
      {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUc p b)
      (fun x hx => hx) ℚ n) := by
  refine isIso_relCohMap_excision_of_interior ℚ (excUc p b) (excMc p b) ?_ n
  have hZ : ({x : ↥(excC p b) | x ∉ ({y : ↥(excC p b) | y ∉ excMc p b})} : Set ↥(excC p b))
      = excMc p b := by
    ext x
    by_cases hx : x ∈ excMc p b <;> simp [hx]
  have hh := Work.Cohomology.univ_eq_interior_union_compl (X := TopCat.of ↥(excC p b))
    (excUc p b) {y : ↥(excC p b) | y ∉ excMc p b} (closure_diff_excMc_subset p b)
  rw [hZ] at hh
  exact hh

/-- The inclusion `Mb ↪ C` carries the collar into the collar. -/
theorem inclMc_mem_cylCollar (p : C(E, B)) (b : B) {x : ↥(excM p b)}
    (hx : (x : cyl p) ∈ cylCollar p) :
    ((inclMc p b x : ↥(excC p b)) : cyl p) ∈ cylCollar p := by
  simpa using hx

/-- The inclusion `Mb ↪ C` carries the bottom copy into the bottom copy. -/
theorem inclMc_mem_cylBot (p : C(E, B)) (b : B) {x : ↥(excM p b)}
    (hx : (x : cyl p) ∈ cylBot p) :
    ((inclMc p b x : ↥(excC p b)) : cyl p) ∈ cylBot p := by
  simpa using hx

/-- **The excision isomorphism in the form `H^n(C, U) ≅ H^n(Mb, U ∩ Mb)`.** -/
theorem isIso_psi (p : C(E, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
      (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n) := by
  have hψ' : CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(excMc p b), ↥(excC p b)))
      {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUc p b)
      (fun x hx => hx) ℚ n) := isIso_excision p b n
  -- the homeomorphism of pairs `mcHomeo`
  have hhe : ∀ x : ↥(excMc p b),
      (x ∈ {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b})
        ↔ ((mcHomeo p b x : ↥(excM p b)) ∈ excUb p b) := fun x => Iff.rfl
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUb p b)
    (mcHomeo p b) hhe ℚ n
  haveI hg : CategoryTheory.IsIso (Work.Thom.relCohMap
      (mcHomeo p b : C(↥(excMc p b), ↥(excM p b)))
      {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUb p b)
      (fun x hx => (hhe x).mp hx) ℚ n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  -- functoriality of the pullback
  have hcomp := Work.Thom.relCohMap_compA
    {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUb p b) (excUc p b)
    (mcHomeo p b : C(↥(excMc p b), ↥(excM p b))) (inclMc p b)
    (fun x hx => (hhe x).mp hx) (fun x hx => inclMc_mem_cylCollar p b hx)
    (fun x hx => (hhe x).mp hx) ℚ n
  have hmap : (inclMc p b).comp (mcHomeo p b : C(↥(excMc p b), ↥(excM p b)))
      = (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(excMc p b), ↥(excC p b))) := by
    ext x; rfl
  have hψ'' : Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
        (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n
      ≫ Work.Thom.relCohMap (mcHomeo p b : C(↥(excMc p b), ↥(excM p b)))
          {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUb p b)
          (fun x hx => (hhe x).mp hx) ℚ n
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(excMc p b), ↥(excC p b)))
          {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUc p b)
          (fun x hx => hx) ℚ n := by
    rw [hcomp]
    exact Work.Thom.relCohMap_congrA _ (excUc p b) hmap
      (fun x hx => (hhe x).mp hx) (fun x hx => hx) ℚ n
  -- now `ψ ≫ (mcHomeo-pullback) = ψ'` is an isomorphism, and the second factor is one
  haveI hIso : CategoryTheory.IsIso (Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
        (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n
      ≫ Work.Thom.relCohMap (mcHomeo p b : C(↥(excMc p b), ↥(excM p b)))
          {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUb p b)
          (fun x hx => (hhe x).mp hx) ℚ n) := by
    rw [hψ'']
    exact hψ'
  exact CategoryTheory.IsIso.of_isIso_comp_right
    (Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
      (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n)
    (Work.Thom.relCohMap (mcHomeo p b : C(↥(excMc p b), ↥(excM p b)))
      {y : ↥(excMc p b) | (y : ↥(excC p b)) ∈ excUc p b} (excUb p b)
      (fun x hx => (hhe x).mp hx) ℚ n)


/-! ## The assembly -/

/-- **The restriction map `H^n(C, A) → H^n(Mb, Mb ∩ A)` is an isomorphism.**  It factors as
`H^n(C,A) ≅ H^n(C,U) ≅ H^n(Mb, U ∩ Mb) ≅ H^n(Mb, Ab)` through the collar `U`, and each factor is an
isomorphism. -/
theorem isIso_target (p : C(E, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
      (fun x hx => inclMc_mem_cylBot p b hx) ℚ n) := by
  -- the three isomorphisms
  haveI hφ : CategoryTheory.IsIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b))
      (excAc p b) (excUc p b) (fun x hx => excAc_subset_excUc p b hx) ℚ n) :=
    isIso_shrinkC p b n
  haveI hψ : CategoryTheory.IsIso (Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
      (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n) := isIso_psi p b n
  haveI hχ : CategoryTheory.IsIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excM p b))
      (excAb p b) (excUb p b) (fun x hx => excAb_subset_excUb p b hx) ℚ n) :=
    isIso_shrinkM p b n
  -- functoriality: the two factorisations of the same restriction map
  have hcomp : Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
        (fun x hx => excAc_subset_excUc p b hx) ℚ n
      ≫ Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
        (fun x hx => inclMc_mem_cylBot p b hx) ℚ n
      = Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
          (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n
        ≫ Work.Thom.relCohMap (ContinuousMap.id ↥(excM p b)) (excAb p b) (excUb p b)
          (fun x hx => excAb_subset_excUb p b hx) ℚ n := by
    rw [Work.Thom.relCohMap_compA (excAb p b) (excAc p b) (excUc p b) (inclMc p b)
        (ContinuousMap.id ↥(excC p b)) (fun x hx => inclMc_mem_cylBot p b hx)
        (fun x hx => excAc_subset_excUc p b hx)
        (fun x hx => excAc_subset_excUc p b (inclMc_mem_cylBot p b hx)) ℚ n,
      Work.Thom.relCohMap_compA (excAb p b) (excUb p b) (excUc p b)
        (ContinuousMap.id ↥(excM p b)) (inclMc p b) (fun x hx => excAb_subset_excUb p b hx)
        (fun x hx => inclMc_mem_cylCollar p b hx)
        (fun x hx => inclMc_mem_cylCollar p b (excAb_subset_excUb p b hx)) ℚ n]
    first
      | (simp only [ContinuousMap.id_comp, ContinuousMap.comp_id]
         exact Work.Thom.relCohMap_hcongrA (inclMc p b) (excAb p b) (excUc p b) _ _ ℚ n)
      | rfl
  -- hence the target map is an isomorphism
  have hff : Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
        (fun x hx => inclMc_mem_cylBot p b hx) ℚ n
      = (asIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
          (fun x hx => excAc_subset_excUc p b hx) ℚ n)).inv
        ≫ (Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
            (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n
          ≫ Work.Thom.relCohMap (ContinuousMap.id ↥(excM p b)) (excAb p b) (excUb p b)
            (fun x hx => excAb_subset_excUb p b hx) ℚ n) := by
    have hinv : (asIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b)
        (excUc p b) (fun x hx => excAc_subset_excUc p b hx) ℚ n)).inv
        ≫ Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
            (fun x hx => excAc_subset_excUc p b hx) ℚ n = 𝟙 _ :=
      (asIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
        (fun x hx => excAc_subset_excUc p b hx) ℚ n)).inv_hom_id
    calc Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
          (fun x hx => inclMc_mem_cylBot p b hx) ℚ n
        = 𝟙 _ ≫ Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
            (fun x hx => inclMc_mem_cylBot p b hx) ℚ n := (Category.id_comp _).symm
      _ = ((asIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
              (fun x hx => excAc_subset_excUc p b hx) ℚ n)).inv
            ≫ Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
              (fun x hx => excAc_subset_excUc p b hx) ℚ n)
          ≫ Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
              (fun x hx => inclMc_mem_cylBot p b hx) ℚ n := by rw [hinv]
      _ = (asIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
              (fun x hx => excAc_subset_excUc p b hx) ℚ n)).inv
            ≫ (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
                (fun x hx => excAc_subset_excUc p b hx) ℚ n
              ≫ Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
                (fun x hx => inclMc_mem_cylBot p b hx) ℚ n) := Category.assoc _ _ _
      _ = (asIso (Work.Thom.relCohMap (ContinuousMap.id ↥(excC p b)) (excAc p b) (excUc p b)
              (fun x hx => excAc_subset_excUc p b hx) ℚ n)).inv
            ≫ (Work.Thom.relCohMap (inclMc p b) (excUb p b) (excUc p b)
                (fun x hx => inclMc_mem_cylCollar p b hx) ℚ n
              ≫ Work.Thom.relCohMap (ContinuousMap.id ↥(excM p b)) (excAb p b) (excUb p b)
                (fun x hx => excAb_subset_excUb p b hx) ℚ n) := by rw [hcomp]
  rw [hff]
  infer_instance


/-! ## The requested lemma -/

/-- Excision for the union `C = A ∪ Mb` of the bottom copy `A = range (cylIncl p)` and the cone
`Mb = (cylRetract p)⁻¹{b}`: the restriction of relative cohomology `H^{r+1}(C,A) → H^{r+1}(Mb,Ab)`
(in the direction needed below) is **injective**.  Only the injectivity is claimed: surjectivity can
fail in non-`T1` bases (a reviewer's Sierpiński-space example), and injectivity is all the caller
needs. -/
theorem fibreExcisionIso (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Injective (Work.Thom.relCohMap
      (⟨fun x => ⟨(x : Work.Serre.cyl p), Or.inr x.2⟩,
        Continuous.subtype_mk continuous_subtype_val _⟩ :
        C(↥((Work.Serre.cylRetract p) ⁻¹' {b}),
          ↥((Set.range (Work.Serre.cylIncl p) ∪ (Work.Serre.cylRetract p) ⁻¹' {b}) :
            Set (Work.Serre.cyl p))))
      {x : ↥((Work.Serre.cylRetract p) ⁻¹' {b}) |
        (x : Work.Serre.cyl p) ∈ Set.range (Work.Serre.cylIncl p)}
      {x : ↥(((Set.range (Work.Serre.cylIncl p) ∪ (Work.Serre.cylRetract p) ⁻¹' {b}) :
          Set (Work.Serre.cyl p))) |
        (x : Work.Serre.cyl p) ∈ Set.range (Work.Serre.cylIncl p)}
      (fun x hx => hx) ℚ (r + 1)).hom := by
  show Function.Injective (Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
      (fun x hx => inclMc_mem_cylBot p b hx) ℚ (r + 1)).hom
  haveI : CategoryTheory.IsIso (Work.Thom.relCohMap (inclMc p b) (excAb p b) (excAc p b)
      (fun x hx => inclMc_mem_cylBot p b hx) ℚ (r + 1)) := isIso_target p b (r + 1)
  exact ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).injective

end

end Work.Serre
