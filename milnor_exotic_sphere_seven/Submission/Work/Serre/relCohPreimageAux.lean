import Mathlib
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Serre.relCohTripleIsoOfVanishing
import Submission.Work.Serre.relCohomologyUnivVanishing
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.StemsB.RelCohomologyExcision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Toolbox for `Work.Serre.relCoh_pair_preimage_iso`

The lemmas collected here reduce the identification of the relative cohomology of the pair over the
old part of the base of a fibration to the cohomological algebra of a `N`-tuple of subsets of the
mapping cylinder:

* `Work.Serre.subsingleton_relCoh_of_homeomorph` — `Subsingleton` of relative cohomology transports
  along a homeomorphism of pairs;
* `Work.Serre.subtypeSubtypeHomeo_relCohPreimage`, `Work.Serre.subtypeSubtypeComm`,
  `Work.Serre.subsingleton_relCoh_subtypeSubtypeComm` — the canonical identifications of the
  nested subtypes `↥{x : ↥s | (x : α) ∈ t}` and the corresponding transport;
* `Work.Serre.isClosed_cylBot` — the bottom copy is closed in the mapping cylinder;
* `Work.Serre.cylBot_eq_cylLam_eq_zero` — the bottom copy is the zero locus of the collar
  coordinate, and `Work.Serre.excision_hZ` — the excision hypothesis for the pair `(A₂, U)`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]

/-! ## Transport of `Subsingleton` of relative cohomology along homeomorphisms of pairs -/

/-- **A homeomorphism of pairs induces an isomorphism of relative cohomology**, hence transports
`Subsingleton`. -/
theorem subsingleton_relCoh_of_homeomorph {R : Type} [CommRing R] {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (B : Set Y) (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) (h : Subsingleton (Work.Thom.RelCoh R n Y B)) :
    Subsingleton (Work.Thom.RelCoh R n X A) := by
  obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph A B e he R n
  exact ⟨fun a b => iso.toLinearEquiv.symm.injective (Subsingleton.elim _ _)⟩

/-! ## Nested subtypes -/

/-- **The canonical homeomorphism `↥{x : ↥s | (x : α) ∈ t} ≃ₜ ↥(s ∩ t)`.** -/
def subtypeSubtypeHomeo_relCohPreimage {α : Type} [TopologicalSpace α] (s t : Set α) :
    ↥{x : ↥s | (x : α) ∈ t} ≃ₜ ↥(s ∩ t) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The canonical homeomorphism `↥{x : ↥s | (x : α) ∈ t} ≃ₜ ↥{x : ↥t | (x : α) ∈ s}`** between
the two presentations of the intersection `s ∩ t`. -/
def subtypeSubtypeComm {α : Type} [TopologicalSpace α] (s t : Set α) :
    ↥{x : ↥s | (x : α) ∈ t} ≃ₜ ↥{x : ↥t | (x : α) ∈ s} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The transport of `Subsingleton` of relative cohomology along `subtypeSubtypeComm`, for the
relative set cut out by a fixed subset `u`. -/
theorem subsingleton_relCoh_subtypeSubtypeComm {α : Type} [TopologicalSpace α] (s t u : Set α)
    (m : ℕ)
    (h : Subsingleton (Work.Thom.RelCoh ℚ m ↥{x : ↥t | (x : α) ∈ s}
      {y : ↥{x : ↥t | (x : α) ∈ s} | ((y : ↥t) : α) ∈ u})) :
    Subsingleton (Work.Thom.RelCoh ℚ m ↥{x : ↥s | (x : α) ∈ t}
      {y : ↥{x : ↥s | (x : α) ∈ t} | ((y : ↥s) : α) ∈ u}) := by
  refine subsingleton_relCoh_of_homeomorph _ _ (subtypeSubtypeComm s t) ?_ m h
  intro x
  show (((x : ↥s) : α) ∈ u) ↔ ((((subtypeSubtypeComm s t) x : ↥t) : α) ∈ u)
  rw [show (((subtypeSubtypeComm s t) x : ↥t) : α) = ((x : ↥s) : α) from rfl]

/-! ## The bottom copy is closed and is the zero locus of the collar coordinate -/

/-- **The bottom copy is the zero locus of the collar coordinate** (in the collar, no gluing
identifies a bottom point with anything else, so no other point has collar coordinate `0`). -/
theorem cylBot_eq_cylLam_eq_zero (q : C(X, Γ)) :
    cylBot q = {y : cyl q | (cylLam q y : ℝ) = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    show (cylLam q (cylIncl q x) : ℝ) = 0
    rw [cylLam_cylIncl]
    norm_num
  · intro hy
    induction y using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl p =>
        refine ⟨p.1, ?_⟩
        by_cases hp : (p.2 : ℝ) = 0
        · have hp' : p.2 = 0 := Subtype.ext hp
          rw [show p = (p.1, (0 : unitInterval)) from Prod.ext rfl hp']
          rfl
        · refine absurd ?_ hp
          have hz : ((cylLam q (cylMk q (Sum.inl p)) : unitInterval) : ℝ) = 0 := hy
          rw [cylLam_cylMk, cylLamFun_inl] at hz
          exact hz
      | inr γ =>
        have hz : ((cylLam q (cylMk q (Sum.inr γ)) : unitInterval) : ℝ) = 0 := hy
        rw [cylLam_cylMk, cylLamFun_inr] at hz
        norm_num at hz

/-- **The bottom copy is closed in the mapping cylinder.** -/
theorem isClosed_cylBot (q : C(X, Γ)) : IsClosed (cylBot q) := by
  rw [cylBot_eq_cylLam_eq_zero]
  exact isClosed_eq (continuous_subtype_val.comp (cylLam q).continuous) continuous_const

/-! ## The excision hypothesis for the pair `(A₂, U)` -/

/-- **The closure of `A₂ ∖ U` inside `A₂` is contained in the interior of the collar part of
`A₂`.**  Here `A₂ = cylPre q S ∪ cylBot q` and `U = cylPre q S`; a point of `A₂ ∖ U` lies in the
bottom copy, hence has collar coordinate `0`, so the same holds for all its limit points. -/
theorem excision_hZ (q : C(X, Γ)) (S : Set Γ) :
    closure {x : ↥(cylPre q S ∪ cylBot q) | (x : cyl q) ∈ cylPre q S → False} ⊆
      interior {x : ↥(cylPre q S ∪ cylBot q) | (x : cyl q) ∈ cylCollar q} := by
  have hC : {x : ↥(cylPre q S ∪ cylBot q) | (x : cyl q) ∈ cylCollar q}
      = (Subtype.val : ↥(cylPre q S ∪ cylBot q) → cyl q) ⁻¹' cylCollar q := rfl
  have hZ0 : {x : ↥(cylPre q S ∪ cylBot q) | (x : cyl q) ∈ cylPre q S → False}
      ⊆ (Subtype.val : ↥(cylPre q S ∪ cylBot q) → cyl q) ⁻¹' {y : cyl q | (cylLam q y : ℝ) = 0} := by
    intro x hx
    have hx' : (x : cyl q) ∈ cylBot q := by
      rcases x.2 with h | h
      · exact absurd h hx
      · exact h
    obtain ⟨x', hx'⟩ := hx'
    show (cylLam q (x : cyl q) : ℝ) = 0
    rw [← hx', cylLam_cylIncl]
    norm_num
  have hclosed : IsClosed ((Subtype.val : ↥(cylPre q S ∪ cylBot q) → cyl q) ⁻¹'
      {y : cyl q | (cylLam q y : ℝ) = 0}) :=
    IsClosed.preimage continuous_subtype_val
      (isClosed_eq (continuous_subtype_val.comp (cylLam q).continuous) continuous_const)
  have hsub : closure {x : ↥(cylPre q S ∪ cylBot q) | (x : cyl q) ∈ cylPre q S → False}
      ⊆ (Subtype.val : ↥(cylPre q S ∪ cylBot q) → cyl q) ⁻¹' {y : cyl q | (cylLam q y : ℝ) = 0} :=
    (hclosed.closure_subset_iff).mpr hZ0
  have hopen : IsOpen {x : ↥(cylPre q S ∪ cylBot q) | (x : cyl q) ∈ cylCollar q} :=
    (isOpen_cylCollar q).preimage continuous_subtype_val
  rw [hopen.interior_eq]
  intro x hx
  have h := hsub hx
  show (x : cyl q) ∈ cylCollar q
  rw [mem_cylCollar_iff]
  rw [show (cylLam q (x : cyl q) : ℝ) = 0 from h]
  norm_num

/-! ## The general vanishing for an invariant part of the collar -/

/-- The shrink of an invariant part `Q` of the collar. -/
def cylShrinkSub (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q)
    (s : unitInterval) : C(↥Q, ↥Q) where
  toFun y := ⟨cylShrink q s (y : ↥(cylCollar q)), hinv s (y : ↥(cylCollar q)) y.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylShrink q s).continuous.comp continuous_subtype_val)
    (fun y => hinv s (y : ↥(cylCollar q)) y.2)

theorem cylShrinkSub_coe (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q)
    (s : unitInterval) (y : ↥Q) :
    ((cylShrinkSub q Q hinv s y : ↥Q) : cyl q)
      = ((cylShrink q s (y : ↥(cylCollar q)) : ↥(cylCollar q)) : cyl q) := rfl

/-- The joint shrink map of an invariant part of the collar, into that part. -/
def cylShrinkSubPair (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q) :
    C(unitInterval × ↥Q, ↥Q) where
  toFun p := ⟨cylShrinkHomotopy q (p.1, (p.2 : ↥(cylCollar q))),
    hinv p.1 (p.2 : ↥(cylCollar q)) p.2.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylShrinkHomotopy q).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun p => hinv p.1 (p.2 : ↥(cylCollar q)) p.2.2)

theorem cylShrinkSubPair_coe (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q)
    (p : unitInterval × ↥Q) :
    ((cylShrinkSubPair q Q hinv p : ↥Q) : cyl q)
      = ((cylShrinkHomotopy q (p.1, (p.2 : ↥(cylCollar q))) : ↥(cylCollar q)) : cyl q) := rfl

theorem cylShrinkSubPair_toFun_coe (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q)
    (p : unitInterval × ↥Q) :
    (((cylShrinkSubPair q Q hinv).toFun p : ↥Q) : ↥(cylCollar q))
      = (cylShrinkHomotopy q (p.1, (p.2 : ↥(cylCollar q))) : ↥(cylCollar q)) := rfl

/-- The restricted shrink homotopy of an invariant part of the collar. -/
def cylShrinkSubHomotopy (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥Q) (cylShrinkSub q Q hinv 1) where
  toContinuousMap := cylShrinkSubPair q Q hinv
  map_zero_left := fun y => by
    refine Subtype.ext ?_
    exact (cylShrinkSubPair_toFun_coe q Q hinv ((0 : unitInterval), y)).trans
      ((cylShrinkHomotopy q).map_zero_left (y : ↥(cylCollar q)))
  map_one_left := fun y => by
    refine Subtype.ext ?_
    exact (cylShrinkSubPair_toFun_coe q Q hinv ((1 : unitInterval), y)).trans
      (((cylShrinkHomotopy q).map_one_left (y : ↥(cylCollar q))).trans
        (by rfl))

/-- **Vanishing of the relative cohomology of a shrink-invariant part of the collar**, relative to
the bottom copy: the shrink `cylShrink q s` restricted to `Q` is a homotopy of pairs from the
identity to the retraction of `Q` onto its bottom part. -/
theorem relCoh_invariantSub_vanishing (q : C(X, Γ)) (Q : Set ↥(cylCollar q))
    (hinv : ∀ (s : unitInterval) (y : ↥(cylCollar q)), y ∈ Q → cylShrink q s y ∈ Q)
    (k : ℕ) :
    Subsingleton (Work.Thom.RelCoh ℚ k ↥Q {y : ↥Q | (y : cyl q) ∈ cylBot q}) := by
  set A : Set ↥Q := {y | (y : cyl q) ∈ cylBot q} with hA
  have hid : ∀ y ∈ A, (ContinuousMap.id ↥Q) y ∈ A := fun y hy => hy
  have hr : ∀ y ∈ A, cylShrinkSub q Q hinv 1 y ∈ A := by
    intro y hy
    show ((cylShrink q 1 (y : ↥(cylCollar q)) : ↥(cylCollar q)) : cyl q) ∈ cylBot q
    rw [cylShrink_fixes_bot q 1 hy]
    exact hy
  have hH : ∀ (s : unitInterval) (y : ↥Q), y ∈ A → cylShrinkSubHomotopy q Q hinv (s, y) ∈ A := by
    intro s y hy
    show ((cylShrinkHomotopy q (s, (y : ↥(cylCollar q))) : ↥(cylCollar q)) : cyl q) ∈ cylBot q
    rw [cylShrinkHomotopy_apply, cylShrink_fixes_bot q s hy]
    exact hy
  have h1 : Work.Thom.relCohMap (ContinuousMap.id ↥Q) A A hid ℚ k
      = Work.Thom.relCohMap (cylShrinkSub q Q hinv 1) A A hr ℚ k :=
    Work.Thom.relCohMap_homotopic A A hid hr (cylShrinkSubHomotopy q Q hinv) hH ℚ k
  rw [Work.Thom.relCohMap_idA A ℚ k] at h1
  let inclA : C(↥A, ↥Q) := ⟨Subtype.val, continuous_subtype_val⟩
  let toA : C(↥Q, ↥A) :=
    ⟨fun y => ⟨cylShrinkSub q Q hinv 1 y, cylShrink_one_mem_cylBot q (y : ↥(cylCollar q))⟩,
      Continuous.subtype_mk (cylShrinkSub q Q hinv 1).continuous
        (fun y => cylShrink_one_mem_cylBot q (y : ↥(cylCollar q)))⟩
  have hcomp : inclA.comp toA = cylShrinkSub q Q hinv 1 := rfl
  have hincl : ∀ b ∈ (Set.univ : Set ↥A), inclA b ∈ A := fun b _ => b.2
  have hr' : ∀ y ∈ A, toA y ∈ (Set.univ : Set ↥A) := fun y hy => trivial
  have hgf : ∀ y ∈ A, inclA (toA y) ∈ A := fun y hy => hincl _ (hr' y hy)
  haveI : Subsingleton (Work.Thom.RelCoh ℚ k ↥A Set.univ) :=
    relCohomologyUnivVanishing ℚ (TopCat.of ↥A) k
  have hz : Work.Thom.relCohMap toA A Set.univ hr' ℚ k = 0 :=
    hom_eq_zero_of_subsingleton_src _
  have hzero : (𝟙 (Work.Thom.RelCoh ℚ k ↥Q A)) = 0 := by
    rw [h1]
    rw [show Work.Thom.relCohMap (cylShrinkSub q Q hinv 1) A A hr ℚ k
        = Work.Thom.relCohMap (inclA.comp toA) A A hgf ℚ k from rfl]
    rw [← Work.Thom.relCohMap_compA A Set.univ A toA inclA hr' hincl hgf ℚ k, hz, comp_zero]
  exact subsingleton_of_id_eq_zero_general hzero

end

end Work.Serre
