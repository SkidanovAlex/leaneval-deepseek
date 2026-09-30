import Mathlib
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Cohomology.cohomologicalExcision

/-!
# The "trimming" of the bottom copy: definitions and a restriction lemma

For a continuous map `q : C(X,B)` with mapping cylinder `cyl q`, collar `cylCollar q` and bottom
copy `cylBot q`, and for subsets `S ⊆ V ⊆ B`, the *trimming* isomorphism

  `H^n(C ∪ Q, Q) ≅ H^n(C, C ∩ Q)`,  `C = cylBot q ∩ cylPre q V`,  `Q = cylPre q S`,

is the content of `Work.Serre.DiscPair.relCoh_cylBot_trimming`.  This file fixes the notation used
by its two halves:

* `trimA q S`  — the union `cylBot q ∪ cylPre q S` inside the mapping cylinder;
* `trimAp q S V` — `trimA q S ∩ cylPre q V`, the part of that union lying over `V`;
* `trimC q V` — the bottom copy over `V`, `cylBot q ∩ cylPre q V`.

It also contains `relCoh_subtype_restrict`, the (bookkeeping) fact that the relative cohomology of
a pair of subtypes `{x : ↥P | (x : Y) ∈ R}` does not change when the subtype is flattened to
`↥(R ∩ P)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The union of the bottom copy of the mapping cylinder with the part of the cylinder over `S`. -/
def trimA (q : C(X, B)) (S : Set B) : Set (Work.Serre.cyl q) :=
  {y | y ∈ Work.Serre.cylBot q ∨ y ∈ Work.Serre.cylPre q S}

/-- The part of `trimA q S` lying over `V`. -/
def trimAp (q : C(X, B)) (S V : Set B) : Set (Work.Serre.cyl q) :=
  trimA q S ∩ Work.Serre.cylPre q V

/-- The bottom copy of the mapping cylinder, cut down to the part lying over `V`. -/
def trimC (q : C(X, B)) (V : Set B) : Set (Work.Serre.cyl q) :=
  Work.Serre.cylBot q ∩ Work.Serre.cylPre q V

@[simp] theorem mem_trimA (q : C(X, B)) (S : Set B) (y : Work.Serre.cyl q) :
    y ∈ trimA q S ↔ y ∈ Work.Serre.cylBot q ∨ y ∈ Work.Serre.cylPre q S := Iff.rfl

@[simp] theorem mem_trimAp (q : C(X, B)) (S V : Set B) (y : Work.Serre.cyl q) :
    y ∈ trimAp q S V ↔ (y ∈ Work.Serre.cylBot q ∨ y ∈ Work.Serre.cylPre q S) ∧
      y ∈ Work.Serre.cylPre q V := Iff.rfl

@[simp] theorem mem_trimC (q : C(X, B)) (V : Set B) (y : Work.Serre.cyl q) :
    y ∈ trimC q V ↔ y ∈ Work.Serre.cylBot q ∧ y ∈ Work.Serre.cylPre q V := Iff.rfl

theorem trimAp_subset_trimA (q : C(X, B)) (S V : Set B) : trimAp q S V ⊆ trimA q S :=
  Set.inter_subset_left

theorem trimAp_subset_pre (q : C(X, B)) (S V : Set B) :
    trimAp q S V ⊆ Work.Serre.cylPre q V := Set.inter_subset_right

theorem trimC_subset_trimAp (q : C(X, B)) (S V : Set B) : trimC q V ⊆ trimAp q S V :=
  fun _ hy => ⟨Or.inl hy.1, hy.2⟩

theorem trimAp_subset_collar (q : C(X, B)) (S V : Set B) :
    trimAp q S V ∩ Work.Serre.cylCollar q ⊆ Work.Serre.cylCollar q := Set.inter_subset_right

/-- The bottom copy lies below the top: a point of `cylBot q` has collar coordinate `0`. -/
theorem cylLam_eq_zero_of_mem_cylBot (q : C(X, B)) {y : Work.Serre.cyl q}
    (hy : y ∈ Work.Serre.cylBot q) : Work.Serre.cylLam q y = 0 := by
  obtain ⟨x, rfl⟩ := hy
  rw [Work.Serre.cylLam_cylIncl]

/-- Monotonicity of `cylPre`. -/
theorem cylPre_mono (q : C(X, B)) {S V : Set B} (hSV : S ⊆ V) :
    Work.Serre.cylPre q S ⊆ Work.Serre.cylPre q V :=
  fun _ hy => hSV hy

/-- **Restriction of a relative cohomology pair to a flattened subtype.**  The pair
`({x : ↥P | (x : Y) ∈ R}, {x : ↥P | (x : Y) ∈ R ∧ (x : Y) ∈ A})` has the same relative cohomology as
the pair `(↥(R ∩ P), ↥(R ∩ P ∩ A))`. -/
theorem relCoh_subtype_restrict {Y : Type} [TopologicalSpace Y] (P R A : Set Y)
    (R' : Type) [CommRing R'] (n : ℕ) :
    Nonempty (Work.Thom.RelCoh R' n ↥{x : ↥P | (x : Y) ∈ R}
        {y : ↥{x : ↥P | (x : Y) ∈ R} | ((y : ↥P) : Y) ∈ A}
      ≅ Work.Thom.RelCoh R' n ↥(R ∩ P) {y : ↥(R ∩ P) | (y : Y) ∈ A}) := by
  let e : ↥{x : ↥P | (x : Y) ∈ R} ≃ₜ ↥(R ∩ P) :=
    { toFun := fun t => ⟨(t : ↥P), ⟨t.2, (t : ↥P).2⟩⟩
      invFun := fun s => ⟨⟨(s : Y), s.2.2⟩, s.2.1⟩
      left_inv := fun t => Subtype.ext (Subtype.ext rfl)
      right_inv := fun s => Subtype.ext rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have he : ∀ t : ↥{x : ↥P | (x : Y) ∈ R},
      (t ∈ {y : ↥{x : ↥P | (x : Y) ∈ R} | ((y : ↥P) : Y) ∈ A} ↔
        e t ∈ {y : ↥(R ∩ P) | (y : Y) ∈ A}) := fun t => Iff.rfl
  exact ⟨(Work.Thom.relCohHomeomorph _ _ e he R' n).some.symm⟩

end

end Work.Serre.DiscPair
