import Mathlib
import Submission.Work.Serre.DiscPair.cylBotTrimDefs
import Submission.Work.Cohomology.cohomologicalExcision

/-!
# Excision for the bottom-copy trimming

This file proves `Work.Serre.DiscPair.cylBotTrimExcision`, the *excision half* of the trimming
isomorphism of `Submission/Work/Serre/DiscPair/cylBotTrimDefs.lean`.

Let `q : C(X,B)`, `S ⊆ V ⊆ B`, `trimAp q S V = (cylBot q ∪ cylPre q S) ∩ cylPre q V`, and write
`Q = cylPre q S` for the part of the cylinder over `S`.  The statement is that the relative
cohomology of the pair `(trimAp q S V, trimAp q S V ∩ Q)` is that of its collar part, i.e. that of
`(trimAp q S V ∩ cylCollar q, trimAp q S V ∩ cylCollar q ∩ Q)`.

The proof is the one described in the docstring of the theorem: apply cohomological excision
(`Work.Cohomology.cohomologicalExcision`) in the ambient space `↥(trimAp q S V)`, with

* `A = {y : ↥(trimAp q S V) | (y : cyl q) ∈ cylPre q S}` and
* `Z = {y : ↥(trimAp q S V) | (y : cyl q) ∉ cylCollar q}`,

and then identify the excised space `↥{y | y ∉ Z}` with the collar part
`↥{y : ↥(trimAp q S V) | (y : cyl q) ∈ cylCollar q}` (the two sets are equal by `Set.ext` and
`not_not`) using `Work.Thom.relCohHomeomorph`.

The geometric input is `closure_compl_collar_subset_interior_pre` below: `Z` is closed because
`cylCollar q` is open; `Z` is contained in the open set `U = {λ > 1/2}`; and every point of
`trimAp q S V` with collar coordinate `> 1/2` lies over `S`, because `cylBot q ⊆ cylCollar q`
(`Work.Serre.DiscPair.cylLam_eq_zero_of_mem_cylBot`).  Hence `closure Z ⊆ interior A`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- **The geometric input of the bottom-copy excision.**  In `↥(trimAp q S V)`, the set of points
outside the collar has closure contained in the interior of the part lying over `S`.

Indeed, the complement of `cylCollar q` is closed and `cylBot q ⊆ cylCollar q`, so a point of
`trimAp q S V` outside the collar has collar coordinate `λ ≥ 1`; on the other hand the open set
`{λ > 1/2}` is contained in `trimAp q S V ∩ cylPre q S`: a point of `trimAp q S V` with `λ > 0` is
not in the bottom copy, hence must lie over `S` (it lies in `cylBot q ∪ cylPre q S`). -/
theorem closure_compl_collar_subset_interior_pre (q : C(X, B)) (S V : Set B) :
    closure {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∉ Work.Serre.cylCollar q} ⊆
      interior {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} := by
  -- `Z` is closed (`cylCollar q` is open).
  have hZclosed : IsClosed {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∉ Work.Serre.cylCollar q} :=
    (Work.Serre.isOpen_cylCollar q).isClosed_compl.preimage continuous_subtype_val
  rw [hZclosed.closure_eq]
  intro y hy
  have hy' : ¬ ((Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ) < 1) := hy
  have hle : (1 : ℝ) ≤ (Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ) := not_lt.mp hy'
  -- the open set `{λ > 1/2}` and its inclusion into the part lying over `S`.
  have hUopen : IsOpen {y : ↥(trimAp q S V) |
      (1 / 2 : ℝ) < (Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ)} :=
    isOpen_lt continuous_const
      (continuous_subtype_val.comp ((Work.Serre.cylLam q).continuous.comp continuous_subtype_val))
  have hUA : {y : ↥(trimAp q S V) |
        (1 / 2 : ℝ) < (Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ)} ⊆
      {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} := by
    intro y hy
    rcases (mem_trimAp q S V (y : Work.Serre.cyl q)).mp y.2 with ⟨h1 | h2, -⟩
    · -- a point of the bottom copy has collar coordinate `0`, contradiction with `λ > 1/2`
      exfalso
      have h0 : (Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ) = 0 :=
        congrArg Subtype.val (cylLam_eq_zero_of_mem_cylBot q h1)
      have hy'' : (1 / 2 : ℝ) < (Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ) := hy
      rw [h0] at hy''
      norm_num at hy''
    · exact h2
  refine interior_maximal hUA hUopen ?_
  show (1 / 2 : ℝ) < (Work.Serre.cylLam q (y : Work.Serre.cyl q) : ℝ)
  exact lt_of_lt_of_le (by norm_num) hle

/-- **Excision half of the bottom-copy trimming.**  For `q : C(X,B)`, `S ⊆ V ⊆ B`, writing
`trimAp q S V = (cylBot q ∪ cylPre q S) ∩ cylPre q V` for the part over `V` of the bottom copy
united with the cylinder over `S`, the relative cohomology of `(trimAp q S V, trimAp q S V ∩ Q)`
(`Q = cylPre q S`) is that of its collar part.

Intended proof: apply `Work.Cohomology.cohomologicalExcision ℚ (TopCat.of ↥(trimAp q S V)) A Z`
with `A = {y : ↥(trimAp q S V) | (y : cyl q) ∈ cylPre q S}` and
`Z = {y : ↥(trimAp q S V) | (y : cyl q) ∉ cylCollar q}`.  Here `Z` is closed (`cylCollar q` is open)
and `Z ⊆ A` because a point of `trimAp q S V` outside the collar is a top point `cylInr γ`, and
`cylBot q ⊆ cylCollar q`, so it must lie in `cylPre q S`.  For the interior condition, use the open
set `{y : ↥(trimAp q S V) | (1/2 : ℝ) < (cylLam q (y : cyl q) : ℝ)}`, which contains `Z` and is
contained in `A` (a point of `trimAp q S V` with collar coordinate `> 1/2` is not in `cylBot q` by
`Work.Serre.DiscPair.cylLam_eq_zero_of_mem_cylBot`, hence lies in `cylPre q S`).  Finally transport
the excision output, which is a `{y | y ∉ Z}`-subtype, to the stated nested subtype form using
`Work.Thom.relCohHomeomorph` (the two sets are equal by `Set.ext` and `not_not`). -/
theorem cylBotTrimExcision {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) (n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℚ n ↥(Work.Serre.DiscPair.trimAp q S V)
        {y : ↥(Work.Serre.DiscPair.trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      ≅ Work.Thom.RelCoh ℚ n
        ↥{y : ↥(Work.Serre.DiscPair.trimAp q S V) |
            (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q}
        {y : ↥{y : ↥(Work.Serre.DiscPair.trimAp q S V) |
              (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q} |
          (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) := by
  classical
  -- the geometric input of the excision
  have hZ := closure_compl_collar_subset_interior_pre q S V
  -- cohomological excision in `↥(trimAp q S V)`
  obtain ⟨e₁⟩ := Work.Cohomology.cohomologicalExcision ℚ (TopCat.of ↥(trimAp q S V))
      {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∉ Work.Serre.cylCollar q} hZ n
  -- the excised space is the collar part: `{y | y ∉ Z} = {y | y ∈ cylCollar q}`
  have hV : {y : ↥(trimAp q S V) | y ∉ {z : ↥(trimAp q S V) |
        (z : Work.Serre.cyl q) ∉ Work.Serre.cylCollar q}}
      = {y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q} := by
    ext y
    simp
  -- the identity of the underlying points is a homeomorphism of the two subtypes
  let e : ↥{y : ↥(trimAp q S V) | y ∉ {z : ↥(trimAp q S V) |
        (z : Work.Serre.cyl q) ∉ Work.Serre.cylCollar q}} ≃ₜ
      ↥{y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q} :=
    { toFun := fun t => ⟨t.1, hV ▸ t.2⟩
      invFun := fun s => ⟨s.1, hV.symm ▸ s.2⟩
      left_inv := fun t => Subtype.ext rfl
      right_inv := fun s => Subtype.ext rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  -- invariance of relative cohomology under this homeomorphism of pairs
  obtain ⟨e₂⟩ := Work.Thom.relCohHomeomorph
      {y : ↥{y : ↥(trimAp q S V) | y ∉ {z : ↥(trimAp q S V) |
          (z : Work.Serre.cyl q) ∉ Work.Serre.cylCollar q}} |
        (y : ↥(trimAp q S V)) ∈ {y : ↥(trimAp q S V) |
          (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}}
      {y : ↥{y : ↥(trimAp q S V) | (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q} |
        (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      e (fun _ => Iff.rfl) ℚ n
  exact ⟨e₁ ≪≫ e₂.symm⟩

end

end Work.Serre.DiscPair
