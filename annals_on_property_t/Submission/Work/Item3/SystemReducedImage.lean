import Submission.Work.Item3.EnergyBridge
import Submission.Work.ImageAggregate

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Image aggregates are `SystemReduced`

The factor list `imageAggregate α m` (the factors of the expression of the
standard generator `a_m` as a product of basis images, read off the reduced
word `((α⁻¹) a_m).toWord`) has no adjacent inverse factors and no identity
factor — the `SystemReduced` hypothesis the aggregate lemmas consume.  It
follows from the reducedness of `((α⁻¹) a_m).toWord`: adjacent inverse factors
would force adjacent inverse letters.

All lemmas kernel-checked.
-/

namespace Submission.Nielsen

/-- `imageFactor` of the inverted letter is the inverse factor. -/
lemma imageFactor_invRev {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (l : Fin n × Bool) :
    imageFactor α (l.1, !l.2) = (imageFactor α l)⁻¹ := by
  cases l with
  | mk i b => cases b <;> simp [imageFactor]

lemma imageFactor_ne_one {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (l : Fin n × Bool) :
    imageFactor α l ≠ 1 := by
  cases l with
  | mk i b =>
    cases b
    · simp only [imageFactor, Bool.false_eq_true, if_false]
      intro h
      have h2 := congrArg (fun x : FreeGroup (Fin n) => x⁻¹) h
      simp at h2
    · simp only [imageFactor, if_true]
      intro h
      exact FreeGroup.of_ne_one i (α.injective (by simpa using h))

/-- `imageFactor` is injective. -/
lemma imageFactor_injective {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {l l' : Fin n × Bool} (h : imageFactor α l = imageFactor α l') : l = l' := by
  cases l with
  | mk i b =>
    cases l' with
    | mk i' b' =>
      cases b <;> cases b' <;>
        simp only [imageFactor, if_true, Bool.false_eq_true, if_false] at h
      · -- (α (of i))⁻¹ = (α (of i'))⁻¹
        have h2 : FreeGroup.of i = FreeGroup.of i' := by
          apply α.injective
          have h3 := congrArg (fun x : FreeGroup (Fin n) => x⁻¹) h
          simpa using h3
        have h5 : ([(i, true)] : List (Fin n × Bool)) = [(i', true)] := by
          simpa using congrArg FreeGroup.toWord h2
        have h4 : i = i' := by simpa using h5
        subst h4
        rfl
      · -- (α (of i))⁻¹ = α (of i')
        exfalso
        have h2 : (FreeGroup.of i)⁻¹ = FreeGroup.of i' := by
          have h3 := congrArg (fun x : FreeGroup (Fin n) => α⁻¹ x) h
          simpa using h3
        have h5 := congrArg FreeGroup.toWord h2
        rw [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.toWord_of] at h5
        simp [FreeGroup.invRev] at h5
      · -- α (of i) = (α (of i'))⁻¹
        exfalso
        have h2 : FreeGroup.of i = (FreeGroup.of i')⁻¹ := by
          have h3 := congrArg (fun x : FreeGroup (Fin n) => α⁻¹ x) h
          simpa using h3
        have h5 := congrArg FreeGroup.toWord h2
        rw [FreeGroup.toWord_of, FreeGroup.toWord_inv, FreeGroup.toWord_of] at h5
        simp [FreeGroup.invRev] at h5
      · -- α (of i) = α (of i')
        have h2 : FreeGroup.of i = FreeGroup.of i' := α.injective h
        have h5 : ([(i, true)] : List (Fin n × Bool)) = [(i', true)] := by
          simpa using congrArg FreeGroup.toWord h2
        have h4 : i = i' := by simpa using h5
        subst h4
        rfl

/-- If two image factors are inverse to each other, the underlying letters are
inverse to each other. -/
lemma imageFactor_eq_inv_letter {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {l l' : Fin n × Bool} (h : imageFactor α l' = (imageFactor α l)⁻¹) :
    l' = (l.1, !l.2) :=
  imageFactor_injective α (by rw [h, imageFactor_invRev])

/-- Consecutive letters of a reduced word satisfy the no-cancellation relation. -/
lemma isReduced_rel_getElem {n : ℕ} {L : List (Fin n × Bool)} (h : FreeGroup.IsReduced L)
    {i : ℕ} (hi : i + 1 < L.length) :
    L[i].1 = L[i+1].1 → L[i].2 = L[i+1].2 := by
  have hchain := (List.isChain_iff_forall_rel_of_append_cons_cons).mp h
  have hdec : L = L.take i ++ L[i] :: L[i+1] :: L.drop (i + 2) := by
    conv_lhs => rw [← List.take_append_drop i L]
    congr 1
    have hd1 : List.drop i L = L[i] :: List.drop (i + 1) L :=
      List.drop_eq_getElem_cons (by omega : i < L.length)
    have hd2 : List.drop (i + 1) L = L[i + 1] :: List.drop (i + 2) L := by
      have := List.drop_eq_getElem_cons (l := L) (i := i + 1) (h := by omega)
      simpa [Nat.add_assoc] using this
    rw [hd1, hd2]
  exact hchain hdec

/-- Image-aggregate factor lists of reduced letter words are `SystemReduced`. -/
lemma systemReduced_imageAggregateList {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {L : List (Fin n × Bool)} (hL : FreeGroup.IsReduced L) :
    SystemReduced (imageAggregateList α L) := by
  unfold SystemReduced imageAggregateList
  constructor
  · intro g hg
    rcases List.mem_map.mp hg with ⟨l, _, rfl⟩
    exact imageFactor_ne_one α l
  · intro i hi h
    have hlen : i + 1 < L.length := by simpa using hi
    have h1 : imageFactor α L[i+1] = (imageFactor α L[i])⁻¹ := by
      simpa only [List.getElem_map] using h
    have h2 : L[i+1] = (L[i].1, !L[i].2) := imageFactor_eq_inv_letter α h1
    have h3 : L[i].1 = L[i+1].1 := by rw [h2]
    have h4 := isReduced_rel_getElem hL hlen h3
    rw [h2] at h4
    simp at h4

/-- **Image aggregates are `SystemReduced`** (no identity factor, no adjacent
inverse factors): they are the factor lists of the reduced word
`((α⁻¹) a_m).toWord`. -/
theorem systemReduced_imageAggregate {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    SystemReduced (imageAggregate α m) :=
  systemReduced_imageAggregateList α (FreeGroup.isReduced_toWord)

end Submission.Nielsen
