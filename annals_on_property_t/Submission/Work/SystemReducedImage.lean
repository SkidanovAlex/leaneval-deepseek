import Submission.Work.ImageAggregate
import Submission.Work.AggregateCoordinate

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# `SystemReduced (imageAggregate α m)`

The aggregate `es_m = imageAggregate α m` is a *reduced system word*: its
factors are the non-trivial basis images `±w_i` (an automorphism maps
generators to non-trivial elements), and no two adjacent factors are
inverses.  The latter is the letter-level fact that `(α⁻¹(a_m)).toWord` is a
reduced word: adjacent letters are never inverse letters
(`isChain_adjacent` instantiated with `IsReduced`'s chain relation), and an
adjacent inverse *factor pair* would pull back (through `α⁻¹`) to an adjacent
inverse *letter pair* (`imageFactor_inv_letter`, `mk_singleton_eq_inv_letter`).

This makes the `u ≠ p` selectors of `AggregateCoordinate`
(`witness_ne_right_minus`, `witness_ne_left_plus`, `witness_ne_right_plus'`,
`witness_ne_left_minus'`) applicable to `es_m`: the rebalanced witness is a
*different* system element than the balanced one.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- In a chain `IsChain R L`, adjacent elements satisfy `R`. -/
lemma isChain_adjacent {α : Type*} (R : α → α → Prop) {L : List α}
    (hL : List.IsChain R L) {j : ℕ} (hj : j + 1 < L.length) :
    R (L[j]) (L[j + 1]) := by
  induction hL generalizing j with
  | nil =>
      simp at hj
  | singleton =>
      simp at hj
  | cons_cons hab htail ih =>
      rename_i a b l
      cases j with
      | zero =>
          -- (a :: b :: l)[0] = a, (a :: b :: l)[1] = b
          simpa using hab
      | succ j' =>
          have hlen : (a :: b :: l).length = (b :: l).length + 1 := by simp
          have hjh : j' + 1 < (b :: l).length := by omega
          simpa using (ih (j := j') hjh)

/-- The reduced word of a single letter is the letter itself. -/
lemma mk_singleton_toWord {n : ℕ} (l : Fin n × Bool) :
    (FreeGroup.mk [l]).toWord = [l] := by
  cases l with
  | mk i b =>
      cases b with
      | true =>
          rw [mk_singleton_true i]
          rfl
      | false =>
          rw [mk_singleton_false i]
          rw [FreeGroup.toWord_inv]
          rfl

/-- An automorphism maps a generator to a non-trivial element. -/
lemma image_of_ne_one {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i : Fin n) :
    α (FreeGroup.of i) ≠ 1 := by
  intro hz
  have h := congrArg (fun x : FreeGroup (Fin n) => (α⁻¹) x) hz
  rw [MulAut.inv_apply_self (FreeGroup (Fin n)) α (FreeGroup.of i)] at h
  rw [aut_map_one (α⁻¹)] at h
  exact (FreeGroup.of_ne_one i) h

/-- The inverse of a non-trivial element is non-trivial. -/
lemma inv_ne_one_of_ne_one {G : Type*} [Group G] {x : G} (hx : x ≠ 1) : x⁻¹ ≠ 1 := by
  intro hz
  apply hx
  have h := congrArg (fun y : G => y⁻¹) hz
  simpa using h

/-- Applying `α⁻¹` to a factor returns the letter: `α⁻¹(f(l)) = mk [l]`. -/
lemma imageFactor_inv_letter {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (l : Fin n × Bool) :
    (α⁻¹) (imageFactor α l) = FreeGroup.mk [l] := by
  unfold imageFactor
  cases l with
  | mk i b =>
      cases b with
      | true =>
          simp
          exact (mk_singleton_true i).symm
      | false =>
          simp
          exact (mk_singleton_false i).symm

/-- Inverse factors correspond to inverse letters: `mk [l'] = (mk [l])⁻¹`
implies `l' = letterInv l`. -/
lemma mk_singleton_eq_inv_letter {n : ℕ} (l l' : Fin n × Bool)
    (h : FreeGroup.mk [l'] = (FreeGroup.mk [l])⁻¹) : l' = letterInv l := by
  have hw := congrArg FreeGroup.toWord h
  rw [mk_singleton_toWord l', FreeGroup.toWord_inv, mk_singleton_toWord l] at hw
  have hrev : FreeGroup.invRev [l] = [letterInv l] := by
    cases l with
    | mk i b => cases b <;> rfl
  rw [hrev] at hw
  simpa using hw

/-- Adjacent factors of an image-aggregate word are never inverses (the
letters `L` are reduced). -/
private lemma mapFactor_no_adjacent_inv {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {L : List (Fin n × Bool)} (hL : FreeGroup.IsReduced L) {i : ℕ}
    (hi : i + 1 < (L.map (imageFactor α)).length)
    (hi0 : i < (L.map (imageFactor α)).length) :
    (L.map (imageFactor α))[i + 1] ≠ ((L.map (imageFactor α))[i])⁻¹ := by
  intro h
  have hlen : i + 1 < L.length := by
    simpa [List.length_map] using hi
  have hj0 : i < L.length := by
    simpa [List.length_map] using hi0
  have hle : (L.map (imageFactor α))[i + 1] = imageFactor α (L[i + 1]) := by
    rw [List.getElem_map]
  have hle0 : (L.map (imageFactor α))[i] = imageFactor α (L[i]) := by
    rw [List.getElem_map]
  have h' : imageFactor α (L[i + 1]) = (imageFactor α (L[i]))⁻¹ := by
    rw [hle, hle0] at h
    exact h
  have hq : FreeGroup.mk [L[i + 1]] = (FreeGroup.mk [L[i]])⁻¹ := by
    have hq0 := congrArg (fun x : FreeGroup (Fin n) => (α⁻¹) x) h'
    rw [imageFactor_inv_letter α (L[i + 1])] at hq0
    rw [aut_map_inv (α⁻¹) (imageFactor α (L[i]))] at hq0
    rw [imageFactor_inv_letter α (L[i])] at hq0
    exact hq0
  have hletter : L[i + 1] = letterInv (L[i]) :=
    mk_singleton_eq_inv_letter (L[i]) (L[i + 1]) hq
  have hrel := isChain_adjacent (fun a b : Fin n × Bool => a.1 = b.1 → a.2 = b.2)
    hL hlen
  have h1 : (L[i]).1 = (L[i + 1]).1 := by
    rw [hletter]
    simp [letterInv]
  have hrel' : (L[i]).2 = (L[i + 1]).2 := hrel h1
  have hflip : (L[i + 1]).2 = !(L[i]).2 := by
    rw [hletter]
    simp [letterInv]
  rw [hflip] at hrel'
  cases (L[i]).2 with
  | true => simp at hrel'
  | false => simp at hrel'

/-- **The aggregate is a reduced system word**: no trivial factors, no
adjacent inverse pairs. -/
theorem SystemReduced_imageAggregate {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    SystemReduced (imageAggregate α m) := by
  classical
  constructor
  · -- (a) every factor is non-trivial
    intro g hg
    unfold imageAggregate imageAggregateList at hg
    rcases (List.mem_map.mp hg) with ⟨l, hl, rfl⟩
    unfold imageFactor
    cases l with
    | mk i b =>
        cases b with
        | true =>
            exact image_of_ne_one α i
        | false =>
            exact inv_ne_one_of_ne_one (image_of_ne_one α i)
  · -- (b) no adjacent inverse pairs
    intro i hi
    have hmain := mapFactor_no_adjacent_inv (α := α)
      (L := ((α⁻¹) (FreeGroup.of m)).toWord)
      (hL := (FreeGroup.isReduced_toWord (x := (α⁻¹) (FreeGroup.of m))))
      (i := i)
      (hi := by simpa [imageAggregate, imageAggregateList] using hi)
      (hi0 := by
        have hi' : i < (imageAggregate α m).length := by omega
        simpa [imageAggregate, imageAggregateList] using hi')
    -- the goal is definitionally the statement of `hmain`
    simpa [imageAggregate, imageAggregateList] using hmain

end Submission.Nielsen
