import Submission.Work.ReachSigned

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# The image aggregate `es_m` for `a_m` — reachability subgoal 3 (construction)

For `a_m = of m` expressed in the basis images `w_i := α(a_i)`, the aggregate
is obtained from the inverse automorphism: `(α⁻¹(a_m)).toWord` is a reduced
word in the standard letters, and mapping each letter through `α` gives the
factor list `es_m` with `es_m.prod = a_m`, whose factors are the basis images
up to sign.  This module constructs that object and proves:

* `imageAggregateList_prod` — `(imageAggregateList α L).prod = α (mk L)` (the
  product of the `± w_i` factors is the image of the word `L`);
* `imageAggregate_prod_letter` — for `es := imageAggregate α m`,
  `es.prod = of m` (the aggregate composes to `a_m`; then by
  `AggregateProtocol.aggregate_reduce_letter` the aggregate word list
  reduces to the single letter);
* `imageAggregate_length` — `|es| = |(α⁻¹(a_m)).toWord|`;
* `imageAggregate_factors` — every factor is a basis image up to sign
  (`ImageAggregate α es`);
* **`exists_confined_image_aggregate`** — from a long image
  (`∃ i, 1 < |w_i|`) a standard generator `a_m` exists whose aggregate has a
  *confined* factor (combining `ReachSigned.exists_two_factor_letter` with
  `AggregateProtocol.aggregate_confined_factor`);
* **`aggregate_element_dichotomy`** — for a confined interior factor of the
  aggregate: either a product of two adjacent factors is strictly shorter
  than one of them (the strict phase, element level), or the balanced
  half-half state holds (`es[j].toWord = A ++ B`, `|A| = |B|`, neighbours
  covering the halves) — the element-level reflection of the word-level
  `T3Rebalance.t3_aggregate_step`.

`SystemReduced` of `es` (no trivial factors, no adjacent inverse pairs) is
the next micro-lemma; it needs the reduced-word no-adjacent-inverse-letter
fact and is used only by the `u ≠ p` selectors at attachment time.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The factor of the aggregate for the letter `l = (i, b)`: the basis image
`α(a_i)` if `b = true`, its inverse otherwise. -/
def imageFactor {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (l : Fin n × Bool) :
    FreeGroup (Fin n) :=
  if l.2 then α (FreeGroup.of l.1) else (α (FreeGroup.of l.1))⁻¹

/-- The image-aggregate factor list over the letter word `L`. -/
def imageAggregateList {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (L : List (Fin n × Bool)) : List (FreeGroup (Fin n)) :=
  L.map (imageFactor α)

/-- The aggregate for the standard generator `a_m` (factors are the letters
of `α⁻¹(a_m)` mapped through `α`). -/
def imageAggregate {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    List (FreeGroup (Fin n)) :=
  imageAggregateList α ((α⁻¹) (FreeGroup.of m)).toWord

/-- `mk [(i, true)] = of i`. -/
lemma mk_singleton_true {n : ℕ} (i : Fin n) :
    FreeGroup.mk [(i, true)] = FreeGroup.of i := by
  have h := FreeGroup.mk_toWord (x := FreeGroup.of i)
  rwa [FreeGroup.toWord_of] at h

/-- `mk [(i, false)] = (of i)⁻¹`. -/
lemma mk_singleton_false {n : ℕ} (i : Fin n) :
    FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := by
  have h := FreeGroup.mk_toWord (x := (FreeGroup.of i)⁻¹)
  rwa [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev] at h

/-- The product of the image factors equals the image of the word `L`:
`(imageAggregateList α L).prod = α (mk L)`. -/
lemma imageAggregateList_prod {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (L : List (Fin n × Bool)) :
    (imageAggregateList α L).prod = α (FreeGroup.mk L) := by
  induction L with
  | nil =>
      simp [imageAggregateList]
      have hmk : FreeGroup.mk ([] : List (Fin n × Bool)) = (1 : FreeGroup (Fin n)) := by
        rfl
      rw [hmk]
      exact (aut_map_one α).symm
  | cons l t ih =>
      change (imageFactor α l * (imageAggregateList α t).prod) =
        α (FreeGroup.mk (l :: t))
      rw [ih]
      have hfac : imageFactor α l = α (FreeGroup.mk [l]) := by
        unfold imageFactor
        cases l with
        | mk i b =>
            cases b with
            | true =>
                simp [mk_singleton_true i]
            | false =>
                simp [mk_singleton_false i]
      rw [hfac]
      have hpm : α (FreeGroup.mk [l] * FreeGroup.mk t) =
          α (FreeGroup.mk [l]) * α (FreeGroup.mk t) := by
        exact map_mul (α : FreeGroup (Fin n) →* FreeGroup (Fin n))
          (FreeGroup.mk [l]) (FreeGroup.mk t)
      rw [← hpm]
      apply congrArg (fun x : FreeGroup (Fin n) => α x)
      rw [FreeGroup.mul_mk]
      rfl

/-- The aggregate for `a_m` composes to `a_m`: `(imageAggregate α m).prod = of m`. -/
lemma imageAggregate_prod_letter {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    (imageAggregate α m).prod = FreeGroup.of m := by
  unfold imageAggregate
  rw [imageAggregateList_prod]
  have h := FreeGroup.mk_toWord (x := (α⁻¹) (FreeGroup.of m))
  rw [h]
  exact MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)

/-- The length of the aggregate is the length of the inverse-image word. -/
lemma imageAggregate_length {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    (imageAggregate α m).length = ((α⁻¹) (FreeGroup.of m)).toWord.length := by
  simp [imageAggregate, imageAggregateList]

/-- Every factor of the image aggregate is a basis image up to sign. -/
lemma imageAggregate_factor {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    ∀ g ∈ imageAggregate α m, IsImageFactor α g := by
  intro g hg
  unfold imageAggregate imageAggregateList at hg
  rcases (List.mem_map.mp hg) with ⟨l, hl, rfl⟩
  unfold imageFactor
  cases l with
  | mk i b =>
      cases b with
      | true => exact ⟨i, Or.inl rfl⟩
      | false => exact ⟨i, Or.inr rfl⟩

/-- The factors of the aggregate are basis images (`ImageAggregate`). -/
lemma imageAggregate_isImageAggregate {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (m : Fin n) :
    ImageAggregate α (imageAggregate α m) := by
  exact imageAggregate_factor α m

/-- **Confined factor from a long image.**  If some basis image has reduced
length ≥ 2, some standard generator has an aggregate with a *confined*
factor (the input of the strict/balanced dichotomy). -/
theorem exists_confined_image_aggregate {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hlong : ∃ j : Fin n, 1 < FreeGroup.norm (α (FreeGroup.of j))) :
    ∃ m : Fin n, ∃ j < (imageAggregate α m).length,
      Confined (aggregateWords (imageAggregate α m)) j := by
  rcases exists_two_factor_letter α hlong with ⟨m, hlen⟩
  have hprod : (imageAggregate α m).prod = FreeGroup.of m := imageAggregate_prod_letter α m
  have hk : 2 ≤ (imageAggregate α m).length := by
    rw [imageAggregate_length]
    exact hlen
  rcases aggregate_confined_factor (imageAggregate α m) m hprod hk with ⟨j, hj, hc⟩
  exact ⟨m, j, hj, hc⟩

/-- **Element-level strict/balanced dichotomy of the aggregate.**  For a
confined interior factor `j` of the aggregate (product of length ≤ 1), either
a product of two adjacent factors is strictly shorter than one of them (the
strict phase), or the balanced half-half state holds with the neighbours
covering the two halves.  (Element-level reflection of
`T3Rebalance.t3_aggregate_step`.) -/
theorem aggregate_element_dichotomy {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hjk : j + 1 < es.length)
    (hm : j - 1 < es.length) (hconf : Confined (aggregateWords es) j) :
    FreeGroup.norm ((es[j - 1]) * (es[j])) < FreeGroup.norm (es[j - 1]) ∨
    FreeGroup.norm ((es[j]) * (es[j + 1])) < FreeGroup.norm (es[j + 1]) ∨
    (∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z) := by
  classical
  let Fs : List (List (Fin n × Bool)) := aggregateWords es
  have hredF : ∀ L ∈ Fs, FreeGroup.IsReduced L := by
    intro L hL
    have hL' : L ∈ aggregateWords es := by simpa [Fs] using hL
    exact aggregateWords_reduced es L hL'
  have hjF : j < Fs.length := by rw [aggregateWords_length]; exact hj
  have hjkF : j + 1 < Fs.length := by rw [aggregateWords_length]; exact hjk
  have hmF : j - 1 < Fs.length := by rw [aggregateWords_length]; exact hm
  have hg_jm : Fs[j - 1] = (es[j - 1]).toWord := by
    rw [List.getElem_map]
  have hg_j : Fs[j] = (es[j]).toWord := by
    rw [List.getElem_map]
  have hg_jp : Fs[j + 1] = (es[j + 1]).toWord := by
    rw [List.getElem_map]
  rcases t3_aggregate_step Fs hredF (j := j) hjF hj0 hjkF hmF
    (by simpa [Fs] using hconf) with hsL | hsR | hbal
  · left
    -- |reduce (Fs[j-1] ++ Fs[j])| < |Fs[j-1]|
    calc
      FreeGroup.norm ((es[j - 1]) * (es[j]))
          = ((es[j - 1]) * (es[j])).toWord.length := rfl
      _ = (FreeGroup.reduce (Fs[j - 1] ++ Fs[j])).length := by
              rw [FreeGroup.toWord_mul]
              rw [← hg_jm, ← hg_j]
      _ < (Fs[j - 1]).length := hsL
      _ = FreeGroup.norm (es[j - 1]) := by rw [hg_jm]; rfl
  · right; left
    calc
      FreeGroup.norm ((es[j]) * (es[j + 1]))
          = ((es[j]) * (es[j + 1])).toWord.length := rfl
      _ = (FreeGroup.reduce (Fs[j] ++ Fs[j + 1])).length := by
              rw [FreeGroup.toWord_mul]
              rw [← hg_j, ← hg_jp]
      _ < (Fs[j + 1]).length := hsR
      _ = FreeGroup.norm (es[j + 1]) := by rw [hg_jp]; rfl
  · right; right
    rcases hbal with ⟨k, hlen, hlenA, hlenB, htail, hhead⟩
    let A : List (Fin n × Bool) := Fs[j].take k
    let B : List (Fin n × Bool) := Fs[j].drop k
    have hmid : (es[j]).toWord = A ++ B := by
      calc
        (es[j]).toWord = Fs[j] := hg_j.symm
        _ = (Fs[j].take k) ++ (Fs[j].drop k) := (List.take_append_drop k (Fs[j])).symm
        _ = A ++ B := by simp [A, B]
    have hlenA' : A.length = B.length := by
      have h1 : A.length = k := by
        unfold A
        rw [List.length_take]
        rw [min_eq_left]
        omega
      have h2 : B.length = k := by
        unfold B
        rw [List.length_drop]
        rw [hlen]
        omega
      omega
    have hleft : ∃ X : List (Fin n × Bool),
        (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by
      refine ⟨Fs[j - 1].take ((Fs[j - 1]).length - k), ?_⟩
      have htailA : (Fs[j - 1]).drop ((Fs[j - 1]).length - k) = FreeGroup.invRev A := by
        simpa [A] using htail
      calc
        (es[j - 1]).toWord = Fs[j - 1] := hg_jm.symm
        _ = (Fs[j - 1].take ((Fs[j - 1]).length - k))
              ++ (Fs[j - 1].drop ((Fs[j - 1]).length - k)) :=
              (List.take_append_drop ((Fs[j - 1]).length - k) (Fs[j - 1])).symm
        _ = (Fs[j - 1].take ((Fs[j - 1]).length - k)) ++ FreeGroup.invRev A := by
              rw [htailA]
    have hright : ∃ Z : List (Fin n × Bool),
        (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by
      refine ⟨Fs[j + 1].drop k, ?_⟩
      have hheadB : (Fs[j + 1]).take k = FreeGroup.invRev B := by
        simpa [B] using hhead
      calc
        (es[j + 1]).toWord = Fs[j + 1] := hg_jp.symm
        _ = (Fs[j + 1].take k) ++ (Fs[j + 1].drop k) :=
              (List.take_append_drop k (Fs[j + 1])).symm
        _ = FreeGroup.invRev B ++ (Fs[j + 1].drop k) := by
              rw [hheadB]
    rcases hleft with ⟨X, hX⟩
    rcases hright with ⟨Z, hZ⟩
    exact ⟨A, B, X, Z, hmid, hlenA', hX, hZ⟩

end Submission.Nielsen
