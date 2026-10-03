/-
# `lsig` as the weighted sum of the exponent sums of a word

`Work.OROneRel.lsig c L` is the total weight of the word `L`, i.e. `∑_{p ∈ L} ± c p.1`.  This file
splits that sum according to the *letter*: the weight is the sum over the letters `y` of `c y` times
the exponent sum `wordEps y L` of `y` in `L`.

This is the elementary identity which converts the level of a Fox occurrence term
(`Work.ORLyndon.levelOfC_occTerm`, a value of `lsig` on a prefix) into the value of the linear
functional `c ↦ ∑ y, c y * (exponent of y in the prefix)`, making the general separating-weight
lemma `Work.ORLyndon.exists_weight_unique_max` applicable to the level method.
-/
import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.MagnusRewrite

set_option autoImplicit false

universe u

namespace Work.ORLyndon

/-- **The weight of a word is the sum over its letters of `c y` times the exponent sum of `y`.**

The hypothesis `hs` only says that the letters of `s` include all letters occurring in `L`; the
(other) letters of `s` contribute nothing since their exponent sum in `L` vanishes.  (All the
conditional expressions below are read in the `classical` context, so that they are syntactically the
ones occurring in the definitions of `lsig` and `wordEps`.) -/
theorem lsig_sum_wordEps {α : Type u} (c : α → ℤ) (L : List (α × Bool)) (s : Finset α)
    (hs : ∀ p ∈ L, p.1 ∈ s) :
    Work.OROneRel.lsig c L = ∑ y ∈ s, c y * Work.OROneRel.wordEps y L := by
  classical
  induction L with
  | nil => simp [Work.OROneRel.lsig, Work.OROneRel.wordEps]
  | cons p L ih =>
    have hs' : ∀ q ∈ L, q.1 ∈ s := fun q hq => hs q (List.mem_cons_of_mem p hq)
    have hcons : Work.OROneRel.lsig c (p :: L) =
        (if p.2 then c p.1 else -c p.1) + Work.OROneRel.lsig c L := by
      simp only [Work.OROneRel.lsig, List.map_cons, List.sum_cons]
    have hw : ∀ y : α, Work.OROneRel.wordEps y (p :: L) =
        (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)
          + Work.OROneRel.wordEps y L := by
      intro y
      simp only [Work.OROneRel.wordEps, List.map_cons, List.sum_cons]
    have hsum : (∑ y ∈ s, c y * Work.OROneRel.wordEps y (p :: L)) =
        (∑ y ∈ s, c y * ((if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)
          + Work.OROneRel.wordEps y L)) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hw y]
    have hdist : (∑ y ∈ s, c y * ((if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)
          + Work.OROneRel.wordEps y L))
        = (∑ y ∈ s, c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0))
          + (∑ y ∈ s, c y * Work.OROneRel.wordEps y L) := by
      rw [show (∑ y ∈ s, c y * ((if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)
            + Work.OROneRel.wordEps y L))
          = (∑ y ∈ s, (c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)
            + c y * Work.OROneRel.wordEps y L)) from
        Finset.sum_congr rfl (fun y _ => by rw [mul_add])]
      rw [Finset.sum_add_distrib]
    have hsingle : (∑ y ∈ s, c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0))
        = (if p.2 then c p.1 else -c p.1) := by
      rw [Finset.sum_eq_single p.1]
      · by_cases h : p.2 <;> simp [h]
      · intro y _ hne
        rw [if_neg (fun h => hne h.symm), mul_zero]
      · intro hnot
        exact absurd (hs p List.mem_cons_self) hnot
    rw [hcons, ih hs', hsum, hdist, hsingle]

/-- The same identity with the set of letters taken to be exactly the letters occurring in `L`. -/
theorem lsig_eq_sum_wordEps {α : Type u} [DecidableEq α] (c : α → ℤ) (L : List (α × Bool)) :
    Work.OROneRel.lsig c L = ∑ y ∈ (L.map Prod.fst).toFinset, c y * Work.OROneRel.wordEps y L :=
  lsig_sum_wordEps c L _ (fun p hp => by
    simp only [List.mem_toFinset]
    exact List.mem_map_of_mem hp)

end Work.ORLyndon
