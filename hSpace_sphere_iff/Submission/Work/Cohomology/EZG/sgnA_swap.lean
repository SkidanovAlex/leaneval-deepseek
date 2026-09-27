import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

/-!
# Swapping two adjacent positions changes the shuffle sign

For a shuffle `A ⊆ Fin (n+1)` the sign `sgnA A = (-1) ^ invA A` counts, through `invA`, the
inversions `#{(i,j) : i ∈ A, j ∉ A, j < i}` of the shuffle.  The main ingredient here is the
closed formula

`invA S = (∑ i ∈ S, i.val) - (#S).choose 2`,

which makes it transparent that exchanging the membership of two *adjacent* positions `q` and
`q+1` (exactly one of which lies in `A`) keeps the cardinality but changes the value-sum by `±1`,
hence flips the sign.

This is the piece of the Eilenberg–Zilber shuffle bookkeeping used downstream: the shuffle lemma
computes the boundary of the shuffle chain of a pair of simplices, and the terms of the boundary
are obtained from the terms of the chain by exactly such an adjacent swap, whose sign change is
what `sgnA_swap` supplies.
-/

namespace Work.Cohomology.EZG

open Work.Cohomology

/-- The number of elements of the complement of `S` lying below `i`, plus the number of elements
of `S` lying below `i`, is `i.val` (there are exactly `i.val` elements of `Fin m` below `i`). -/
lemma card_compl_filter_add {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    ((Finset.univ \ S).filter (fun j : Fin m => j.val < i.val)).card
      + (S.filter (fun j : Fin m => j.val < i.val)).card = i.val := by
  have hdisj : Disjoint ((Finset.univ \ S).filter (fun j : Fin m => j.val < i.val))
      (S.filter (fun j : Fin m => j.val < i.val)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx hx'
    exact hx.1 hx'.1
  have hunion : ((Finset.univ \ S).filter (fun j : Fin m => j.val < i.val))
      ∪ (S.filter (fun j : Fin m => j.val < i.val))
      = Finset.univ.filter (fun j : Fin m => j.val < i.val) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro h
      by_cases hx : x ∈ S
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hx, h⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  exact card_filter_lt (le_of_lt i.isLt)

/-- The number of strictly ordered pairs of elements of `S` is `(#S).choose 2`, counted one
first coordinate at a time. -/
lemma sum_filter_card_choose {m : ℕ} (S : Finset (Fin m)) :
    (∑ i ∈ S, (S.filter (fun j => j.val < i.val)).card) = S.card.choose 2 := by
  have key : (∑ i ∈ S, (S.filter (fun j => j.val < i.val)).card)
      = ∑ i ∈ S, ∑ j ∈ S, (if j.val < i.val then (1:ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_filter]
  have key2 : ((S ×ˢ S).filter (fun x : Fin m × Fin m => x.2.val < x.1.val)).card
      = ∑ i ∈ S, ∑ j ∈ S, (if j.val < i.val then (1:ℕ) else 0) := by
    rw [Finset.card_filter, Finset.sum_product]
  have h := key.trans key2.symm
  rw [h]
  have h2 : ((S ×ˢ S).filter (fun x : Fin m × Fin m => x.2.val < x.1.val)).card
      = ((S ×ˢ S).filter (fun x : Fin m × Fin m => x.1 < x.2)).card := by
    have he : ((S ×ˢ S).filter (fun x : Fin m × Fin m => x.2.val < x.1.val))
        = ((S ×ˢ S).filter (fun x : Fin m × Fin m => x.2 < x.1)) := by
      ext x; simp only [Finset.mem_filter, Fin.lt_def]
    rw [he]
    refine Finset.card_bij (fun x _ => (x.2, x.1)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · intro x1 _ x2 _ hh
      simp only [Prod.mk.injEq] at hh
      exact Prod.ext hh.2 hh.1
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_product] at hy
      exact ⟨(y.2, y.1), by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hy.1.2, hy.1.1⟩, hy.2⟩, by simp⟩
  rw [h2, Finset.card_product_filter_lt]

/-- Closed formula for `invA`: `invA S = ∑ i ∈ S, i.val - (#S).choose 2`, as an identity in `ℤ`
(so that no natural-number truncation occurs). -/
lemma invA_formula {m : ℕ} (S : Finset (Fin m)) :
    (invA S : ℤ) = ((∑ i ∈ S, i.val : ℕ) : ℤ) - (S.card.choose 2 : ℤ) := by
  have h1 : (invA S : ℤ)
      = ∑ i ∈ S, (((Finset.univ \ S).filter (fun j : Fin m => j.val < i.val)).card : ℤ) := by
    rw [invA, Nat.cast_sum]
  have h2 : ∀ i ∈ S, (((Finset.univ \ S).filter (fun j : Fin m => j.val < i.val)).card : ℤ)
      = (i.val : ℤ) - ((S.filter (fun j : Fin m => j.val < i.val)).card : ℤ) := by
    intro i _
    have hc := card_compl_filter_add S i
    have hle : (S.filter (fun j : Fin m => j.val < i.val)).card ≤ i.val := by omega
    have he : ((Finset.univ \ S).filter (fun j : Fin m => j.val < i.val)).card
        = i.val - (S.filter (fun j : Fin m => j.val < i.val)).card := by omega
    rw [he, Nat.cast_sub hle]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
    sum_filter_card_choose]

/-- Replacing an element `c` of `S` by the next element `d` (`d.val = c.val + 1`) raises `invA`
by one. -/
lemma invA_swap_plus {m : ℕ} (S : Finset (Fin m)) {c d : Fin m}
    (hc : c ∈ S) (hd : d ∉ S) (hadj : d.val = c.val + 1) :
    (invA (insert d (S.erase c)) : ℤ) = (invA S : ℤ) + 1 := by
  have hdc : d ∉ S.erase c := by simp [Finset.mem_erase, hd]
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨c, hc⟩
  have hcard : (insert d (S.erase c)).card = S.card := by
    rw [Finset.card_insert_of_notMem hdc, Finset.card_erase_of_mem hc]
    omega
  have hsum : (∑ i ∈ insert d (S.erase c), i.val) = (∑ i ∈ S, i.val) + 1 := by
    rw [Finset.sum_insert hdc]
    have h1 := Finset.sum_erase_add S (fun i : Fin m => i.val) hc
    have h2 : c.val ≤ ∑ i ∈ S, i.val := Finset.single_le_sum (fun i _ => Nat.zero_le _) hc
    omega
  rw [invA_formula (insert d (S.erase c)), invA_formula S, hcard, hsum]
  push_cast
  ring

/-- Replacing an element `d` of `S` by the preceding element `c` (`d.val = c.val + 1`) lowers
`invA` by one. -/
lemma invA_swap_minus {m : ℕ} (S : Finset (Fin m)) {c d : Fin m}
    (hc : c ∉ S) (hd : d ∈ S) (hadj : d.val = c.val + 1) :
    (invA (insert c (S.erase d)) : ℤ) = (invA S : ℤ) - 1 := by
  have hcd : c ∉ S.erase d := by simp [Finset.mem_erase, hc]
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨d, hd⟩
  have hcard : (insert c (S.erase d)).card = S.card := by
    rw [Finset.card_insert_of_notMem hcd, Finset.card_erase_of_mem hd]
    omega
  have hsum : (∑ i ∈ S, i.val) = (∑ i ∈ insert c (S.erase d), i.val) + 1 := by
    rw [Finset.sum_insert hcd]
    have h1 := Finset.sum_erase_add S (fun i : Fin m => i.val) hd
    omega
  rw [invA_formula (insert c (S.erase d)), invA_formula S, hcard, hsum]
  push_cast
  ring

/-- Exchanging the membership of two adjacent positions `q` and `q+1` (exactly one of which
belongs to `A`) flips the shuffle sign. -/
theorem sgnA_swap {n : ℕ} (A : Finset (Fin (n + 1))) (q : Fin n)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) :
    sgnA (if q.castSucc ∈ A then insert q.succ (A.erase q.castSucc)
          else insert q.castSucc (A.erase q.succ)) = - sgnA A := by
  have hadj : (q.succ : Fin (n+1)).val = (q.castSucc : Fin (n+1)).val + 1 := by
    rw [Fin.val_succ, Fin.val_castSucc]
  by_cases hq : q.castSucc ∈ A
  · have hq' : q.succ ∉ A := h.mp hq
    rw [if_pos hq]
    have hkey := invA_swap_plus A hq hq' hadj
    have hnat : invA (insert q.succ (A.erase q.castSucc)) = invA A + 1 := by omega
    simp only [sgnA, hnat, pow_succ]
    ring
  · have hq' : q.succ ∈ A := by by_contra hc; exact hq (h.mpr hc)
    rw [if_neg hq]
    have hkey := invA_swap_minus A hq hq' hadj
    have hnat : invA A = invA (insert q.castSucc (A.erase q.succ)) + 1 := by omega
    simp only [sgnA, hnat, pow_succ]
    ring

end Work.Cohomology.EZG
