import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

/-!
# The shuffle sign after deleting a position (main case)

For a shuffle `A ⊆ Fin (n+1)` and a position `q : Fin n` such that *both* adjacent positions
`q.castSucc` and `q.succ` lie in `A`, we compute how `sgnA` changes when the position `q.succ`
is deleted (`delPosP A q.succ`).

The key invariant is the number of inversions `invA`: for `p ∈ A` one has
`invA A = invA (delPosP A p) + cntB A p.val` (`invA_delPosP`), because the bijection
`Fin.succAbove p` matches the elements of `A \ {p}` with `delPosP A p` while it preserves the
count of complement elements below each element, and the extra element `p ∈ A` contributes the
complement elements below `p`, i.e. `cntB A p.val`.  Reading this identity modulo `2` with
`cnt A p.val + cntB A p.val = p.val` gives the stated sign relation.
-/

namespace Work.Cohomology.EZG

/-- The elements of the complement of `A` below `p.succAbove i` correspond, under `Fin.succAbove p`,
to the complement elements of `delPosP A p` below `i`.  (Here `p ∈ A`, so deleting `p` is
"allowed": the complement of `A` misses `p`, which is precisely the point omitted by
`Fin.succAbove p`.) -/
lemma card_compl_filter_succAbove {n : ℕ} (A : Finset (Fin (n + 1))) (p : Fin (n + 1))
    (hp : p ∈ A) (i : Fin n) :
    ((Finset.univ \ A).filter (fun j : Fin (n + 1) => j.val < (p.succAbove i).val)).card
      = ((Finset.univ \ delPosP A p).filter (fun j : Fin n => j.val < i.val)).card := by
  refine (Finset.card_bij
    (fun (t : Fin n) (_ : t ∈ (Finset.univ \ delPosP A p).filter
        (fun j : Fin n => j.val < i.val)) => p.succAbove t) ?_ ?_ ?_).symm
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨htB, htlt⟩ := ht
    refine ⟨?_, ?_⟩
    · simpa only [mem_delPosP] using htB
    · exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr htlt))
  · intro t1 _ t2 _ h
    exact Fin.succAbove_right_injective h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
    obtain ⟨hjA, hjlt⟩ := hj
    have hjne : j ≠ p := fun h => hjA (h ▸ hp)
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hjne
    refine ⟨t, ?_, ht⟩
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [mem_delPosP, ht]; exact hjA
    · have h2 : p.succAbove t < p.succAbove i := ht.symm ▸ (Fin.lt_def.mpr hjlt)
      exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp h2)

/-- **Deleting a position of a shuffle, on the inversion number.**  If `p ∈ A ⊆ Fin (n+1)` then
`invA A = invA (delPosP A p) + cntB A p.val`. -/
lemma invA_delPosP {n : ℕ} (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (hp : p ∈ A) :
    invA A = invA (delPosP A p) + cntB A p.val := by
  have hA : A = (delPosP A p).image (p.succAbove) ∪ {p} := (insUp_delPosP hp).symm
  have hdisj : Disjoint ((delPosP A p).image (p.succAbove)) ({p} : Finset (Fin (n + 1))) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨t, _, ht⟩
    exact Fin.succAbove_ne p t ht
  rw [invA]
  nth_rewrite 1 [hA]
  rw [Finset.sum_union hdisj, Finset.sum_singleton]
  rw [Finset.sum_image (fun a _ b _ h => Fin.succAbove_right_injective h)]
  rw [Finset.sum_congr rfl (fun i _ => card_compl_filter_succAbove A p hp i)]
  rw [invA]
  congr 1

theorem sgnA_delPos_succ {n : ℕ} (A : Finset (Fin (n + 1))) (q : Fin n)
    (hq : q.castSucc ∈ A) (hq' : q.succ ∈ A) :
    sgnA A * (-1 : ℤ) ^ (q.val + 1)
      = sgnA (delPosP A q.succ) * (-1 : ℤ) ^ (cnt A (q.val + 1)) := by
  have hqv : ((q.succ : Fin (n + 1)).val) = q.val + 1 := rfl
  -- `cntB A (q.val + 1) = (q.val + 1) - cnt A (q.val + 1)`
  have hcntB : cntB A (q.val + 1) = (q.val + 1) - cnt A (q.val + 1) := by
    have h1 := cnt_add_cntB A (n := n + 1) (le_of_lt q.succ.isLt)
    rw [hqv] at h1
    omega
  have hle : cnt A (q.val + 1) ≤ q.val + 1 := by
    have h1 := cnt_add_cntB A (n := n + 1) (le_of_lt q.succ.isLt)
    rw [hqv] at h1
    omega
  -- inversion-number identity at `p = q.succ`
  have h2 : invA A = invA (delPosP A q.succ) + cntB A (q.val + 1) := by
    simpa only [hqv] using invA_delPosP A q.succ hq'
  have hexp : invA A + (q.val + 1)
      = invA (delPosP A q.succ) + cnt A (q.val + 1)
        + 2 * ((q.val + 1) - cnt A (q.val + 1)) := by
    rw [h2, hcntB]
    omega
  have hpow : (-1 : ℤ) ^ (invA A + (q.val + 1))
      = (-1 : ℤ) ^ (invA (delPosP A q.succ) + cnt A (q.val + 1)) := by
    rw [hexp, pow_add, pow_mul]
    norm_num
  simp only [sgnA]
  rw [← pow_add, ← pow_add]
  exact hpow

end Work.Cohomology.EZG
