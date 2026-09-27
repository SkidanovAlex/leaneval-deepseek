import Mathlib
import Submission.Work.Cohomology.EZG.dAux

namespace Work.Cohomology.EZG

open Work.Cohomology

/-- `swapA` exchanges the membership of the two adjacent positions `q.castSucc` and `q.succ` of a
shuffle `A`, so the complement changes only inside this pair.  Since `cntB` counts the elements of
the complement below a threshold `m`, the count is unaffected as long as `m ≠ q.succ`: either both
positions of the pair are `≥ m` (so neither is counted), or both are `< m` (so exactly one of them
is counted, before and after the swap). -/
theorem cntB_swapA_of_ne {N : ℕ} (A : Finset (Fin (N+1))) (q : Fin N)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) {m : ℕ} (hm1 : m ≤ N+1) (hm : m ≠ (q.succ : ℕ)) :
    Work.Cohomology.cntB A m = Work.Cohomology.cntB (Work.Cohomology.EZG.swapA N A q) m := by
  classical
  -- The transposition exchanging the two positions of the pair.
  let σ : Fin (N+1) → Fin (N+1) := Equiv.swap q.castSucc q.succ
  have hinvol : ∀ i : Fin (N+1), σ (σ i) = i := fun i => Equiv.swap_apply_self _ _ _
  -- `σ` preserves the threshold condition, because `m` is not the larger element of the pair.
  have hval : ∀ i : Fin (N+1), (σ i).val < m ↔ i.val < m := by
    intro i
    by_cases h1 : i = q.castSucc
    · subst h1
      have hσl : σ q.castSucc = q.succ := Equiv.swap_apply_left _ _
      rw [hσl]
      have hs : (q.succ : ℕ) = (q.castSucc : ℕ) + 1 := rfl
      omega
    · by_cases h2 : i = q.succ
      · subst h2
        have hσr : σ q.succ = q.castSucc := Equiv.swap_apply_right _ _
        rw [hσr]
        have hs : (q.succ : ℕ) = (q.castSucc : ℕ) + 1 := rfl
        omega
      · have hσn : σ i = i := Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [hσn]
  -- `σ` converts membership in `A` into membership in `swapA N A q`.
  have hmemA : ∀ i : Fin (N+1), σ i ∈ A ↔ i ∈ Work.Cohomology.EZG.swapA N A q := by
    intro i
    by_cases h1 : i = q.castSucc
    · subst h1
      have hσl : σ q.castSucc = q.succ := Equiv.swap_apply_left _ _
      rw [hσl]
      exact (Work.Cohomology.EZG.swapA_mem_castSucc A q h).symm
    · by_cases h2 : i = q.succ
      · subst h2
        have hσr : σ q.succ = q.castSucc := Equiv.swap_apply_right _ _
        rw [hσr]
        exact (Work.Cohomology.EZG.swapA_mem_succ A q h).symm
      · have hσn : σ i = i := Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [hσn]
        exact (Work.Cohomology.EZG.swapA_mem_of_ne A q h1 h2).symm
  -- Elementwise: `σ` carries the "complement below `m`" filter of `A` to that of `swapA`.
  have hiff : ∀ i : Fin (N+1),
      (i ∈ (Finset.univ \ Work.Cohomology.EZG.swapA N A q).filter (fun i => i.val < m)) ↔
      (σ i ∈ (Finset.univ \ A).filter (fun i => i.val < m)) := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(not_congr (hmemA i)).mpr h1, (hval i).mpr h2⟩,
           fun ⟨h1, h2⟩ => ⟨(not_congr (hmemA i)).mp h1, (hval i).mp h2⟩⟩
  -- Hence the two filters differ by the permutation `σ`, so they have the same cardinality.
  have himg : (Finset.univ \ Work.Cohomology.EZG.swapA N A q).filter (fun i => i.val < m) =
      ((Finset.univ \ A).filter (fun i => i.val < m)).image σ := by
    ext i
    rw [Finset.mem_image]
    constructor
    · intro hi
      exact ⟨σ i, (hiff i).mp hi, hinvol i⟩
    · rintro ⟨j, hj, rfl⟩
      have h2 : σ (σ j) ∈ (Finset.univ \ A).filter (fun i => i.val < m) := by
        rw [hinvol j]; exact hj
      exact (hiff (σ j)).mpr h2
  rw [Work.Cohomology.cntB, Work.Cohomology.cntB, himg,
    Finset.card_image_of_injective _ (Equiv.swap q.castSucc q.succ).injective]

end Work.Cohomology.EZG
