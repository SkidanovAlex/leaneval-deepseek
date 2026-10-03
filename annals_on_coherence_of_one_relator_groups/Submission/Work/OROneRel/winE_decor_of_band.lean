import Mathlib
import Submission.Work.OROneRel.winBandDefs
import Submission.Work.OROneRel.band_of_winE_decor

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The levels of the decorated letters.**  The `j`-th decorated letter of `decor c i L` runs from
the level `i + lsig c (L.take j)` to the level `i + lsig c (L.take (j+1))`.  This is the
level-indexed reading of the walk, and it is the bridge between `band` (a condition on the levels
`lsig c (L.take k)`, `k ≤ L.length`) and `winE` (a condition on the edges `coverEdge q`). -/
private lemma mem_decor_exists (c : α → ℤ) :
    ∀ (L : List (α × Bool)) (i : ℤ) (q : (α × ℤ) × Bool), q ∈ decor c i L →
      ∃ j : ℕ, j < L.length ∧ coverSrc c q = i + lsig c (L.take j) ∧
        coverTgt c q = i + lsig c (L.take (j + 1)) := by
  intro L
  induction L with
  | nil =>
      intro i q hq
      simp [decor] at hq
  | cons p L' ih =>
      intro i q hq
      rw [decor_cons'] at hq
      rcases List.mem_cons.mp hq with hq | hq
      · rw [hq]
        refine ⟨0, by simp, ?_, ?_⟩
        · rw [coverSrc_head_decor, List.take_zero, lsig_nil']
          ring
        · rw [coverTgt_head_decor]
          have h1 : (p :: L').take 1 = [p] := rfl
          rw [h1, lsig_singleton']
      · obtain ⟨j, hj, hsrc, htgt⟩ := ih (i + linc c p) q hq
        refine ⟨j + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · rw [hsrc, List.take_succ_cons, lsig_cons']
          ring
        · rw [htgt, show (p :: L').take (j + 1 + 1) = p :: L'.take (j + 1) from
              List.take_succ_cons .., lsig_cons']
          ring

theorem winE_decor_of_band {α : Type u} (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool))
    (h : Work.OROneRel.band c lo hi L) :
    ∀ q ∈ Work.OROneRel.decor c 0 L,
      Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi := by
  intro q hq
  rw [coverEdge_mem_winE_iff]
  obtain ⟨j, hj, hsrc, htgt⟩ := mem_decor_exists c L 0 q hq
  have hjle : j ≤ L.length := le_of_lt hj
  have hj1le : j + 1 ≤ L.length := hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsrc]; simpa using (h j hjle).1
  · rw [hsrc]; simpa using (h j hjle).2
  · rw [htgt]; simpa using (h (j + 1) hj1le).1
  · rw [htgt]; simpa using (h (j + 1) hj1le).2

end Work.OROneRel
