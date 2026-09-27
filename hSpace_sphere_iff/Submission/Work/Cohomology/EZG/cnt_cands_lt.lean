import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

namespace Work.Cohomology.EZG

/-- If `p, q` both lie in `{0} ∪ (A.image Fin.succ) ⊆ Fin (N+1)` and `p < q` as natural numbers,
then `cnt A p.val < cnt A q.val`.

Indeed `q = b.succ` for some `b ∈ A`, and `p` is either `0` or `a.succ` for some `a ∈ A` with
`a < b`; in both cases `b` is an element of `A` lying in `[p.val, q.val)`, which forces `cnt` to
increase strictly. -/
theorem cnt_cands_lt {N : ℕ} (A : Finset (Fin N)) {p q : Fin (N + 1)}
    (hp : p ∈ insert 0 (A.image Fin.succ)) (hq : q ∈ insert 0 (A.image Fin.succ))
    (h : (p : ℕ) < (q : ℕ)) : cnt A p.val < cnt A q.val := by
  rw [Finset.mem_insert] at hq
  obtain hq0 | hqim := hq
  · -- `q = 0` contradicts `p < q`.
    subst hq0
    simp at h
  · obtain ⟨b, hbA, hbq⟩ := Finset.mem_image.mp hqim
    have hqv : (q : ℕ) = b.val + 1 := by rw [← hbq]; rfl
    -- `p` is `0` or `a.succ` with `a ∈ A`, and in the latter case `a < b`; so `p.val ≤ b.val`.
    have hpv : (p : ℕ) ≤ b.val := by
      rw [Finset.mem_insert] at hp
      rcases hp with hp0 | hpim
      · rw [hp0]; exact Nat.zero_le _
      · obtain ⟨a, _, hap⟩ := Finset.mem_image.mp hpim
        have hapv : (p : ℕ) = a.val + 1 := by rw [← hap]; rfl
        omega
    -- `b ∈ A` lies in `[p.val, q.val)`, so `cnt` increases strictly.
    exact cnt_lt_cnt A h b hbA hpv (by omega)

end Work.Cohomology.EZG
