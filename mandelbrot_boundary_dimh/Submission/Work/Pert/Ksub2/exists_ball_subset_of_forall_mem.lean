import Mathlib

namespace Work.Pert.Ksub2

/-- Finitely many points `u, u+1, ..., u+n` all lying in an open set `s` admit a single
positive radius `r` such that the ball of radius `r` around each of them is contained in `s`. -/
theorem exists_ball_subset_of_forall_mem {s : Set ℂ} (hs : IsOpen s) {u : ℂ} {n : ℕ}
    (h : ∀ i : ℕ, i ≤ n → u + (i : ℂ) ∈ s) :
    ∃ r : ℝ, 0 < r ∧ ∀ i : ℕ, i ≤ n → Metric.ball (u + (i : ℂ)) r ⊆ s := by
  suffices H : ∀ n : ℕ, (∀ i : ℕ, i ≤ n → u + (i : ℂ) ∈ s) →
      ∃ r : ℝ, 0 < r ∧ ∀ i : ℕ, i ≤ n → Metric.ball (u + (i : ℂ)) r ⊆ s from H n h
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds (h 0 (le_refl 0)))
    exact ⟨r, hr, fun i hi => by rw [Nat.le_zero.mp hi]; simpa using hsub⟩
  | succ n ih =>
    intro h
    obtain ⟨r1, hr1, h1⟩ := ih (fun i hi => h i (le_trans hi (Nat.le_succ n)))
    obtain ⟨r2, hr2, h2⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds (h (n+1) (le_refl _)))
    refine ⟨min r1 r2, lt_min hr1 hr2, fun i hi => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · rw [heq]
      exact subset_trans (Metric.ball_subset_ball (min_le_right _ _)) h2
    · exact subset_trans (Metric.ball_subset_ball (min_le_left _ _)) (h1 i (Nat.lt_succ_iff.mp hlt))

end Work.Pert.Ksub2
