import Mathlib
import Submission.Work.WilE6.Base

namespace Work.WilE6

theorem norm_witness_iff (k : ℕ) (hk : 0 < k) (u : Fin k → ℝ) (t : ℝ) :
    (∃ (w : Fin k → ℝ) (w₀ : ℝ), (∀ i, u i ^ 2 - t ^ 2 + w i ^ 2 = 0) ∧
        (∃ j, u j ^ 2 = t ^ 2) ∧ t = w₀ ^ 2) ↔ t = dist u 0 := by
  have hcoord : ∀ i : Fin k, dist (u i) ((0 : Fin k → ℝ) i) = |u i| := by
    intro i; simp
  constructor
  · -- `→` : the witnesses force `t = max_i |u i| = dist u 0`.
    rintro ⟨w, w₀, hw, ⟨j, hj⟩, ht⟩
    have ht0 : 0 ≤ t := ht ▸ sq_nonneg w₀
    have hle : ∀ i, u i ^ 2 ≤ t ^ 2 := by
      intro i
      have := hw i
      nlinarith [sq_nonneg (w i)]
    have habs : ∀ i, |u i| ≤ t := by
      intro i
      have h1 : Real.sqrt (u i ^ 2) ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (hle i)
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq ht0] at h1
    have hdist_le : dist u 0 ≤ t := by
      rw [dist_pi_le_iff ht0]
      intro i
      rw [hcoord i]
      exact habs i
    have hjabs : |u j| = t := by
      have h1 : Real.sqrt (u j ^ 2) = Real.sqrt (t ^ 2) := by rw [hj]
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq ht0] at h1
    have hge : t ≤ dist u 0 := by
      calc t = |u j| := hjabs.symm
        _ = dist (u j) ((0 : Fin k → ℝ) j) := (hcoord j).symm
        _ ≤ dist u 0 := dist_le_pi_dist u 0 j
    exact le_antisymm hge hdist_le
  · -- `←` : from `t = dist u 0` build the witnesses.
    intro ht
    have ht0 : 0 ≤ t := ht.symm ▸ dist_nonneg
    have habs : ∀ i, |u i| ≤ t := by
      intro i
      have h1 : dist (u i) ((0 : Fin k → ℝ) i) ≤ dist u 0 := dist_le_pi_dist u 0 i
      rw [hcoord i, ← ht] at h1
      exact h1
    have hsq : ∀ i, u i ^ 2 ≤ t ^ 2 := by
      intro i
      have h1 := habs i
      nlinarith [mul_self_le_mul_self (abs_nonneg (u i)) h1, sq_abs (u i)]
    have hex : ∃ j : Fin k, u j ^ 2 = t ^ 2 := by
      by_cases hzero : t = 0
      · refine ⟨⟨0, hk⟩, ?_⟩
        have h1 : |u ⟨0, hk⟩| ≤ 0 := by simpa [hzero] using habs ⟨0, hk⟩
        have h2 : |u ⟨0, hk⟩| = 0 := le_antisymm h1 (abs_nonneg _)
        have h3 : u ⟨0, hk⟩ = 0 := abs_eq_zero.mp h2
        simp [h3, hzero]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hzero)
        by_contra hcon
        have hcon' : ∀ i, u i ^ 2 ≠ t ^ 2 := fun i h => hcon ⟨i, h⟩
        have hlt : ∀ i, dist (u i) ((0 : Fin k → ℝ) i) < t := by
          intro i
          have h1 : u i ^ 2 < t ^ 2 := lt_of_le_of_ne (hsq i) (hcon' i)
          have h2 : |u i| < |t| := sq_lt_sq.mp h1
          rw [abs_of_nonneg ht0] at h2
          rwa [hcoord i]
        have h3 : dist u 0 < t := by
          rw [dist_pi_lt_iff htpos]
          exact hlt
        linarith [ht, h3]
    refine ⟨fun i => Real.sqrt (t ^ 2 - u i ^ 2), Real.sqrt t, ?_, hex, ?_⟩
    · intro i
      have h1 : 0 ≤ t ^ 2 - u i ^ 2 := by linarith [hsq i]
      rw [Real.sq_sqrt h1]
      ring
    · rw [Real.sq_sqrt ht0]

end Work.WilE6
