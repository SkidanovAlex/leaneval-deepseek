import Mathlib

namespace Work.KMTContract

/-- If `G : ℝ → ℂ` is continuous and supported in `{y | |y| < R}` while `K` is compact, then the
family of sup-norms `n ↦ ‖(y ↦ G (y + n))|_K‖` is summable over `ℤ`: only the integers `n` with
`|n| < R + M` (where `M` bounds `K`) give a non-zero term, so the family has finite support. -/
theorem summableShiftRestrict {G : ℝ → ℂ} (hG : Continuous G) {R : ℝ}
    (hR : ∀ y : ℝ, R ≤ |y| → G y = 0) (K : TopologicalSpace.Compacts ℝ) :
    Summable fun n : ℤ =>
      ‖((⟨G, hG⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
  -- A bound `M` for `K`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y ∈ (K : Set ℝ), |y| ≤ M := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℝ)).mp K.isCompact.isBounded
    exact ⟨r, fun y hy => by
      have h := hr hy
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      exact h⟩
  -- For `n ≥ R + M` the shifted function vanishes on `K`.
  have hzero_ge : ∀ n : ℤ, R + M ≤ (n:ℝ) →
      (‖((⟨G, hG⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) = 0 := by
    intro n hn
    rw [norm_eq_zero]
    ext y
    rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply]
    show G (↑y + (n:ℝ)) = 0
    apply hR
    have hy : |(y:ℝ)| ≤ M := hM _ y.2
    have h1 : -M ≤ (y:ℝ) := (abs_le.mp hy).1
    have h2 : R ≤ (y:ℝ) + (n:ℝ) := by linarith
    exact le_trans h2 (le_abs_self _)
  -- For `n ≤ -(R + M)` the shifted function vanishes on `K`.
  have hzero_le : ∀ n : ℤ, (n:ℝ) ≤ -(R + M) →
      (‖((⟨G, hG⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) = 0 := by
    intro n hn
    rw [norm_eq_zero]
    ext y
    rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply]
    show G (↑y + (n:ℝ)) = 0
    apply hR
    have hy : |(y:ℝ)| ≤ M := hM _ y.2
    have h1 : (y:ℝ) ≤ M := (abs_le.mp hy).2
    have h2 : (y:ℝ) + (n:ℝ) ≤ -R := by linarith
    have h3 : R ≤ -((y:ℝ) + (n:ℝ)) := by linarith
    exact le_trans h3 (neg_le_abs _)
  -- Only the finitely many integers in `[-⌈R + M⌉, ⌈R + M⌉]` can contribute.
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(⌈R + M⌉)) (⌈R + M⌉)) ?_
  intro n hn
  rw [Finset.mem_Icc, not_and_or] at hn
  rcases hn with hlt | hgt
  · rw [not_le] at hlt
    exact hzero_le n (by
      have h1 : ((-(⌈R + M⌉) : ℤ) : ℝ) ≤ -(R + M) := by
        have := Int.le_ceil (R + M)
        push_cast
        linarith
      have h2 : (n:ℝ) < ((-(⌈R + M⌉) : ℤ) : ℝ) := by exact_mod_cast hlt
      linarith)
  · rw [not_le] at hgt
    exact hzero_ge n (by
      have h1 : R + M ≤ ((⌈R + M⌉ : ℤ) : ℝ) := Int.le_ceil (R + M)
      have h2 : ((⌈R + M⌉ : ℤ) : ℝ) < (n:ℝ) := by exact_mod_cast hgt
      linarith)

end Work.KMTContract
