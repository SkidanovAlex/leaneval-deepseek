import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Boundedness of `ζ` on a bounded slice of the critical strip

`ζ` has a single pole, at `s = 1`, and is holomorphic everywhere else.  On the
compact set `K = {s : 1/2 ≤ Re s ≤ 1, 3 ≤ |Im s| ≤ T}` (with `T ≥ 1`) the point
`1` is avoided, so `ζ` is continuous on `K`; a continuous function on a compact
set is bounded.  This file records the resulting quantitative statement.
-/

namespace Work.BMF

open Set Metric

theorem zeta_bdd_height (T : ℝ) (hT : 1 ≤ T) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 3 ≤ |t| → |t| ≤ T →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A := by
  set K : Set ℂ := {s : ℂ | 1/2 ≤ s.re ∧ s.re ≤ 1 ∧ 3 ≤ |s.im| ∧ |s.im| ≤ T} with hK
  -- `K` is closed.
  have hclosed : IsClosed K := by
    rw [hK]
    have h1 : IsClosed {s : ℂ | (1/2 : ℝ) ≤ s.re} :=
      isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {s : ℂ | s.re ≤ (1 : ℝ)} :=
      isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {s : ℂ | (3 : ℝ) ≤ |s.im|} :=
      isClosed_le continuous_const Complex.continuous_im.abs
    have h4 : IsClosed {s : ℂ | |s.im| ≤ T} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    simpa only [Set.ofPred_and] using (h1.inter (h2.inter (h3.inter h4)))
  -- `K` is bounded: it sits in the closed ball of radius `sqrt (1 + T^2) + 1`.
  have hbounded : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨Real.sqrt (1 + T ^ 2) + 1, ?_⟩
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsre : s.re ^ 2 ≤ 1 := by
      have h0 : 0 ≤ s.re := by linarith [hs.1]
      nlinarith [hs.1, hs.2.1, h0]
    have hsim : s.im ^ 2 ≤ T ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]
      exact hs.2.2.2
    have hsq : ‖s‖ ^ 2 ≤ 1 + T ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [hsre, hsim]
    calc ‖s‖ = Real.sqrt (‖s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg s)).symm
      _ ≤ Real.sqrt (1 + T ^ 2) := Real.sqrt_le_sqrt hsq
      _ ≤ Real.sqrt (1 + T ^ 2) + 1 := by linarith
  have hKcomp : IsCompact K :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩
  -- `ζ` is continuous on `K`, since `K` avoids the pole `s = 1`.
  have hcont : ContinuousOn riemannZeta K := by
    intro s hs
    rw [hK] at hs
    have hs1 : s ≠ 1 := by
      intro h
      have him0 : s.im = 0 := by rw [h]; simp
      have h3 : (3 : ℝ) ≤ |s.im| := hs.2.2.1
      rw [him0, abs_zero] at h3
      linarith
    exact (differentiableAt_riemannZeta hs1).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro σ t h1 h2 h3 h4
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  have him : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  have hm : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ K := by
    rw [hK]
    simp only [Set.mem_ofPred_eq, hre, him]
    exact ⟨h1, h2, h3, h4⟩
  calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := hC _ hm
    _ ≤ max C 1 := le_max_left C 1

end Work.BMF
