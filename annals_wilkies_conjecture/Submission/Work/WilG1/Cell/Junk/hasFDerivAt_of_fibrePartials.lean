import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Cell.Stair.Basic
import Submission.Work.WilG1.Cell.Stair.exists_stair_decomp

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilG1.Cell.Junk

open Work.WilG1.Cell

theorem hasFDerivAt_of_fibrePartials {n : ℕ} (h : (Fin n → ℝ) → ℝ) {V : Set (Fin n → ℝ)}
    (hV : IsOpen V) {y : Fin n → ℝ} (hy : y ∈ V)
    (hex : ∀ i : Fin n, ∀ z ∈ V, DifferentiableAt ℝ (fibreMap h i z) (z i))
    (hcont : ∀ i : Fin n, ContinuousAt (junkP h i) y) :
    HasFDerivAt h (jet (fun i => junkP h i y)) y := by
  rw [hasFDerivAt_iff_tendsto]
  -- a ball around `y` contained in `V`
  obtain ⟨ρ, hρpos, hρball⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hy)
  have hρ : ∀ z : Fin n → ℝ, dist z y < ρ → z ∈ V := fun z hz => hρball hz
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- per-direction continuity moduli
  set ε' : ℝ := ε / ((n : ℝ) + 1) with hε'def
  have hε'pos : 0 < ε' := by positivity
  have hcont_eps : ∀ k : Fin n, ∃ δ > 0, ∀ z : Fin n → ℝ, dist z y < δ →
      dist (junkP h k z) (junkP h k y) < ε' :=
    fun k => Metric.continuousAt_iff.1 (hcont k) ε' hε'pos
  choose δ hδpos hδ using hcont_eps
  have hball : ∀ᶠ x in 𝓝 y, dist x y < ρ := Metric.ball_mem_nhds y hρpos
  have hdelta : ∀ᶠ x in 𝓝 y, ∀ k : Fin n, dist x y < δ k :=
    Filter.eventually_all.2 fun k =>
      Filter.mem_of_superset (Metric.ball_mem_nhds y (hδpos k)) fun x hx => by
        simpa [Metric.mem_ball] using hx
  -- the staircase decomposition, valid on the ball
  have hdec : ∀ᶠ x in 𝓝 y, ∀ k : Fin n, ∃ p : Fin n → ℝ, p ∈ V ∧ ‖p - y‖ ≤ ‖x - y‖ ∧
      h (stair x y ((k : ℕ) + 1)) - h (stair x y (k : ℕ)) = (x k - y k) * junkP h k p := by
    filter_upwards [hball] with x hx
    intro k
    refine Work.WilG1.Cell.Stair.exists_stair_decomp h hex k fun t ht => hρ _ ?_
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (stairSeg_sub_le' x y k ht) hx
  filter_upwards [hball, hdelta, hdec] with x _hxρ hxδ hxdec
  choose p hp using hxdec
  have hpV : ∀ k : Fin n, p k ∈ V := fun k => (hp k).1
  have hple : ∀ k : Fin n, ‖p k - y‖ ≤ ‖x - y‖ := fun k => (hp k).2.1
  have hpid : ∀ k : Fin n,
      h (stair x y ((k : ℕ) + 1)) - h (stair x y (k : ℕ)) = (x k - y k) * junkP h k (p k) :=
    fun k => (hp k).2.2
  -- expansion of the two sides
  have hrew1 : h x - h y = ∑ k : Fin n, (x k - y k) * junkP h k (p k) := by
    rw [← sum_stair_sub' h x y]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [stairSeg_succ, stairSeg_self]
    exact hpid k
  have hrew2 : jet (fun i => junkP h i y) (x - y) =
      ∑ k : Fin n, (x k - y k) * junkP h k y := by
    rw [jet_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.sub_apply]
  have hbound : ‖h x - h y - jet (fun i => junkP h i y) (x - y)‖ ≤
      ‖x - y‖ * ∑ k : Fin n, ‖junkP h k (p k) - junkP h k y‖ := by
    rw [hrew1, hrew2, ← Finset.sum_sub_distrib]
    calc ‖∑ k : Fin n, ((x k - y k) * junkP h k (p k) - (x k - y k) * junkP h k y)‖
        ≤ ∑ k : Fin n, ‖(x k - y k) * junkP h k (p k) - (x k - y k) * junkP h k y‖ :=
          norm_sum_le (Finset.univ : Finset (Fin n)) _
      _ = ∑ k : Fin n, ‖(x k - y k) * (junkP h k (p k) - junkP h k y)‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          ring
      _ = ∑ k : Fin n, ‖x k - y k‖ * ‖junkP h k (p k) - junkP h k y‖ := by
          simp only [norm_mul]
      _ ≤ ∑ k : Fin n, ‖x - y‖ * ‖junkP h k (p k) - junkP h k y‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hk : ‖x k - y k‖ ≤ ‖x - y‖ := by
            simpa [Pi.sub_apply] using norm_le_pi_norm (x - y) k
          exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      _ = ‖x - y‖ * ∑ k : Fin n, ‖junkP h k (p k) - junkP h k y‖ := by
          rw [Finset.mul_sum]
  -- each of the `n` summands is small
  have hterm : ∀ k : Fin n, ‖junkP h k (p k) - junkP h k y‖ < ε' := by
    intro k
    have hlt : dist (p k) y < δ k := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hple k) (hxδ k)
    have h1 : ‖junkP h k (p k) - junkP h k y‖ = dist (junkP h k (p k)) (junkP h k y) := by
      rw [Real.dist_eq, Real.norm_eq_abs]
    rw [h1]
    exact hδ k (p k) hlt
  have hsum_lt : ∑ k : Fin n, ‖junkP h k (p k) - junkP h k y‖ < ε := by
    have h1 : ∑ k : Fin n, ‖junkP h k (p k) - junkP h k y‖ ≤ ∑ _k : Fin n, ε' :=
      Finset.sum_le_sum fun k _ => (hterm k).le
    have h2 : ∑ _k : Fin n, ε' = (n : ℝ) * ε' := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (n : ℝ) * ε' < ε := by
      have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hkey : ((n : ℝ) + 1) * ε' = ε := by
        rw [hε'def, mul_div_assoc', mul_div_cancel_left₀ ε hpos]
      have : (n : ℝ) * ε' = ε - ε' := by linarith
      rw [this]
      linarith
    linarith
  -- conclusion
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
  rcases eq_or_ne ‖x - y‖ 0 with hz | hz
  · rw [hz, inv_zero, zero_mul]
    exact hε
  · calc ‖x - y‖⁻¹ * ‖h x - h y - jet (fun i => junkP h i y) (x - y)‖
        ≤ ‖x - y‖⁻¹ * (‖x - y‖ * ∑ k : Fin n, ‖junkP h k (p k) - junkP h k y‖) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg _))
      _ = ∑ k : Fin n, ‖junkP h k (p k) - junkP h k y‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
      _ < ε := hsum_lt

end Work.WilG1.Cell.Junk
