import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Filter Finset MeasureTheory
open scoped Topology

namespace NK.NUV2.HeckeLAbel

/-- The integral appearing in the Abel-summation representation of `LSeries` converges as
`σ → 1⁺`, by dominated convergence and the partial-sum bound. -/
private lemma tendsto_integral_partialSums (b : ℕ → ℂ) (θ C : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ‖∑ k ∈ Finset.Icc 1 N, b k‖ ≤ C * (N : ℝ) ^ θ) :
    Tendsto (fun σ : ℝ ↦ ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-((1 : ℂ) + 1)))) := by
  have hboundA : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k‖ ≤ C * t ^ θ := by
    intro t ht
    refine (hbd ⌊t⌋₊ (Nat.le_floor (n := 1) (by exact_mod_cast ht))).trans ?_
    have h1 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by linarith)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hθ0) hC
  have hmeasA : AEStronglyMeasurable (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k)
      (volume.restrict (Set.Ioi 1)) := by
    refine LocallyIntegrableOn.aestronglyMeasurable ?_
    have h := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) b (a := 1) (m := 1) zero_le_one
      (g := fun _ : ℝ ↦ (1 : ℂ)) (locallyIntegrableOn_const (1 : ℂ))
    simpa using h.mono_set Set.Ioi_subset_Ici_self
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 1)) (bound := fun t : ℝ ↦ C * t ^ (θ - 2)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun σ ↦ ?_
    refine hmeasA.mul ?_
    have hcont : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-((σ : ℂ) + 1))) (Set.Ioi 1) :=
      fun t ht ↦ (Complex.continuousAt_ofReal_cpow_const t _
        (Or.inr (by have := Set.mem_Ioi.mp ht; linarith))).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1 : ℝ) < σ := hσ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hA := hboundA t ht1.le
    have hnorm : ‖(t : ℂ) ^ (-((σ : ℂ) + 1))‖ = t ^ (-σ - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
      ring
    rw [norm_mul, hnorm]
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k‖ * t ^ (-σ - 1)
        ≤ (C * t ^ θ) * t ^ (-σ - 1) :=
          mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (θ - σ - 1) := by
          rw [mul_assoc, ← Real.rpow_add ht0]
          ring_nf
      _ ≤ C * t ^ (θ - 2) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1.le ?_) hC
          linarith
  · exact Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one) C
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := by have := Set.mem_Ioi.mp ht; linarith
    have hc : ContinuousAt (fun σ : ℝ ↦ (t : ℂ) ^ (-((σ : ℂ) + 1))) 1 := by
      have hfun : (fun σ : ℝ ↦ (t : ℂ) ^ (-((σ : ℂ) + 1))) =
          fun σ : ℝ ↦ ((t ^ (-σ - 1) : ℝ) : ℂ) := by
        funext σ
        rw [Complex.ofReal_cpow ht0.le]
        congr 1
        push_cast
        ring
      rw [hfun]
      exact Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_const_rpow ht0.ne').comp (by fun_prop))
    exact tendsto_const_nhds.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)

/-- If the partial sums of a sequence `b : ℕ → ℂ` are `O(N^θ)` for some `θ < 1`, and the `L`-series
of `b` converges absolutely at every real point `σ > 1`, then `LSeries b σ` has a finite limit as
`σ → 1⁺`.  (Abel summation / the standard convergence criterion for Dirichlet series whose partial
sums grow slower than linearly.) -/
theorem tendsto_LSeries_of_partial_sum_bound (b : ℕ → ℂ) (θ C : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : 0 ≤ C)
    (hbd : ∀ N : ℕ, 1 ≤ N → ‖∑ k ∈ Finset.Icc 1 N, b k‖ ≤ C * (N : ℝ) ^ θ)
    (hsum : ∀ σ : ℝ, 1 < σ → LSeriesSummable b (σ : ℂ)) :
    ∃ L : ℂ, Tendsto (fun σ : ℝ => LSeries b (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 L) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, b k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ θ := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) θ)]
    exact hbd n hn
  have hrep : ∀ σ : ℝ, 1 < σ → LSeries b (σ : ℂ) =
      (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-((σ : ℂ) + 1)) := by
    intro σ hσ
    exact LSeries_eq_mul_integral b hθ0 (by simpa using lt_trans hθ1 hσ) (hsum σ hσ) hO
  have hint := tendsto_integral_partialSums b θ C hθ0 hθ1 hC hbd
  refine ⟨∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-((1 : ℂ) + 1)), ?_⟩
  have hσ : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun σ : ℝ ↦ (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-((1 : ℂ) + 1)))) := by
    simpa using hσ.mul hint
  refine Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin] with σ hσ'
  exact (hrep σ hσ').symm

end NK.NUV2.HeckeLAbel
