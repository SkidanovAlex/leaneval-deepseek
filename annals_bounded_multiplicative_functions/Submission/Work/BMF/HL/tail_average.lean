import Mathlib
import Submission.Work.BMF.HL.norm_integral_cpow_theta_le
import Submission.Work.BMF.HL.integral_le_mul_of_continuousOn
import Submission.Work.BMF.HL.integral_term_re

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- Averaging in the frequency variable.  Write `δ(y) := min 1 (1/log y)`.  If the weighted tail
mass `Σ_{y<p≤x} min(1, 2/(δ(y) log p))/p` is at most `K`, then for every `u` there is
`θ ∈ [0, δ(y)]` with `Re Σ_{y<p≤x} g(p) p^{-(u+θ)i}/p ≥ -K`.

Proof sketch: put `F(θ) := Re Σ_{y<p≤x} g(p) p^{-(u+θ)i}/p`.  Dividing the interval integral of
`F` over `[0,δ]` by `δ` gives `Re Σ_{y<p≤x} h_p w_p / p` with `h_p := g(p)p^{-ui}` (`|h_p| ≤ 1`)
and `w_p := (1/δ)∫_0^δ p^{-iθ}dθ = (1−p^{-iδ})/(i δ log p)`, so
`|w_p| = |1 − e^{-iδ log p}|/(δ log p) ≤ min(1, 2/(δ log p))`.  Hence
`(1/δ)∫_0^δ F ≥ −Σ_{y<p≤x} min(1,2/(δ log p))/p ≥ −K`, and a continuous function on the compact
interval `[0,δ]` attains its maximum, which therefore dominates the average. -/
theorem tail_average {K : ℝ} (hK : 0 < K)
    (hbound : ∀ y x : ℝ, 2 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
          min 1 (2 / (min 1 (1 / Real.log y) * Real.log p)) / (p : ℝ)) ≤ K) :
    ∀ (g : ℕ → ℂ), (∀ n, ‖g n‖ ≤ 1) → ∀ (u y x : ℝ), 2 ≤ y → y ≤ x →
      ∃ θ ∈ Set.Icc (0 : ℝ) (min 1 (1 / Real.log y)),
        -K ≤ ∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
            (g p * (p : ℂ) ^ (-(Complex.I * (u + θ)))).re / (p : ℝ) := by
  intro g hg u y x hy hyx
  have hy1 : (1 : ℝ) < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  set δ : ℝ := min 1 (1 / Real.log y) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  set s : Finset ℕ := (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE with hs
  have hprime : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    rw [hs] at hp
    simp only [Finset.mem_sdiff, Nat.mem_primesLE] at hp
    exact hp.1.2
  have h2p : ∀ p ∈ s, 2 ≤ p := fun p hp => (hprime p hp).two_le
  have hppos : ∀ p ∈ s, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    have h : (0 : ℕ) < p := by have := h2p p hp; omega
    exact_mod_cast h
  -- The averaged function `F`.
  set F : ℝ → ℝ :=
    fun θ => ∑ p ∈ s, (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re / (p : ℝ)
    with hFdef
  -- Each summand is continuous.
  have hcont_term : ∀ p ∈ s, Continuous
      (fun θ : ℝ => (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re / (p : ℝ)) := by
    intro p hp
    have h2 : 2 ≤ p := h2p p hp
    have heq : (fun θ : ℝ => (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re / (p : ℝ))
        = fun θ : ℝ =>
            (g p * Complex.exp ((-(Complex.I * (Real.log p : ℂ))) * ((u + θ : ℝ) : ℂ))).re
              / (p : ℝ) := by
      funext θ
      rw [cpow_neg_I_eq_exp p h2 (u + θ)]
    rw [heq]
    apply Continuous.div_const
    apply Complex.continuous_re.comp
    apply Continuous.mul continuous_const
    apply Complex.continuous_exp.comp
    apply Continuous.mul continuous_const
    exact Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
  have hcontF : ContinuousOn F (Set.Icc 0 δ) := by
    rw [hFdef]
    exact (continuous_finsetSum s hcont_term).continuousOn
  -- Integral of the finite sum is the sum of the integrals.
  have hcongr : (∫ θ in (0 : ℝ)..δ, F θ)
      = ∑ p ∈ s,
          ∫ θ in (0 : ℝ)..δ, (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re
            / (p : ℝ) := by
    simp only [hFdef]
    exact intervalIntegral.integral_finsetSum
      (fun p hp => (hcont_term p hp).intervalIntegrable 0 δ)
  -- Per-prime lower bound for each summand integral.
  have hterm_lb : ∀ p ∈ s,
      -(δ * min 1 (2 / (δ * Real.log p)) / (p : ℝ)) ≤
        ∫ θ in (0 : ℝ)..δ, (g p * (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))).re
          / (p : ℝ) := by
    intro p hp
    rw [integral_term_re g p (h2p p hp) u δ]
    set Ip : ℂ := ∫ θ in (0 : ℝ)..δ, (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ))) with hIp
    have hIpb : ‖Ip‖ ≤ δ * min 1 (2 / (δ * Real.log p)) := by
      rw [hIp]
      exact norm_integral_cpow_theta_le p (h2p p hp) u hδpos
    have hpp : (0 : ℝ) < (p : ℝ) := hppos p hp
    have habs : |(((g p) * Ip).re) / (p : ℝ)| ≤ δ * min 1 (2 / (δ * Real.log p)) / (p : ℝ) := by
      rw [abs_div, abs_of_pos hpp]
      have h1 : |(((g p) * Ip).re)| ≤ ‖(g p) * Ip‖ := Complex.abs_re_le_norm _
      have h2 : ‖(g p) * Ip‖ ≤ ‖Ip‖ := by
        rw [norm_mul]
        calc ‖g p‖ * ‖Ip‖ ≤ 1 * ‖Ip‖ := mul_le_mul_of_nonneg_right (hg p) (norm_nonneg _)
          _ = ‖Ip‖ := one_mul _
      calc |(((g p) * Ip).re)| / (p : ℝ)
          ≤ ‖(g p) * Ip‖ / (p : ℝ) := div_le_div_of_nonneg_right h1 (le_of_lt hpp)
        _ ≤ ‖Ip‖ / (p : ℝ) := div_le_div_of_nonneg_right h2 (le_of_lt hpp)
        _ ≤ (δ * min 1 (2 / (δ * Real.log p))) / (p : ℝ) :=
              div_le_div_of_nonneg_right hIpb (le_of_lt hpp)
    exact (abs_le.mp habs).1
  -- Lower bound for the integral of `F`.
  have hfinal : -(δ * K) ≤ ∫ θ in (0 : ℝ)..δ, F θ := by
    have hb' : (∑ p ∈ s, min 1 (2 / (δ * Real.log p)) / (p : ℝ)) ≤ K := by
      rw [hs, hδ]
      exact hbound y x hy hyx
    have h1 : -(δ * K) ≤ -(δ * (∑ p ∈ s, min 1 (2 / (δ * Real.log p)) / (p : ℝ))) := by
      have h := mul_le_mul_of_nonneg_left hb' hδnn
      linarith
    have h2 : (∑ p ∈ s, -(δ * min 1 (2 / (δ * Real.log p)) / (p : ℝ)))
        = -(δ * ∑ p ∈ s, min 1 (2 / (δ * Real.log p)) / (p : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib, neg_inj]
      exact Finset.sum_congr rfl (fun p hp => by ring)
    have h3 : (∑ p ∈ s, -(δ * min 1 (2 / (δ * Real.log p)) / (p : ℝ)))
        ≤ ∫ θ in (0 : ℝ)..δ, F θ := by
      rw [hcongr]
      exact Finset.sum_le_sum hterm_lb
    linarith
  -- Choose the point where `F` is at least its average.
  obtain ⟨θ, hθI, hθ⟩ := integral_le_mul_of_continuousOn hδnn hcontF
  refine ⟨θ, ?_, ?_⟩
  · rw [hδ] at hθI
    exact hθI
  · have h1 : -(δ * K) ≤ δ * F θ := le_trans hfinal hθ
    have h2 : 0 ≤ (F θ + K) * δ := by nlinarith [h1]
    have h3 : 0 ≤ F θ + K := nonneg_of_mul_nonneg_left h2 hδpos
    have h4 : -K ≤ F θ := by
      have hKnn : 0 ≤ K := le_of_lt hK
      linarith
    simpa [hFdef, hs] using h4

end Work.BMF.HL
