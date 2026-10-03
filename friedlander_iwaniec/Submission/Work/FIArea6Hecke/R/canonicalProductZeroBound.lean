import Mathlib

open Complex Metric Filter
open scoped BigOperators Topology

namespace Work.FIArea6Hecke.R

/-- The divisor (on a closed ball) of a function that is analytic there is nonnegative:
on the ball it is the (analytic) order of vanishing, a natural number, and it vanishes
outside the ball. -/
private lemma divisor_nonneg_of_analyticOnNhd {Λ : ℂ → ℂ} {T : ℝ}
    (hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T))
    {u : ℂ} (hu : u ∈ Metric.closedBall 0 T) :
    (0 : ℤ) ≤ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu, WithTop.untop₀_nonneg]
  exact ENat.map_natCast_nonneg

/--
**Canonical-product bound away from the zeros.**

Let `Λ` be analytic on the closed disc `|z| ≤ T` with `T ≥ 1`, and suppose that every zero of `Λ`
has modulus at least `δ > 0`.  Then the (finite) product of `-u` over the zeros `u` of `Λ` in the
disc, raised to the multiplicity with which they occur, has logarithm of modulus bounded by
`(∑ u, ord u) * (log T + |log δ|)`.

Indeed, each zero `u` counted with multiplicity satisfies `δ ≤ ‖u‖ ≤ T`, so
`|log ‖u‖| ≤ log T + |log δ|`, and the logarithm of the modulus of the product is
`∑ u, ord u * log ‖u‖`. -/
theorem canonicalProductZeroBound (Λ : ℂ → ℂ) (T : ℝ) (hT : 1 ≤ T) (δ : ℝ) (hδpos : 0 < δ)
    (hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T))
    (hδ : ∀ u : ℂ, Λ u = 0 → δ ≤ ‖u‖) :
    |Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖| ≤
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u : ℤ) : ℝ))
        * (Real.log T + |Real.log δ|) := by
  classical
  -- Abbreviate the divisor as a plain function.
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u
  have hD_eq : D = fun u => MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u := rfl
  change |Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (D u)‖| ≤
      (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ)) * (Real.log T + |Real.log δ|)
  -- The divisor is nonnegative everywhere (it is an order of vanishing on the disc).
  have hDnn : ∀ u : ℂ, (0 : ℝ) ≤ (D u : ℝ) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) T
    · have h : (0 : ℤ) ≤ D u := by
        rw [hD_eq]
        exact divisor_nonneg_of_analyticOnNhd hAn hu
      exact Int.cast_nonneg h
    · have h0 : D u = 0 := by
        rw [hD_eq]
        exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
      rw [h0]; norm_num
  -- A point supporting the divisor lies in the disc.
  have hDz : ∀ u : ℂ, D u ≠ 0 → u ∈ Metric.closedBall (0 : ℂ) T := by
    intro u hu
    by_contra h
    exact hu (by rw [hD_eq]; exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
  have hmer : MeromorphicOn Λ (Metric.closedBall 0 T) := hAn.meromorphicOn
  -- A point supporting the divisor is a zero of `Λ`.
  have hDzero : ∀ u : ℂ, D u ≠ 0 → Λ u = 0 := by
    intro u hu
    have huU := hDz u hu
    have h1 : (meromorphicOrderAt Λ u).untop₀ ≠ 0 := by
      have h2 := MeromorphicOn.divisor_apply hmer huU
      have h3 : D u = (meromorphicOrderAt Λ u).untop₀ := by rw [hD_eq]; exact h2
      intro h4
      exact hu (h3.trans h4)
    have h5 : analyticOrderAt Λ u ≠ 0 := by
      intro h0
      apply h1
      rw [(hAn u huU).meromorphicOrderAt_eq, h0]
      simp
    exact apply_eq_zero_of_analyticOrderAt_ne_zero h5
  -- The divisor has finite support, since the disc is compact.
  have hfin : (Function.support D).Finite := by
    rw [hD_eq]
    exact (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)).finiteSupport (isCompact_closedBall 0 T)
  set s : Finset ℂ := hfin.toFinset with hs
  have hmem : ∀ u : ℂ, u ∈ s ↔ D u ≠ 0 := by
    intro u
    simp [hs, Function.mem_support]
  -- Replace the infinite product and sum by products and sums over the support.
  have hsub : Function.mulSupport (fun u : ℂ => ((0 : ℂ) - u) ^ (D u)) ⊆ ↑s := by
    intro u hu
    rw [Finset.mem_coe, hmem u]
    intro h0
    exact hu (by simp [h0])
  have hsubsum : Function.support (fun u : ℂ => ((D u : ℤ) : ℝ)) ⊆ ↑s := by
    intro u hu
    rw [Finset.mem_coe, hmem u]
    intro h0
    exact hu (by simp [h0])
  rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => ((0 : ℂ) - u) ^ (D u)) hsub,
      finsum_eq_sum_of_support_subset (fun u : ℂ => ((D u : ℤ) : ℝ)) hsubsum]
  -- Compute the modulus of the product.
  have hnorm : ‖∏ u ∈ s, ((0 : ℂ) - u) ^ (D u)‖ = ∏ u ∈ s, ‖u‖ ^ (D u) := by
    have h1 : ‖∏ u ∈ s, ((0 : ℂ) - u) ^ (D u)‖ = ∏ u ∈ s, ‖((0 : ℂ) - u) ^ (D u)‖ := by simp
    rw [h1]
    exact Finset.prod_congr rfl (fun u _ => by rw [norm_zpow, zero_sub, norm_neg])
  -- Each zero contributing to the divisor satisfies `δ ≤ ‖u‖ ≤ T`.
  have hbound : ∀ u ∈ s, |Real.log ‖u‖| ≤ Real.log T + |Real.log δ| := by
    intro u hu
    have hDne : D u ≠ 0 := (hmem u).mp hu
    have hδu : δ ≤ ‖u‖ := hδ u (hDzero u hDne)
    have huT : ‖u‖ ≤ T := by
      have := hDz u hDne
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    have hpos : 0 < ‖u‖ := lt_of_lt_of_le hδpos hδu
    refine abs_le'.mpr ⟨?_, ?_⟩
    · exact le_trans (Real.log_le_log hpos huT) (le_add_of_nonneg_right (abs_nonneg _))
    · have h2 : -Real.log ‖u‖ ≤ |Real.log δ| := by
        have h3 : Real.log δ ≤ Real.log ‖u‖ := Real.log_le_log hδpos hδu
        linarith [neg_le_abs (Real.log δ)]
      linarith [h2, abs_nonneg (Real.log δ), Real.log_nonneg hT]
  -- Take logarithms; this is where the multiplicities appear as coefficients.
  have hlog : Real.log ‖∏ u ∈ s, ((0 : ℂ) - u) ^ (D u)‖
      = ∑ u ∈ s, (D u : ℝ) * Real.log ‖u‖ := by
    rw [hnorm, Real.log_prod]
    · exact Finset.sum_congr rfl (fun u _ => by rw [Real.log_zpow])
    · intro u hu
      have hpos : 0 < ‖u‖ := lt_of_lt_of_le hδpos (hδ u (hDzero u ((hmem u).mp hu)))
      exact zpow_ne_zero (D u) (ne_of_gt hpos)
  rw [hlog]
  -- Bound the resulting sum termwise and factor out the total multiplicity.
  refine (Finset.abs_sum_le_sum_abs (fun u => (D u : ℝ) * Real.log ‖u‖) s).trans ?_
  have hstep : ∀ u ∈ s, |(D u : ℝ) * Real.log ‖u‖| ≤ (D u : ℝ) * (Real.log T + |Real.log δ|) := by
    intro u hu
    rw [abs_mul, abs_of_nonneg (hDnn u)]
    exact mul_le_mul_of_nonneg_left (hbound u hu) (hDnn u)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_mul]

end Work.FIArea6Hecke.R
