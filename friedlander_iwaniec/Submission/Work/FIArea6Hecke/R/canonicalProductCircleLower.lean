import Mathlib
import Submission.Work.FIArea6Hecke.R.divisorSupportFacts
import Submission.Work.FIArea6Hecke.R.finsetProdZpowNormLower

namespace Work.FIArea6Hecke.R

open scoped Classical

/-- Lower bound for the canonical product on the circle `‖ζ‖ = T`.

`Λ` is analytic on a neighbourhood of the closed ball of radius `T`, and every zero of `Λ`
has distance at least `1 / (log (A+2) + K + 1)^2` from the circle of radius `T`.  Writing
`L = log (A + 2) + K + 1` and `D` for the divisor of `Λ` on the closed ball, every point `u`
in the support of `D` satisfies `‖u‖ ≤ T` and `Λ u = 0`, hence
`‖ζ - u‖ ≥ T - ‖u‖ ≥ 1/L²`.  Since `D` has finite support, this gives
`‖∏ᶠ u, (ζ - u)^(D u)‖ ≥ (1/L²)^(∑ D u)`, and taking `-log` yields the claim. -/
theorem canonicalProductCircleLower (Λ : ℂ → ℂ) (A T K : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hT : 0 < T) (hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T))
    (hmargin : ∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) :
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖ ≤
      2 * Real.log (Real.log (A + 2) + K + 1) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u : ℤ) : ℝ)) := by
  classical
  set D := MeromorphicOn.divisor Λ (Metric.closedBall 0 T) with hD
  set L : ℝ := Real.log (A + 2) + K + 1 with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h1 : 0 ≤ Real.log (A + 2) := Real.log_nonneg (by linarith)
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall (0 : ℂ) T)
  set S : Finset ℂ := hfin.toFinset with hSe
  have hScoe : (S : Set ℂ) = D.support := by rw [hSe, hfin.coe_toFinset]
  -- Reduction of the finitely supported sum to the finite support of the divisor.
  have hsum_eq : (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ)) = ∑ u ∈ S, ((D u : ℤ) : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    rw [hScoe]
    exact Function.mem_support.mpr (fun h => hu (by simp [h]))
  -- Reduction of the finitely supported product to the finite support of the divisor.
  have hprod_eq : (∏ᶠ u : ℂ, (ζ - u) ^ (D u)) = ∏ u ∈ S, (ζ - u) ^ (D u) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    rw [hScoe]
    exact Function.mem_support.mpr (fun h => hu (by simp [h]))
  -- Reverse triangle inequality + the margin hypothesis.
  have hC : ∀ u : ℂ, Λ u = 0 → ‖u‖ ≤ T → 1 / L ^ 2 ≤ ‖ζ - u‖ := by
    intro u hΛu hu
    have hm := hmargin u hΛu
    have habs : |‖u‖ - T| = T - ‖u‖ := by
      have h : ‖u‖ - T ≤ 0 := by linarith
      rw [abs_of_nonpos h, neg_sub]
    rw [habs] at hm
    have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
    have h1 : 1 / L ^ 2 ≤ T - ‖u‖ := by
      rw [div_le_iff₀ hL2pos]
      linarith [hm]
    have h2 : T - ‖u‖ ≤ ‖ζ - u‖ := by
      have h3 := norm_sub_norm_le ζ u
      rw [hζ] at h3
      have h4 : T - ‖u‖ ≤ |T - ‖u‖| := le_abs_self _
      linarith
    linarith
  have hw : ∀ u ∈ S, 0 ≤ D u := by
    intro u hu
    have hDu : D u ≠ 0 := by
      have : u ∈ D.support := by rw [← hScoe]; exact hu
      exact this
    exact (divisorSupportFacts hAn hDu).2.2
  have hz : ∀ u ∈ S, 1 / L ^ 2 ≤ ‖ζ - u‖ := by
    intro u hu
    have hDu : D u ≠ 0 := by
      have : u ∈ D.support := by rw [← hScoe]; exact hu
      exact this
    exact hC u (divisorSupportFacts hAn hDu).1 (divisorSupportFacts hAn hDu).2.1
  have hc : 0 < 1 / L ^ 2 := by positivity
  have hbound := finsetProdZpowNormLower S (1 / L ^ 2) hc D hw ζ hz
  have hsumD : (∑ u ∈ S, ((D u : ℤ) : ℝ)) = ∑ u ∈ S, ((D u).toNat : ℝ) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hDu : D u ≠ 0 := by
      have : u ∈ D.support := by rw [← hScoe]; exact hu
      exact this
    have h0 : 0 ≤ D u := (divisorSupportFacts hAn hDu).2.2
    have h1 : ((D u).toNat : ℝ) = ((D u : ℤ) : ℝ) := by
      rw [← Int.cast_natCast ((D u).toNat), Int.toNat_of_nonneg h0]
    exact h1.symm
  have hlog : Real.log (1 / L ^ 2) = -(2 * Real.log L) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    ring
  rw [hprod_eq, hsum_eq]
  calc -Real.log ‖∏ u ∈ S, (ζ - u) ^ (D u)‖
      ≤ -(∑ u ∈ S, ((D u).toNat : ℝ)) * Real.log (1 / L ^ 2) := hbound
    _ = 2 * Real.log L * (∑ u ∈ S, ((D u : ℤ) : ℝ)) := by
        rw [hlog, ← hsumD]; ring

end Work.FIArea6Hecke.R
