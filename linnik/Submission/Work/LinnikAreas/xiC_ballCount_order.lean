import Mathlib
import Submission.Work.LinnikAreas.PrincipalZeroCount

/-!
# Ball count of the zeros of `Ξ = xiC`

`xiC` is the entire completion `Ξ(s) = 1/2 + (1/2) s (s-1) Λ₀(s)` of the Riemann zeta function
(see `Submission.Work.LinnikAreas.PrincipalZeroCount`).  Its zeros are exactly the non-trivial
zeros of `ζ`, so the total vanishing order of `xiC` over any finite set lying in the closed ball
of radius `R` is `≪ R log R`: this is the Riemann–von Mangoldt count in the form supplied by
`Commons.NumberTheory.Zeta.xiE_zeroCount` (Jensen's inequality + the circle growth bound).

The bridge between a finite multiplicity sum over an arbitrary finite set and the divisor
`finsum` of `xiE_zeroCount` is the elementary lemma `xiC_mult_sum_le_divisor`.
-/

open Complex
open scoped Classical BigOperators Topology
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract (zeroMult)

/-- A finite multiplicity sum of vanishing orders of `xiC` inside a compact set `U` is bounded by
the divisor sum of `xiC` over `U`.  (Since `xiC` is entire, the divisor is everywhere
nonnegative, so dropping the zeros of `xiC` outside the given finite set only increases the sum.) -/
lemma xiC_mult_sum_le_divisor (U : Set ℂ) (hU : IsCompact U) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ U) :
    (∑ ρ ∈ S, (analyticOrderNatAt xiC ρ : ℝ))
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor xiC U) u : ℝ) := by
  classical
  have han : AnalyticOnNhd ℂ xiC U := xiC_analyticOn U
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor xiC U u with hD
  have hfin : D.support.Finite := by
    rw [hD]
    exact (MeromorphicOn.divisor xiC U).finiteSupport hU
  have hmem : ∀ u : ℂ, u ∈ hfin.toFinset ↔ D u ≠ 0 := by
    intro u; rw [Set.Finite.mem_toFinset]; exact Iff.rfl
  have hval : ∀ u : ℂ, u ∈ U → D u = (analyticOrderNatAt xiC u : ℤ) := by
    intro u hu
    rw [hD]
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hUsub : ∀ u : ℂ, u ∈ hfin.toFinset → u ∈ U := by
    intro u hu
    have hne : D u ≠ 0 := (hmem u).mp hu
    exact (MeromorphicOn.divisor xiC U).supportWithinDomain (by simpa [hD] using hne)
  have hfs : (∑ᶠ u : ℂ, (D u : ℝ)) = ∑ u ∈ hfin.toFinset, (D u : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact (hmem u).mpr (by intro h0; exact hu (by simp [h0]))
  rw [hfs]
  have hleft : (∑ ρ ∈ S, (analyticOrderNatAt xiC ρ : ℝ))
      = ∑ ρ ∈ S.filter (fun ρ => ρ ∈ hfin.toFinset),
          (analyticOrderNatAt xiC ρ : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro u hu hnot
    have hnotin : u ∉ hfin.toFinset := fun hc => hnot (Finset.mem_filter.mpr ⟨hu, hc⟩)
    have hD0 : D u = 0 := by
      by_contra hne
      exact hnotin ((hmem u).mpr hne)
    have huU := hS u hu
    rw [hval u huU] at hD0
    have hz : analyticOrderNatAt xiC u = 0 := by exact_mod_cast hD0
    simp [hz]
  rw [hleft]
  have hsub : S.filter (fun ρ => ρ ∈ hfin.toFinset) ⊆ hfin.toFinset :=
    fun u hu => (Finset.mem_filter.mp hu).2
  have hcongr : (∑ ρ ∈ S.filter (fun ρ => ρ ∈ hfin.toFinset),
        (analyticOrderNatAt xiC ρ : ℝ))
      = ∑ ρ ∈ S.filter (fun ρ => ρ ∈ hfin.toFinset), (D ρ : ℝ) := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have huU := hS u (Finset.mem_filter.mp hu).1
    have h1 := hval u huU
    rw [h1]
    push_cast
    ring
  rw [hcongr]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro u hu _
  have h0 : (0 : ℤ) ≤ D u := by
    rw [hval u (hUsub u hu)]
    exact Int.natCast_nonneg _
  exact_mod_cast h0

theorem xiC_ballCount_order :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 2 ≤ R → ∀ t : Finset ℂ, (∀ u ∈ t, ‖u‖ ≤ R) →
      ∑ u ∈ t, (analyticOrderNatAt xiC u : ℝ) ≤ c * R * (Real.log (R + 2) + 2) := by
  obtain ⟨c₀, hc₀⟩ := Commons.NumberTheory.Zeta.xiE_zeroCount
  refine ⟨max c₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right c₀ 1), ?_⟩
  intro R hR t ht
  -- the divisor `finsum` bound from `xiE_zeroCount`, transported to `xiC`
  have hball : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ))
      ≤ c₀ * R * (Real.log (R + 2) + 2) := by
    rw [show xiC = (fun z : ℂ => (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1)
      * completedRiemannZeta₀ z) from rfl]
    exact hc₀ R hR
  -- the finite sum over `t` is dominated by the divisor `finsum` over the closed ball
  have hle := xiC_mult_sum_le_divisor (Metric.closedBall (0:ℂ) R)
    (isCompact_closedBall (0:ℂ) R) t (fun u hu => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact ht u hu)
  refine le_trans (le_trans hle hball) ?_
  -- enlarge the constant to be positive
  have hR0 : 0 ≤ R := by linarith
  have hlog : 0 ≤ Real.log (R + 2) + 2 := by
    have : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    linarith
  have hc₀le : c₀ ≤ max c₀ 1 := le_max_left c₀ 1
  nlinarith [mul_nonneg hR0 hlog]

end Work.LinnikAreas
