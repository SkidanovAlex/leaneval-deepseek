import Mathlib
import Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound

open scoped BigOperators

namespace Work.LinnikAreas

/-- The entire completion `Ξ = 1/2 + (1/2) s (s-1) Λ₀(s)` of the Riemann zeta function used in
`Commons.NumberTheory.Zeta.XiPF` and the copy `Work.LinnikAreas.xiC` are the very same
function, so the analytic vanishing orders agree. -/
lemma analyticOrderNatAt_xiF_eq_xiC (u : ℂ) :
    analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u =
      analyticOrderNatAt Work.LinnikAreas.xiC u := rfl

/-- **The multiplicity-weighted inverse-square zero sum of the Riemann zeta completion is
bounded.**

There is an absolute constant `C > 0` such that for every finite set `s` of complex numbers,
the sum of the vanishing orders of `Ξ` over `s`, weighted by the Poisson-type kernel
`1/(1 + ‖u‖²)`, is at most `C`.

The zeros with `‖u‖ ≤ 2` are finite, and their total multiplicity is bounded by the
Riemann–von Mangoldt count `xiC_ballCount_order`; for the zeros with `‖u‖ > 2` the kernel is
dominated by `1/‖u‖²` and the dyadic tail estimate `xiCZeroInvSqTailBound` applies. -/
theorem zetaZeroSumInvSq :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℂ,
      Finset.sum s (fun u => (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
        (1 / (1 + ‖u‖ ^ 2))) ≤ C := by
  classical
  obtain ⟨C₂, hC₂pos, htail⟩ := Work.LinnikAreas.xiCZeroInvSqTailBound
  obtain ⟨c, hcpos, hcount⟩ := Work.LinnikAreas.xiC_ballCount_order
  set C₁ : ℝ := c * 2 * (Real.log (2 + 2) + 2) with hC₁def
  -- Bound for the part of the sum carried by the zeros of norm at most `2`.
  have hsmall : ∀ t : Finset ℂ, (∀ u ∈ t, ‖u‖ ≤ 2) →
      ∑ u ∈ t, (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) ≤ C₁ := by
    intro t ht
    calc ∑ u ∈ t, (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ)
        = ∑ u ∈ t, (analyticOrderNatAt Work.LinnikAreas.xiC u : ℝ) :=
          Finset.sum_congr rfl (fun u _ => by rw [analyticOrderNatAt_xiF_eq_xiC])
      _ ≤ c * 2 * (Real.log (2 + 2) + 2) := hcount 2 le_rfl t ht
      _ = C₁ := by rw [hC₁def]
  -- Bound for the part of the sum carried by the zeros of norm exceeding `2`.
  have hlarge : ∀ t : Finset ℂ, (∀ u ∈ t, 2 < ‖u‖) →
      ∑ u ∈ t, (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
        (1 / (1 + ‖u‖ ^ 2)) ≤ C₂ := by
    intro t ht
    have hle : ∀ u ∈ t,
        (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
            (1 / (1 + ‖u‖ ^ 2)) ≤
          (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) / ‖u‖ ^ 2 := by
      intro u hu
      have hpos : (0:ℝ) < ‖u‖ ^ 2 := by
        have := ht u hu
        positivity
      have hweight : (1:ℝ) / (1 + ‖u‖ ^ 2) ≤ 1 / ‖u‖ ^ 2 :=
        one_div_le_one_div_of_le hpos (by linarith [sq_nonneg ‖u‖])
      calc (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
              (1 / (1 + ‖u‖ ^ 2))
          ≤ (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
              (1 / ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg _)
        _ = (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) / ‖u‖ ^ 2 := by ring
    calc ∑ u ∈ t, (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
            (1 / (1 + ‖u‖ ^ 2))
        ≤ ∑ u ∈ t, (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) / ‖u‖ ^ 2 :=
          Finset.sum_le_sum hle
      _ = ∑ u ∈ t, (analyticOrderNatAt Work.LinnikAreas.xiC u : ℝ) / ‖u‖ ^ 2 :=
          Finset.sum_congr rfl (fun u _ => by rw [analyticOrderNatAt_xiF_eq_xiC])
      _ ≤ C₂ := htail t ht
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁def]
    have h1 : 0 < Real.log (2 + 2) + 2 := by
      have h2 : (0:ℝ) ≤ Real.log (2 + 2) := Real.log_nonneg (by norm_num)
      linarith
    positivity
  refine ⟨C₁ + C₂ + 1, by linarith, ?_⟩
  intro s
  rw [← Finset.sum_filter_add_sum_filter_not s (fun u : ℂ => ‖u‖ ≤ 2)
        (fun u => (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
          (1 / (1 + ‖u‖ ^ 2)))]
  have hp : ∀ u ∈ s.filter (fun u : ℂ => ‖u‖ ≤ 2), ‖u‖ ≤ 2 :=
    fun u hu => (Finset.mem_filter.mp hu).2
  have hnp : ∀ u ∈ s.filter (fun u : ℂ => ¬ ‖u‖ ≤ 2), 2 < ‖u‖ :=
    fun u hu => lt_of_not_ge (Finset.mem_filter.mp hu).2
  have h1 : (∑ u ∈ s.filter (fun u : ℂ => ‖u‖ ≤ 2),
        (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
          (1 / (1 + ‖u‖ ^ 2))) ≤ C₁ := by
    have hle : ∀ u ∈ s.filter (fun u : ℂ => ‖u‖ ≤ 2),
        (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
            (1 / (1 + ‖u‖ ^ 2)) ≤
          (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) := by
      intro u _
      have hw : (1:ℝ) / (1 + ‖u‖ ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [sq_nonneg ‖u‖]
      calc (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
              (1 / (1 + ‖u‖ ^ 2))
          ≤ (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
        _ = (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) := by ring
    exact le_trans (Finset.sum_le_sum hle) (hsmall _ hp)
  have h2 : (∑ u ∈ s.filter (fun u : ℂ => ¬ ‖u‖ ≤ 2),
        (analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u : ℝ) *
          (1 / (1 + ‖u‖ ^ 2))) ≤ C₂ := hlarge _ hnp
  linarith

end Work.LinnikAreas
