import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeroSum_finsum_le_beta
import Submission.Commons.NumberTheory.Zeta.divisor_xi_eq_logDeriv_pole_order
import Submission.Commons.Analysis.MeromorphicOn.divisor_closedBall_mono

open scoped BigOperators

set_option linter.unusedVariables false

namespace Commons.NumberTheory.Zeta

theorem zeroSum_finset_le_beta (h : RiemannHypothesis) (R : ℝ) (hR : 0 ≤ R) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ (1/4 : ℝ) < ρ.re ∧ ρ.re < 2) :
    S.sum (fun ρ => (((MeromorphicOn.divisor (fun z : ℂ =>
        (1/2 : ℂ) + (1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z) (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) / ‖ρ‖ ^ 2)
      ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  classical
  set f : ℂ → ℝ := fun ρ => (((MeromorphicOn.divisor (fun z : ℂ =>
      (1/2 : ℂ) + (1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
      (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) / ‖ρ‖ ^ 2 with hf
  have hfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor (fun z : ℂ =>
      (1/2 : ℂ) + (1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
      (Metric.closedBall 0 R) u)).Finite := XiPF.xiF_divisor_support_finite R
  set D : Finset ℂ := hfin.toFinset with hD
  have hDmem : ∀ u : ℂ, u ∈ D ↔ MeromorphicOn.divisor (fun z : ℂ =>
      (1/2 : ℂ) + (1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
      (Metric.closedBall 0 R) u ≠ 0 := by
    intro u
    rw [hD]
    simp only [Set.Finite.mem_toFinset, Function.mem_support]
  have hfnonneg : ∀ u : ℂ, 0 ≤ f u := by
    intro u
    rw [hf]
    exact div_nonneg (by exact_mod_cast XiPF.xiF_divisor_nonneg_closedBall R u) (by positivity)
  have hfinsum : (∑ᶠ u : ℂ, f u) = ∑ u ∈ (S ∪ D), f u := by
    rw [finsum_eq_sum_of_support_subset]
    intro u hu
    rw [Function.mem_support] at hu
    refine Finset.mem_union_right S ?_
    rw [hDmem]
    intro hd
    refine hu ?_
    rw [hf]
    dsimp only
    rw [hd]
    simp
  have hle : S.sum f ≤ ∑ u ∈ (S ∪ D), f u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      (fun u _ _ => hfnonneg u)
  calc S.sum f ≤ ∑ u ∈ (S ∪ D), f u := hle
    _ = ∑ᶠ u : ℂ, f u := hfinsum.symm
    _ ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) :=
        zeroSum_finsum_le_beta h R

end Commons.NumberTheory.Zeta
