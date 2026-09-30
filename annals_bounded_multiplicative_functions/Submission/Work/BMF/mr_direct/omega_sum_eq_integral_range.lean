import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.remPointwise_defs
import Submission.Work.BMF.mr_direct.remPointwise_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral

noncomputable section

/-- **The `(ω+1)^{-1} = ∫_0^1 x^ω dx` identity over an arbitrary range.** Range version of `Work.BMF.mr_direct.omegaWeighted_sum_eq_integral` (same proof: exchange the finite sum with the interval integral, then `∫_0^1 (x:ℂ)^k dx = ((k:ℂ)+1)^{-1}` is `integral_cpow_nat` in the same file). No hypothesis on `X₁, X₂` is needed: for every `m` the integrand `x ↦ x^{ω(m;P,Q)}·g m·m^{-(1+it)}` is continuous, so each summand is interval-integrable. -/
lemma omega_sum_eq_integral_range (g : ℕ → ℂ) (P Q X₁ X₂ t : ℝ) :
    (∑ m ∈ Work.BMF.natIcc X₁ X₂,
        g m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * t)))
      = ∫ x in (0 : ℝ)..1,
          ∑ m ∈ Work.BMF.natIcc X₁ X₂,
            omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t)) := by
  have hint : ∀ m ∈ Work.BMF.natIcc X₁ X₂, IntervalIntegrable
      (fun x : ℝ => omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t)))
      volume (0 : ℝ) 1 := by
    intro m hm
    apply Continuous.intervalIntegrable
    unfold omegaWeighted omegaPow
    continuity
  rw [intervalIntegral.integral_finsetSum hint]
  apply Finset.sum_congr rfl
  intro m hm
  have hrw : ∀ x : ℝ, omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t))
      = (x : ℂ) ^ (Work.BMF.mrDirect.omegaCount P Q m) *
          (g m * (m : ℂ) ^ (-(1 + Complex.I * t))) := by
    intro x; unfold omegaWeighted omegaPow; ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_mul_const (g m * (m : ℂ) ^ (-(1 + Complex.I * t))),
    integral_cpow_nat]
  have hc : ((Work.BMF.mrDirect.omegaCount P Q m : ℂ) + 1)
      = ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ) := by push_cast; ring
  rw [hc]
  ring

end

end Work.BMF.mr_direct
