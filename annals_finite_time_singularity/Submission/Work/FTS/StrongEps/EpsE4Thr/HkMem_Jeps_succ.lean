/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_succ` — the fixed-`ε` angular gain of `J_ε`

`J_ε = Jeps ρ ε` (the log-coordinate mollifier of `Submission/Work/FTS/StrongEps/Basic.lean`)
*raises the `ℋ^k`-membership degree by one*: if `f` is smooth on the open quadrant and
`HkMem α k f` with `k ≥ 1`, then `HkMem α (k+1) (J_ε f)`.

This is the membership half of the refuted norm statement `HkSq_Jeps_succ_le`
(`NOTES_HkSq_Jeps_succ_le_FALSE.md`): no bound of `HkSq α (k+1) (J_ε f)` by `HkSq α k f` can hold
(the pure angular top slot `D_θ^{k+1}` is a level-`(k+1)` slot of `f`), but *finiteness* is
inherited, and the hypothesis `1 ≤ k` is essential (at `k = 0` there is no angular slot at all in
`HkIntegrand α 0 f`, and the profile `φ(z)·θ^σ` with `(η-1)/2 < σ ≤ (γ-1)/2` refutes the `k = 0`
case — `NOTES_HkSq_Jeps_succ_le_FALSE.md` §2).

## Proof

Every slot of `HkIntegrand α (k+1) (J_ε f)` is handled through the log-coordinate convolution
structure of `J_ε`:

* slots of order `≤ k`: they are `J_ε` of the corresponding slot of `f` (commutation of `D_z`,
  `D_θ` with `J_ε`), and `J_ε` is an average with a probability density, so the weighted square is
  bounded by the average of the shifted weighted square of `f`; the shift cost of the weights is
  `e^{c|p|}` (`wdiv_shift_le`, `Wt_shift_le`) — *no* price;
* slots of order exactly `k+1` (`D_z^{k+1}`, `D_θ^{k+1}` and `D_z^jD_θ^i` with `j, i ≥ 1`): one
  derivative is routed onto the kernel (`mixed_Jeps_route_z`, `DthIter_Jeps_route_theta`), which
  costs *one* factor `ε⁻¹` (the routed density is `Ψ = ε⁻¹ Jker ρ̃ ε`, `ρ̃ = ρ + |∂₁ρ| + |∂₂ρ|`)
  and leaves a level-`k` slot of `f`.

The pointwise assembly of these two halves is `step_pointwise_gen` (the `m`-unrestricted form of
`StepFacts.step_pointwise`), and the passage from that pointwise bound to the two `HkMem`
integrability clauses (Tonelli in `p`, the angular shift comparison `lintegral_thShift_le`, the
`z`-substitution, and the mass of `Ψ`) is `HkMem_Jeps_of_pointwise`, which keeps the constant
abstract and therefore needs no bound on `k`.  The `k ≤ 7` case is the existing
`StepFacts.HkMem_Jeps_step`; the route here covers all `k ≥ 1` uniformly.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepMembership
import Submission.Work.FTS.StrongEps.EpsE4Thr.step_pointwise_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem HkMem_Jeps_succ {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) →
        (∀ z, 0 ≤ z → f z 0 = 0 ∧ f z (π / 2) = 0) →
        Work.Spaces.HkMem α k f →
        Work.Spaces.HkMem α (k + 1) (Work.FTS.StrongEps.Jeps ρ ε f) := by
  intro α hα0 hα1 k hk ε hε0 hε1 f hsm hvan hmem
  -- the two weight-shift comparisons with the common constant `c = max cη cγ`
  obtain ⟨cη, hcη0, hWη0⟩ := Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγ0, hWγ0⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  set c : ℝ := max cη cγ with hcdef
  have hc : 0 ≤ c := le_of_lt (lt_of_lt_of_le hcη0 (le_max_left _ _))
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hαI z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  have hm : 2 ≤ k + 1 := by omega
  -- the pointwise one-order smoothing step, in the shape consumed below
  have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
        ≤ ENNReal.ofReal ((((k + 1 + 1 : ℕ) ^ 2 + 2 : ℕ) : ℝ)
              * Work.FTS.StrongEps.StepFacts.Mmax ρ ε)
          * ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * Work.FTS.StrongEps.StepFacts.Fd α (k + 1) f z θ p := by
    intro z hz θ hθ
    by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · simpa only [Work.FTS.StrongEps.StepFacts.Jint, Work.FTS.StrongEps.StepFacts.Kd,
        Work.FTS.StrongEps.StepFacts.Fd] using
        step_pointwise_gen ρ hρ hε0 hε1 hαI hm hsm hWη hWγ hq.1 hq.2
    · have hzero : Work.Spaces.HkIntegrand α (k + 1) (Work.FTS.StrongEps.Jeps ρ ε f) z θ = 0 :=
        Work.FTS.StrongEps.HkSqAux.HkIntegrand_boundary_zero hαI hz hθ hq
      rw [hzero, ENNReal.ofReal_zero]
      exact zero_le
  exact HkMem_Jeps_of_pointwise hρ hαI hm hε0 hε1 hc (fun n => hsm n) hmem hP

end Work.FTS.StrongEps.EpsE4Thr
