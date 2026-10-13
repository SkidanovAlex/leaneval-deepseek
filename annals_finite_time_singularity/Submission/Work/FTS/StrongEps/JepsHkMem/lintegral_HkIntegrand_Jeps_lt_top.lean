/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `H^k`-integrand of the mollified profile is `lintegral`-integrable

`Work.FTS.StrongEps.JepsHkMem.lintegral_HkIntegrand_Jeps_lt_top` is the finiteness half of the
membership statement `HkMem α k (J_ε f)` (the other half being the honest integrability of the
iterated Bochner integrals): for an admissible mollifier `ρ`, `0 < ε`, `α ∈ (0,1]`, a `C^∞` profile
`f` on the open quadrant with `HkMem α k f`,

  `∫⁻ z ∈ [0,∞), ∫⁻ θ ∈ [0,π/2], ofReal (HkIntegrand α k (J_ε f) z θ) < ⊤`.

This is proved by the same chain as `HkSqAux.ofReal_HkSq_Jeps_le` (the `E1` bound
`HkSq α k (J_ε f) ≤ e^{Cε} HkSq α k f`), but *without* the hypothesis `HkMem α k (J_ε f)`: that
hypothesis is only needed there to convert the iterated Bochner integral `HkSq α k (J_ε f)` into
the iterated `lintegral` (step `h1` of that proof).  Here the `lintegral` is the object of
interest, so the proof starts directly at the pointwise slot estimate `ofReal_GJ_le`, passes
through Tonelli (`fubini_shift`), the log-coordinate shift bound for the `H^k`-integrand
(`integral_shift_le`), and the kernel mass estimate (`Jker_exp_integral_le`), producing

  `∫⁻ z ∫⁻ θ ofReal (HkIntegrand α k (J_ε f) z θ)
     ≤ ofReal (HkSq α k f) · ofReal (exp ((4c + 2δ)ε))`,

which is finite because `ofReal` never hits `⊤`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.HkSqAux.integral_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsHkMem

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lintegral_HkIntegrand_Jeps_lt_top {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hmem : Work.Spaces.HkMem α k f) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Jeps ρ ε f) z θ)) < ⊤ := by
  -- the three shift bounds of the `E1` chapter
  obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  -- the two weight bounds, with the common constant `max cη cγ`
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos
          (Work.FTS.StrongEps.thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos
          (Work.FTS.StrongEps.thShift_mem hθ))) _)))
  -- the `H^k`-integrand of `f` is continuous on the open quadrant
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    HkSqAux.continuousOn_HkIntegrand_Quad α k hsm
  set C : ENNReal := ENNReal.ofReal (Work.Spaces.HkSq α k f) with hC
  set E1 : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (2 * max cη cγ * (|p.1| + |p.2|))) with hE1
  set E2 : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) with hE2
  set E3 : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp ((2 * max cη cγ + δ) * (|p.1| + |p.2|))) with hE3
  set K : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε p) with hK
  set Φ : ℝ → ℝ → ENNReal := fun z θ => ENNReal.ofReal
    (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Jeps ρ ε f) z θ) with hΦ
  -- the pointwise slot estimate
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
      ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z hz =>
      MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
    rw [hΦ, hK, hE1]
    exact HkSqAux.ofReal_GJ_le ρ hρ hε hα hsm hWη hWγ hz hθ k
  -- Tonelli
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
            (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))) := by
    rw [hK, hE1]
    exact HkSqAux.fubini_shift hρ.cont hcont
  -- the log-coordinate shift bound for the shifted integrand
  have h4 : (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))))
      ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C)) := by
    refine lintegral_mono fun p => mul_le_mul_right ?_ _
    rw [hE2, hC]
    exact HkSqAux.integral_shift_le (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂) hmem hcont p
  -- the exponential factors combine
  have h5 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
      = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := by
    have hAB : ∀ p : ℝ × ℝ, E1 p * E2 p = E3 p := by
      intro p
      rw [hE1, hE2, hE3, HkSqAux.ofReal_exp_mul]
      congr 2
      ring
    have hstep1 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
        = ∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C :=
      lintegral_congr fun p => by ring
    have hstep2 : (∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C)
        = (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) * C :=
      MeasureTheory.lintegral_mul_const' C _ ENNReal.ofReal_ne_top
    have hstep3 : (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) = ∫⁻ p : ℝ × ℝ, K p * E3 p :=
      lintegral_congr fun p => by rw [hAB p]
    rw [hstep1, hstep2, hstep3, mul_comm]
  -- the kernel mass bound
  have h6 : (∫⁻ p : ℝ × ℝ, K p * E3 p)
      ≤ ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)) := by
    rw [hK, hE3]
    exact HkSqAux.Jker_exp_integral_le hρ hε hc0 (le_of_lt hδpos)
  have hfinal : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
      ≤ C * ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)) :=
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
        ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))) := h2
      _ = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)))) := h3
      _ ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C)) := h4
      _ = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := h5
      _ ≤ C * ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)) :=
          mul_le_mul_right h6 C
  refine lt_of_le_of_lt hfinal ?_
  refine lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ?_ ?_)
  · rw [hC]; exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

end Work.FTS.StrongEps.JepsHkMem
