/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/Pointwise.lean`

The pointwise Jensen (Cauchy–Schwarz) bound for the mollifier: the weighted square of `Jeps ρ ε f`
at a point is dominated by the kernel average of the weighted square of `f` at the shifted points,
with the weight ratio `e^{2cε}` taken out.  Everything is carried out in `ℝ≥0∞`, so no
measurability of `f` is needed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.EpsSrc.sq_le_of_forall_mul
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise Jensen bound -/

open scoped ENNReal in
/-- **The abstract pointwise Jensen bound.**  If `J` is the `p`-integral of `Jker ρ ε · B` and
the nonnegative weight `W` is dominated by `e^{c(|p₁|+|p₂|)} Ws p` with `Ws ≥ 0`, then

  `(W J)² ≤ e^{4cε} ∫ p, Jker ρ ε p · (Ws p · B p)²`

(the weight ratio is taken inside the `p`-integral, and the kernel being a probability density
supported in the ball of radius `ε` turns `e^{c|p|}` into `e^{2cε}`). -/
theorem pointwise_aux {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    {B Ws : ℝ × ℝ → ℝ} {W J : ℝ} (hWnn : 0 ≤ W) (hWsnn : ∀ p, 0 ≤ Ws p)
    (hJ : J = ∫ p : ℝ × ℝ, Jker ρ ε p * B p)
    (hker : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hcomp : ∀ p : ℝ × ℝ, W ≤ Real.exp (c * (|p.1| + |p.2|)) * Ws p) :
    ENNReal.ofReal ((W * J) ^ 2)
      ≤ ENNReal.ofReal (Real.exp (4 * c * ε))
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal ((Ws p * B p) ^ 2) := by
  -- (1) the weighted slot is dominated by the kernel-average of the shifted slot
  have hx : ENNReal.ofReal (W * |J|)
      ≤ ENNReal.ofReal (Real.exp (2 * c * ε))
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Ws p * |B p|) := by
    subst hJ
    have h1 : W * ∫ p : ℝ × ℝ, Jker ρ ε p * B p
        = ∫ p : ℝ × ℝ, W * (Jker ρ ε p * B p) :=
      (MeasureTheory.integral_const_mul W _).symm
    have h2 : ‖∫ p : ℝ × ℝ, W * (Jker ρ ε p * B p)‖ₑ
        ≤ ∫⁻ p : ℝ × ℝ, ‖W * (Jker ρ ε p * B p)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    have h3 : ENNReal.ofReal (W * |∫ p : ℝ × ℝ, Jker ρ ε p * B p|)
        = ‖∫ p : ℝ × ℝ, W * (Jker ρ ε p * B p)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, ← h1, abs_mul, abs_of_nonneg hWnn]
    rw [h3]
    refine h2.trans ?_
    have hpt1 : ∀ p : ℝ × ℝ, ‖W * (Jker ρ ε p * B p)‖ₑ
        = ENNReal.ofReal (W * (Jker ρ ε p * |B p|)) := by
      intro p
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_mul, abs_of_nonneg hWnn,
        abs_of_nonneg (HkSqAux.Jker_nonneg ρ hρ ε p)]
    simp only [hpt1]
    calc ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (W * (Jker ρ ε p * |B p|))
        = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal W
            * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|) := by
          refine lintegral_congr (fun p => ?_)
          rw [ENNReal.ofReal_mul hWnn, ENNReal.ofReal_mul (HkSqAux.Jker_nonneg ρ hρ ε p)]
      _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Ws p)
            * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|) := by
          refine lintegral_mono (fun p => ?_)
          have h2' : ENNReal.ofReal W ≤ ENNReal.ofReal (Real.exp (c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Ws p) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            exact ENNReal.ofReal_le_ofReal (hcomp p)
          calc ENNReal.ofReal W * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|)
              ≤ (ENNReal.ofReal (Real.exp (c * (|p.1| + |p.2|))) * ENNReal.ofReal (Ws p))
                  * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|) :=
                mul_le_mul_of_nonneg_right h2' (by positivity)
            _ = ENNReal.ofReal (Real.exp (c * (|p.1| + |p.2|))) * ENNReal.ofReal (Ws p)
                  * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|) := rfl
      _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (2 * c * ε))
            * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Ws p * |B p|)) := by
          refine lintegral_mono (fun p => ?_)
          by_cases hp : Jker ρ ε p = 0
          · rw [hp]; simp
          · have hexp : ENNReal.ofReal (Real.exp (c * (|p.1| + |p.2|)))
                ≤ ENNReal.ofReal (Real.exp (2 * c * ε)) :=
              ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
                have hb := hker p hp
                nlinarith [abs_nonneg p.1, abs_nonneg p.2]))
            calc ENNReal.ofReal (Real.exp (c * (|p.1| + |p.2|))) * ENNReal.ofReal (Ws p)
                  * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|)
                ≤ ENNReal.ofReal (Real.exp (2 * c * ε)) * ENNReal.ofReal (Ws p)
                  * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal |B p|) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hexp zero_le) (by positivity)
              _ = ENNReal.ofReal (Real.exp (2 * c * ε))
                  * (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Ws p * |B p|)) := by
                  rw [ENNReal.ofReal_mul (hWsnn p)]; ring
      _ = ENNReal.ofReal (Real.exp (2 * c * ε))
          * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Ws p * |B p|) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (2) the AM–GM step: `N ≤ t/2 + M/(2t)` for every `t > 0`
  have hN : ∀ t : ℝ, 0 < t →
      (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Ws p * |B p|))
        ≤ ENNReal.ofReal (t / 2)
          + (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal ((Ws p * B p) ^ 2)) * ENNReal.ofReal ((2 * t)⁻¹) := by
    intro t ht
    have hmeas : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2) :=
      ((ENNReal.measurable_ofReal.comp (Jker_continuous hρ ε).measurable)).mul measurable_const
    have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Ws p * |B p|)
        ≤ ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2)
          + ENNReal.ofReal (Jker ρ ε p)
              * (ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹)) := by
      intro p
      have ha0 : 0 ≤ Ws p * |B p| := mul_nonneg (hWsnn p) (abs_nonneg _)
      have hAM : Ws p * |B p| ≤ t / 2 + (Ws p * |B p|) ^ 2 / (2 * t) := by
        rw [← sub_nonneg]
        have h2t : (2 : ℝ) * t ≠ 0 := by linarith
        have heq : t / 2 + (Ws p * |B p|) ^ 2 / (2 * t) - Ws p * |B p|
            = (t - Ws p * |B p|) ^ 2 / (2 * t) := by
          field_simp
          ring
        rw [heq]
        exact div_nonneg (sq_nonneg _) (by linarith)
      have h1 : ENNReal.ofReal (Ws p * |B p|) ≤ ENNReal.ofReal (t / 2)
          + ENNReal.ofReal ((Ws p * |B p|) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹) := by
        calc ENNReal.ofReal (Ws p * |B p|)
            ≤ ENNReal.ofReal (t / 2 + (Ws p * |B p|) ^ 2 / (2 * t)) :=
              ENNReal.ofReal_le_ofReal hAM
          _ = ENNReal.ofReal (t / 2) + ENNReal.ofReal ((Ws p * |B p|) ^ 2 / (2 * t)) :=
              ENNReal.ofReal_add (by linarith) (by positivity)
          _ = ENNReal.ofReal (t / 2)
                + ENNReal.ofReal ((Ws p * |B p|) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹) := by
              congr 1
              rw [div_eq_mul_inv]
              exact ENNReal.ofReal_mul (by positivity)
      have habs : Ws p * |B p| = |Ws p * B p| := by rw [abs_mul, abs_of_nonneg (hWsnn p)]
      have hsq : ENNReal.ofReal ((Ws p * |B p|) ^ 2) = ENNReal.ofReal ((Ws p * B p) ^ 2) := by
        congr 1
        rw [habs, sq_abs]
      rw [hsq] at h1
      calc ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Ws p * |B p|)
          ≤ ENNReal.ofReal (Jker ρ ε p) * (ENNReal.ofReal (t / 2)
              + ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹)) :=
            mul_le_mul_of_nonneg_left h1 zero_le
        _ = ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2)
              + ENNReal.ofReal (Jker ρ ε p)
                  * (ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹)) := by
            ring
    have hmass : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) = 1 := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (Jker_integrable hρ hε)
        (Eventually.of_forall (HkSqAux.Jker_nonneg ρ hρ ε)), Jker_integral_eq_one ρ hρ hε,
        ENNReal.ofReal_one]
    have e1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2))
        = ENNReal.ofReal (t / 2) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) := by
      rw [show (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2))
          = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (t / 2) * ENNReal.ofReal (Jker ρ ε p) from
            lintegral_congr (fun p => mul_comm _ _)]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have e2 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
          * (ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹)))
        = ENNReal.ofReal ((2 * t)⁻¹) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal ((Ws p * B p) ^ 2) := by
      rw [show (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * (ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹)))
          = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((2 * t)⁻¹) * (ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal ((Ws p * B p) ^ 2)) from
            lintegral_congr (fun p => by ring)]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Ws p * |B p|))
        ≤ ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2)
            + ENNReal.ofReal (Jker ρ ε p)
                * (ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹))) :=
          lintegral_mono hpt
      _ = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (t / 2))
            + ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * (ENNReal.ofReal ((Ws p * B p) ^ 2) * ENNReal.ofReal ((2 * t)⁻¹)) :=
          MeasureTheory.lintegral_add_left hmeas _
      _ = ENNReal.ofReal (t / 2) * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p))
            + ENNReal.ofReal ((2 * t)⁻¹) * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal ((Ws p * B p) ^ 2)) := by rw [e1, e2]
      _ = ENNReal.ofReal (t / 2)
            + (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal ((Ws p * B p) ^ 2)) * ENNReal.ofReal ((2 * t)⁻¹) := by
          rw [hmass, mul_one, mul_comm]
  -- (3) squaring the bound with `t = √M`
  have hmain := Work.FTS.StrongEps.EpsSrc.sq_le_of_forall_mul
    (x := ENNReal.ofReal (W * |J|))
    (M := ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal ((Ws p * B p) ^ 2))
    (K := ENNReal.ofReal (Real.exp (2 * c * ε))) ENNReal.ofReal_ne_top
    (fun t ht => hx.trans (mul_le_mul_of_nonneg_left (hN t ht) zero_le))
  have hsqx : (ENNReal.ofReal (W * |J|)) ^ 2 = ENNReal.ofReal ((W * J) ^ 2) := by
    rw [← ENNReal.ofReal_pow (mul_nonneg hWnn (abs_nonneg J)) 2]
    congr 1
    have : W * |J| = |W * J| := by rw [abs_mul, abs_of_nonneg hWnn]
    rw [this, sq_abs]
  have hK2 : (ENNReal.ofReal (Real.exp (2 * c * ε))) ^ 2
      = ENNReal.ofReal (Real.exp (4 * c * ε)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le 2]
    congr 1
    rw [sq, ← Real.exp_add]
    ring_nf
  calc ENNReal.ofReal ((W * J) ^ 2)
      = (ENNReal.ofReal (W * |J|)) ^ 2 := hsqx.symm
    _ ≤ (ENNReal.ofReal (Real.exp (2 * c * ε))) ^ 2
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal ((Ws p * B p) ^ 2)) := hmain
    _ = ENNReal.ofReal (Real.exp (4 * c * ε))
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal ((Ws p * B p) ^ 2)) := by rw [hK2]

open scoped ENNReal in
/-- **Jensen's inequality for the mollifier, with the weight ratio taken inside the
`p`-integral.**  For `(z,θ)` in the closed quadrant,

  `((Jeps ρ ε f)(z,θ) · epsW α z θ)²
     ≤ e^{4cε} ∫ p, Jker ρ ε p · ((f · epsW α)(zShift z p₁, thShift θ p₂))²`

where `c` is a constant with `Wt α z θ ≤ e^{c(|p₁|+|p₂|)} Wt α (zShift z p₁)(thShift θ p₂)`. -/
theorem pointwise_le {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hW : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    ENNReal.ofReal ((Jeps ρ ε f z θ * epsW α z θ) ^ 2)
      ≤ ENNReal.ofReal (Real.exp (4 * c * ε))
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
                * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
  by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · obtain ⟨hzpos, hθIoo⟩ := hq
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hθIoo.1.le, hθIoo.2.le⟩
    have hthIcc : ∀ p : ℝ × ℝ, thShift θ p.2 ∈ Set.Icc (0 : ℝ) (π / 2) :=
      fun p => ⟨(thShift_mem hθIoo).1.le, (thShift_mem hθIoo).2.le⟩
    have hWtp : ∀ p : ℝ × ℝ, epsW α (zShift z p.1) (thShift θ p.2)
        = Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) :=
      fun p => epsW_eq_Wt_of_mem_Iθ (hthIcc p)
    rw [mul_comm (Jeps ρ ε f z θ) (epsW α z θ)]
    rw [epsW_eq_Wt_of_mem_Iθ hθIcc]
    have hRHS : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
                * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
        = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal ((Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)
                * f (zShift z p.1) (thShift θ p.2)) ^ 2) := by
      refine lintegral_congr (fun p => ?_)
      rw [hWtp p]
      congr 1
      ring
    rw [hRHS]
    refine pointwise_aux (ρ := ρ) hρ hε hc
      (B := fun p => f (zShift z p.1) (thShift θ p.2))
      (Ws := fun p => Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (W := Work.Spaces.Wt α z θ) (J := Jeps ρ ε f z θ)
      (Wt_nonneg_Icc hθIcc) (fun p => Wt_nonneg_Icc (hthIcc p))
      (Jeps_eq_integral ρ ε f hzpos hθIoo) ?_ ?_
    · intro p hp
      exact HkSqAux.Jker_support_abs hρ hε hp
    · intro p
      exact hW z θ hzpos hθIoo p
  · have hzero : epsW α z θ = 0 := epsW_eq_zero_of_not_mem_quad hα.1 hz hθ hq
    rw [hzero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
    exact zero_le


end Work.FTS.StrongEps.EpsSqTools
