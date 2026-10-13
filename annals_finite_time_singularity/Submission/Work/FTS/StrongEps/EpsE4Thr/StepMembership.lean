/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/StepMembership.lean`

The **integrated half** of the one-order smoothing of the log-coordinate mollifier `J_ε`:

  `HkMem α (m-1) u  ⟹  HkMem α m (J_ε u)`

from an *abstract* pointwise bound

  `ofReal (HkIntegrand α m (J_ε u) z θ) ≤ ofReal c₀ * ∫⁻ p, Kd ρ ε c p * Fd α m u z θ p`

with an arbitrary finite constant `c₀` (`Kd` is the density `Ψ = ε⁻¹ Jker ρ̃ ε` with the shift
gain, `Fd` the shifted level-`m-1` integrand of `u`).

This is the membership part of `Work.FTS.StrongEps.StepFacts.HkMem_Jeps_step` — the whole file
refactored so that

* the pointwise step (`step_pointwise` there) is *not* used: its conclusion enters as the
  hypothesis `hP`, with the constant left abstract.  Consequently **no hypothesis on `m` above
  `2 ≤ m` is needed** (the `m ≤ 8` of the existing file is used only to replace the count factor
  `(m+1)²` by `81` inside `step_pointwise`);
* the weights and the common constant `c = max cη cγ` do not appear at all: the chain below only
  uses the density `Ψ`, the log-coordinate Jacobian comparison `logJac_shift_le` and the
  angular-shift comparison `lintegral_thShift_le`.

The route is the one of `HkMem_Jeps`: `hP` gives the finiteness of every angular slice by
Tonelli + the `θ`-shift comparison (with the finiteness of the shifted slice from `HkMem α (m-1) u`,
which holds at *every* `z' ∈ Iz`), and the finiteness of the double integral by Tonelli +
`integral_shift_le` + the mass `Psi_mass` of `Ψ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.HkSqAux.integral_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas
import Submission.Work.FTS.StrongEps.JepsHkMem.Jker_comp_zShift_lt_top
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le
import Submission.Work.FTS.StrongEps.JepsHkMem.aemeasurable_pair_slice
import Submission.Work.FTS.StrongEps.JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
import Submission.Work.FTS.StrongEps.StepFacts.KernelFacts
import Submission.Work.FTS.StrongEps.StepFacts.HkMemJepsStepAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.StrongEps.StepFacts (Kd Fd Psi Psi_nonneg Psi_mass Psi_moment_integrable Dmass
  hjstep_Psi_comp_zShift_lt_top hjstep_aemeasurable_pair_slice_Psi aemeasurable_Psi_shift)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The integrated membership step, with the pointwise bound as a hypothesis.**  If the
level-`m` integrand of `J_ε u` is dominated pointwise by a constant times the `p`-average of the
shifted level-`m-1` integrand of `u` (`hP`), then `HkMem α (m-1) u` implies
`HkMem α m (J_ε u)`.  No bound on `m` beyond `2 ≤ m` is used. -/
theorem HkMem_Jeps_of_pointwise {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {m : ℕ} (hm : 2 ≤ m) {ε c c₀ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hc : 0 ≤ c) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hMem : Work.Spaces.HkMem α (m - 1) u)
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        ≤ ENNReal.ofReal c₀
          * ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) :
    Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) := by
  obtain ⟨δ, hδ0, hJac0⟩ := HkSqAux.logJac_shift_le
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α (m - 1) u q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α (m - 1) hu
  -- the `u`-side mass, as an `ℝ≥0∞`-integral
  have hGs_fin : (∫⁻ u' in Set.Ioi 0,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (m - 1) u u' θ)) < ⊤ := by
    have hHz : ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)
        = ∫⁻ u' in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (m - 1) u u' θ) := by
      rw [Work.Spaces.HkSq]
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMem.2
        (Eventually.of_forall fun z' => integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α (m - 1) u z' θ)]
    have hIoi : (∫⁻ u' in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (m - 1) u u' θ))
        = ∫⁻ u' in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (m - 1) u u' θ) :=
      MeasureTheory.setLIntegral_congr
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
    rw [hIoi, ← hHz]
    exact ENNReal.ofReal_lt_top
  -- the angular slice of `J_ε u` is finite for every `z`
  have hslice_fin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)) < ⊤ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) 0 θ))
          = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      simp
    · have hGsz : ∀ p : ℝ × ℝ,
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
              (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1) θ))
            = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1) θ) :=
        fun p => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hMem.1 _ (Work.FTS.StrongEps.zShift_pos hzpos).le)
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ θ)).symm
      have hpair := hjstep_aemeasurable_pair_slice_Psi (ρ := ρ) hρ
        (ε := ε) (c := c) (z := z) hzpos
        (H := fun z' θ' => Work.Spaces.HkIntegrand α (m - 1) u z' θ') hcont
      have hstep1 : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
          ≤ ENNReal.ofReal c₀
            * (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                * (∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p)) := by
        calc (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
            ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                    * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) :=
              MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
                (fun θ hθ => hP z hz θ hθ)
          _ = ENNReal.ofReal c₀
                * (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
                    Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                      * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) :=
              MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ = ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                    * (∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p)) := by
              congr 1
              rw [MeasureTheory.lintegral_lintegral_swap
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (ν := MeasureTheory.volume) hpair]
              refine lintegral_congr fun p => ?_
              exact MeasureTheory.lintegral_const_mul' (Work.FTS.StrongEps.StepFacts.Kd ρ ε c p)
                (fun θ => Work.FTS.StrongEps.StepFacts.Fd α m u z θ p)
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      have hstep2 : (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p))
          ≤ ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.Spaces.HkIntegrand α (m - 1) u
                      (Work.FTS.StrongEps.zShift z p.1) θ))) := by
        refine lintegral_mono fun p => mul_le_mul_of_nonneg_left ?_ zero_le
        simpa only [Work.FTS.StrongEps.StepFacts.Fd] using JepsHkMem.lintegral_thShift_le
          (fun θ => ENNReal.ofReal
            (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1) θ)) p.2
      have hstep3 : (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.Spaces.HkIntegrand α (m - 1) u
                      (Work.FTS.StrongEps.zShift z p.1) θ))))
          = ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α (m - 1) u
                      (Work.FTS.StrongEps.zShift z p.1) θ)) := by
        refine lintegral_congr fun p => ?_
        rw [hGsz p]
      have hstep4 : (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α (m - 1) u
                      (Work.FTS.StrongEps.zShift z p.1) θ)))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
              * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ) := by
        refine lintegral_mono fun p => ?_
        have hexp : ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have h2 : |p.2| ≤ |p.1| + |p.2| := le_add_of_nonneg_left (abs_nonneg _)
          linarith
        have hKX : Work.FTS.StrongEps.StepFacts.Kd ρ ε c p * ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
              * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))) := by
          calc Work.FTS.StrongEps.StepFacts.Kd ρ ε c p * ENNReal.ofReal (Real.exp (3 * |p.2|))
              = ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
                  * (ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                    * ENNReal.ofReal (Real.exp (3 * |p.2|))) := by
                simp only [Work.FTS.StrongEps.StepFacts.Kd]; ring
            _ ≤ ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
                  * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))) :=
                mul_le_mul_of_nonneg_left hexp zero_le
        calc Work.FTS.StrongEps.StepFacts.Kd ρ ε c p * (ENNReal.ofReal (Real.exp (3 * |p.2|))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ))
            = (Work.FTS.StrongEps.StepFacts.Kd ρ ε c p * ENNReal.ofReal (Real.exp (3 * |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ) := (mul_assoc _ _ _).symm
          _ ≤ (ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
                * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ) :=
              mul_le_mul_of_nonneg_right hKX zero_le
          _ = ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
                * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|)))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ) := rfl
      have hchain : (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
              * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ) :=
        hstep2.trans ((le_of_eq hstep3).trans hstep4)
      have hfin_int : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
            * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|)))
            * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ)) < ⊤ :=
        hjstep_Psi_comp_zShift_lt_top ρ hρ hε hzpos (by linarith : (0 : ℝ) ≤ 2 * c + 3) hGs_fin
      exact lt_of_le_of_lt (hstep1.trans (mul_le_mul_of_nonneg_left hchain zero_le))
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_int)
  -- the double `z`,`θ`-integral is finite
  have hdouble : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)) < ⊤ := by
    have hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε q.2)
          * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      aemeasurable_Psi_shift (ρ := ρ) (ε := ε) (c := c) (α := α) (k := m - 1) (u := u) hρ hcont
    have hstep1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
        ≤ ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
              Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) := by
      calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
          ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                    * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) :=
            MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
              (fun z hz => MeasureTheory.setLIntegral_mono'
                (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => hP z hz θ hθ))
        _ = ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
                Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                  * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) := by
            rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun z => ?_
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have htriple : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p)
        = ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) := by
      have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p)
          = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * Work.FTS.StrongEps.StepFacts.Fd α m u q.1 q.2 p
              ∂MeasureTheory.volume ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
                (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
        exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
            ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * Work.FTS.StrongEps.StepFacts.Fd α m u q.1 q.2 p)
          (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
            rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
              (ν := MeasureTheory.volume) _ _]
            exact hAe.lintegral_prod_right')).symm
      rw [hL]
      rw [MeasureTheory.lintegral_lintegral_swap
        (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (ν := MeasureTheory.volume) hAe]
      refine lintegral_congr fun p => ?_
      rw [MeasureTheory.lintegral_const_mul' (Work.FTS.StrongEps.StepFacts.Kd ρ ε c p) _
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      congr 1
      rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
      exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
          Work.FTS.StrongEps.StepFacts.Fd α m u q.1 q.2 p)
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume) _ _]
          exact HkSqAux.aemeasurable_shift_slice hcont p)
    have hstep2 : (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
          * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p))
        ≤ ∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) :=
      lintegral_mono fun p => mul_le_mul_of_nonneg_left
        (HkSqAux.integral_shift_le (δ := δ) (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂) hMem hcont p)
        zero_le
    have hstep3 : (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)))
        = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
      rw [← MeasureTheory.lintegral_mul_const'
        (ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun p => ?_
      have hone : Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          = ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p
              * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) := by
        rw [show Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            = ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p)
              * (ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))) by
              simp only [Work.FTS.StrongEps.StepFacts.Kd]; ring]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          show (2 * c * (|p.1| + |p.2|)) + δ * (|p.1| + |p.2|)
            = (2 * c + δ) * (|p.1| + |p.2|) from by ring,
          ← ENNReal.ofReal_mul (Psi_nonneg ρ hρ hε p)]
      calc Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))
          = (Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := (mul_assoc _ _ _).symm
        _ = ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p
              * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by rw [hone]
    have hstep4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
        ≤ ENNReal.ofReal (ε⁻¹ * Work.FTS.StrongEps.StepFacts.Dmass ρ (2 * c + δ)) := by
      have hγ : (0 : ℝ) ≤ 2 * c + δ := by linarith
      have hint := Psi_moment_integrable ρ hρ hε hε1 hγ
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun p =>
          mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal (Psi_mass ρ hρ hε hε1 hγ)
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
        ≤ ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
              Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
                * Work.FTS.StrongEps.StepFacts.Fd α m u z θ p) := hstep1
      _ = ENNReal.ofReal c₀ * (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.StepFacts.Fd α m u z θ p)) := by
          rw [htriple]
      _ ≤ ENNReal.ofReal c₀ * (∫⁻ p : ℝ × ℝ, Work.FTS.StrongEps.StepFacts.Kd ρ ε c p
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))) :=
          mul_le_mul_of_nonneg_left hstep2 zero_le
      _ = ENNReal.ofReal c₀ * ((∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Work.FTS.StrongEps.StepFacts.Psi ρ ε p
              * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) := by rw [hstep3]
      _ ≤ ENNReal.ofReal c₀
            * (ENNReal.ofReal (ε⁻¹ * Work.FTS.StrongEps.StepFacts.Dmass ρ (2 * c + δ))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep4 zero_le) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- the first `HkMem` component
  have hSliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ =>
        Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ =>
          Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) 0 θ) = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      exact integrableOn_zero
    · refine ⟨JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps_slice hρ.moll hε hu hzpos, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun θ => ?_) (hslice_fin z hz)
      rw [Real.enorm_eq_ofReal
        (Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)]
  exact ⟨hSliceInt, JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
    hSliceInt (JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps hρ.moll hε hu) hdouble⟩

end Work.FTS.StrongEps.EpsE4Thr
