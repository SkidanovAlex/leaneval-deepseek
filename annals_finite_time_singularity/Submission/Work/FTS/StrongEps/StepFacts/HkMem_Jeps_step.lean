import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.StepFacts.HkMemJepsStepAux
import Submission.Work.FTS.StrongEps.StepFacts.StepPointwise
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

-- context: namespace Work.FTS.StrongEps.StepFacts. `Jeps ρ ε` is the log-coordinate mollifier, `Quad = (0,∞)×(0,π/2)`,
-- `HkMem α k f` = both iterated integrals of the weighted `HkIntegrand α k f` are integrable.
-- `Work.FTS.StrongEps.StepFacts.step_pointwise` (proved, in module StepFacts/StepPointwise) gives, on the closed quadrant,
-- `ofReal (HkIntegrand α m (Jeps ρ ε u) z θ) ≤ ofReal (ε⁻¹ * Bconst ρ) * ∫⁻p ofReal(Ψ)ofReal(exp)ofReal(HkIntegrand α (m-1) u (shift))`
-- where `Ψ = Psi ρ ε = ε⁻¹ * Jker (ε⁻¹ * rhoTilde ρ) ε` is continuous with compact support (module StepFacts/KernelFacts),
-- and `Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le`, `Jker_comp_zShift_lt_top`,
-- `integrableOn_sliceIntegral_of_lintegral_lt_top`, `aestronglyMeasurable_HkIntegrand_Jeps_slice` are available.
theorem HkMem_Jeps_step (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {m : ℕ} (hm : 2 ≤ m) (hm8 : m ≤ 8) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    {u : ℝ → ℝ → ℝ} (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hMem : Work.Spaces.HkMem α (m - 1) u) :
    Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) := by
  obtain ⟨cη, hcη0, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγ0, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδ0, hJac0⟩ := HkSqAux.logJac_shift_le
  set c : ℝ := max cη cγ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (lt_of_lt_of_le hcη0 (le_max_left _ _))
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
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α (m - 1) u q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α (m - 1) hu
  -- the pointwise step, valid on the whole closed quadrant
  have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ)
          * ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p := by
    intro z hz θ hθ
    by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · simpa only [Kd, Fd, Jint] using
        step_pointwise ρ hρ hε hε1 hα hm hm8 hu hWη hWγ hq.1 hq.2
    · have hzero : Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ = 0 :=
        HkSqAux.HkIntegrand_boundary_zero hα hz hθ hq
      rw [hzero, ENNReal.ofReal_zero]
      exact zero_le
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
          ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ)
            * (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p)) := by
        calc (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
            ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * Bconst ρ)
                * (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p) :=
              MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
                (fun θ hθ => hP z hz θ hθ)
          _ = ENNReal.ofReal (ε⁻¹ * Bconst ρ)
                * (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p) :=
              MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ = ENNReal.ofReal (ε⁻¹ * Bconst ρ)
                * (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p)) := by
              congr 1
              rw [MeasureTheory.lintegral_lintegral_swap
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (ν := MeasureTheory.volume) hpair]
              refine lintegral_congr fun p => ?_
              exact MeasureTheory.lintegral_const_mul' (Kd ρ ε c p)
                (fun θ => Fd α m u z θ p)
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      have hstep2 : (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p))
          ≤ ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (ENNReal.ofReal (Real.exp (3 * |p.2|))
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                  (Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ))) := by
        refine lintegral_mono fun p => mul_le_mul_of_nonneg_left ?_ zero_le
        simpa only [Fd] using JepsHkMem.lintegral_thShift_le
          (fun θ => ENNReal.ofReal
            (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1) θ)) p.2
      have hstep3 : (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (ENNReal.ofReal (Real.exp (3 * |p.2|))
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                  (Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ))))
          = ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (ENNReal.ofReal (Real.exp (3 * |p.2|))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ)) := by
        refine lintegral_congr fun p => ?_
        rw [hGsz p]
      have hstep4 : (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (ENNReal.ofReal (Real.exp (3 * |p.2|))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ)))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
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
        have hKX : Kd ρ ε c p * ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal (Psi ρ ε p)
              * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))) := by
          calc Kd ρ ε c p * ENNReal.ofReal (Real.exp (3 * |p.2|))
              = ENNReal.ofReal (Psi ρ ε p)
                  * (ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                    * ENNReal.ofReal (Real.exp (3 * |p.2|))) := by
                simp only [Kd]; ring
            _ ≤ ENNReal.ofReal (Psi ρ ε p)
                  * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))) :=
                mul_le_mul_of_nonneg_left hexp zero_le
        calc Kd ρ ε c p * (ENNReal.ofReal (Real.exp (3 * |p.2|))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ))
            = (Kd ρ ε c p * ENNReal.ofReal (Real.exp (3 * |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ) := (mul_assoc _ _ _).symm
          _ ≤ (ENNReal.ofReal (Psi ρ ε p)
                * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|))))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) θ) :=
              mul_le_mul_of_nonneg_right hKX zero_le
          _ = ENNReal.ofReal (Psi ρ ε p)
                * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|)))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ) := rfl
      have hchain : (∫⁻ p : ℝ × ℝ, Kd ρ ε c p
            * (∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
              * ENNReal.ofReal (Real.exp ((2 * c + 3) * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1) θ) :=
        hstep2.trans ((le_of_eq hstep3).trans hstep4)
      have hfin_int : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
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
        ENNReal.ofReal (Psi ρ ε q.2)
          * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      aemeasurable_Psi_shift (ρ := ρ) (ε := ε) (c := c) (α := α) (k := m - 1) (u := u) hρ hcont
    have hstep1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p) := by
      calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
          ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (ε⁻¹ * Bconst ρ)
                * (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p) :=
            MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
              (fun z hz => MeasureTheory.setLIntegral_mono'
                (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => hP z hz θ hθ))
        _ = ENNReal.ofReal (ε⁻¹ * Bconst ρ) * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p) := by
            rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun z => ?_
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have htriple : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p)
        = ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p) := by
      have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p)
          = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u q.1 q.2 p
              ∂MeasureTheory.volume ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
                (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
        exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
            ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u q.1 q.2 p)
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
      rw [MeasureTheory.lintegral_const_mul' (Kd ρ ε c p) _
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      congr 1
      rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
      exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => Fd α m u q.1 q.2 p)
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume) _ _]
          exact HkSqAux.aemeasurable_shift_slice hcont p)
    have hstep2 : (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (∫⁻ z in Work.Spaces.Iz,
          ∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p))
        ≤ ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) :=
      lintegral_mono fun p => mul_le_mul_of_nonneg_left
        (HkSqAux.integral_shift_le (δ := δ) (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂) hMem hcont p)
        zero_le
    have hstep3 : (∫⁻ p : ℝ × ℝ, Kd ρ ε c p * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)))
        = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
      rw [← MeasureTheory.lintegral_mul_const'
        (ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun p => ?_
      have hone : Kd ρ ε c p * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          = ENNReal.ofReal (Psi ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) := by
        rw [show Kd ρ ε c p * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            = ENNReal.ofReal (Psi ρ ε p)
              * (ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))) by
              simp only [Kd]; ring]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          show (2 * c * (|p.1| + |p.2|)) + δ * (|p.1| + |p.2|)
            = (2 * c + δ) * (|p.1| + |p.2|) from by ring,
          ← ENNReal.ofReal_mul (Psi_nonneg ρ hρ hε p)]
      calc Kd ρ ε c p * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))
          = (Kd ρ ε c p * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := (mul_assoc _ _ _).symm
        _ = ENNReal.ofReal (Psi ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by rw [hone]
    have hstep4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
        ≤ ENNReal.ofReal (ε⁻¹ * Dmass ρ (2 * c + δ)) := by
      have hγ : (0 : ℝ) ≤ 2 * c + δ := by linarith
      have hint := Psi_moment_integrable ρ hρ hε hε1 hγ
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun p =>
          mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal (Psi_mass ρ hρ hε hε1 hγ)
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, Kd ρ ε c p * Fd α m u z θ p) := hstep1
      _ = ENNReal.ofReal (ε⁻¹ * Bconst ρ) * (∫⁻ p : ℝ × ℝ, Kd ρ ε c p
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Fd α m u z θ p)) := by
          rw [htriple]
      _ ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * (∫⁻ p : ℝ × ℝ, Kd ρ ε c p
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))) :=
          mul_le_mul_of_nonneg_left hstep2 zero_le
      _ = ENNReal.ofReal (ε⁻¹ * Bconst ρ) * ((∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Psi ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) := by rw [hstep3]
      _ ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * (ENNReal.ofReal (ε⁻¹ * Dmass ρ (2 * c + δ))
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

end Work.FTS.StrongEps.StepFacts
