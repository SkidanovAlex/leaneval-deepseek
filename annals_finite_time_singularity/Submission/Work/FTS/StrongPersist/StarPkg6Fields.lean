import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.StrongEps.EpsSqTools.Pointwise
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSq_Jeps_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The iterated set integral over `Iz × Iθ` is the product-measure integral.** -/
theorem setIntegral_prod_eq (F : ℝ → ℝ → ENNReal)
    (hF : AEMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, F z θ)
      = ∫⁻ q : ℝ × ℝ, F q.1 q.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [← MeasureTheory.setLIntegral_prod (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume) (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ)
      (fun q : ℝ × ℝ => F q.1 q.2) hF,
    ← Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      Work.Spaces.Iz Work.Spaces.Iθ]

/-- **The product-measure integral is at most the iterated integral** (no measurability needed). -/
theorem prod_integral_le_setIntegral (F : ℝ → ℝ → ENNReal) :
    (∫⁻ q : ℝ × ℝ, F q.1 q.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, F z θ :=
  MeasureTheory.lintegral_prod_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun q : ℝ × ℝ => F q.1 q.2)

theorem EpsSq_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ → ℝ,
        EpsMem α f → EpsMem α (Jeps ρ ε f) →
        EpsSq α (Jeps ρ ε f) ≤ Real.exp (C * ε) * EpsSq α f := by
  obtain ⟨c, hcpos, hWc⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := HkSqAux.logJac_shift_le
  refine ⟨4 * c + 2 * δ, by positivity, ?_⟩
  intro α hα ε hε hε1 f hf hJf
  have hc0 : 0 ≤ c := hcpos.le
  have hWshift : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) :=
    fun z θ hz hθ p => hWc α hα z θ p.1 p.2 hz hθ
  have hGmeas : AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (((Jeps ρ ε f) q.1 q.2 * epsW α q.1 q.2) ^ 2))
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hJf.aestronglyMeasurable.aemeasurable
  have hKmeas : AEMeasurable (Function.uncurry (fun q p : ℝ × ℝ =>
      ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal ((f (zShift q.1 p.1) (thShift q.2 p.2)
        * epsW α (zShift q.1 p.1) (thShift q.2 p.2)) ^ 2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
    have hFmeas : AEMeasurable (fun q : ℝ × ℝ =>
        ENNReal.ofReal ((f q.1 q.2 * epsW α q.1 q.2) ^ 2))
        (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable
    have hGmeas' := EpsSqTools.aemeasurable_shift_comp' hFmeas
    have hJmeas : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Jker ρ ε z.2))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      (ENNReal.measurable_ofReal.comp
        ((Jker_continuous hρ ε).measurable.comp measurable_snd)).aemeasurable
    convert hJmeas.mul hGmeas' using 1
    ext z
    simp only [Function.uncurry, Pi.mul_apply]
  have hmain : ENNReal.ofReal (EpsSq α (Jeps ρ ε f))
      ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε) * EpsSq α f) := by
    have h1 : ENNReal.ofReal (EpsSq α (Jeps ρ ε f))
        = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (((Jeps ρ ε f) q.1 q.2 * epsW α q.1 q.2) ^ 2)
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral hJf,
        setIntegral_prod_eq (F := fun z θ =>
          ENNReal.ofReal (((Jeps ρ ε f) z θ * epsW α z θ) ^ 2)) hGmeas]
    calc ENNReal.ofReal (EpsSq α (Jeps ρ ε f))
        = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (((Jeps ρ ε f) q.1 q.2 * epsW α q.1 q.2) ^ 2)
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := h1
      _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Real.exp (4 * c * ε))
            * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal ((f (zShift q.1 p.1) (thShift q.2 p.2)
                    * epsW α (zShift q.1 p.1) (thShift q.2 p.2)) ^ 2)
                ∂MeasureTheory.volume)
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
          refine MeasureTheory.lintegral_mono (fun q => ?_)
          by_cases hq : q.1 ∈ Work.Spaces.Iz ∧ q.2 ∈ Work.Spaces.Iθ
          · exact EpsSqTools.pointwise_le (ρ := ρ) (c := c) hρ hε hc0 hα hWshift hq.1 hq.2
          · have hz0 : ¬(0 < q.1 ∧ q.2 ∈ Set.Ioo 0 (π / 2)) := fun h =>
              hq ⟨h.1.le, ⟨h.2.1.le, h.2.2.le⟩⟩
            rw [Jeps_eq_zero ρ ε f hz0, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
              ENNReal.ofReal_zero]
            exact zero_le
      _ = ENNReal.ofReal (Real.exp (4 * c * ε))
            * ∫⁻ q : ℝ × ℝ, (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal ((f (zShift q.1 p.1) (thShift q.2 p.2)
                    * epsW α (zShift q.1 p.1) (thShift q.2 p.2)) ^ 2)
                ∂MeasureTheory.volume)
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (Real.exp (4 * c * ε))
            * ∫⁻ p : ℝ × ℝ, (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal ((f (zShift q.1 p.1) (thShift q.2 p.2)
                    * epsW α (zShift q.1 p.1) (thShift q.2 p.2)) ^ 2)
                ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                  (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
            ∂MeasureTheory.volume := by
          congr 1
          exact MeasureTheory.lintegral_lintegral_swap (μ := (MeasureTheory.volume.restrict
            Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
            (ν := MeasureTheory.volume) hKmeas
      _ = ENNReal.ofReal (Real.exp (4 * c * ε))
            * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * (∫⁻ q : ℝ × ℝ, ENNReal.ofReal ((f (zShift q.1 p.1) (thShift q.2 p.2)
                    * epsW α (zShift q.1 p.1) (thShift q.2 p.2)) ^ 2)
                    ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                      (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
            ∂MeasureTheory.volume := by
          congr 1
          refine MeasureTheory.lintegral_congr (fun p => ?_)
          exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (4 * c * ε))
            * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                    * ENNReal.ofReal (EpsSq α f))
            ∂MeasureTheory.volume := by
          refine mul_le_mul_of_nonneg_left (lintegral_mono (fun p => ?_)) zero_le
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          refine le_trans (prod_integral_le_setIntegral (fun z θ => ENNReal.ofReal
            ((f (zShift z p.1) (thShift θ p.2) * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))) ?_
          exact EpsSqTools.shift_step hf hJac0 p
      _ = ENNReal.ofReal (Real.exp (4 * c * ε)) * ENNReal.ofReal (EpsSq α f)
            * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                ∂MeasureTheory.volume) := by
          rw [show (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                    * ENNReal.ofReal (EpsSq α f)) ∂MeasureTheory.volume)
              = ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                  * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))))
                  * ENNReal.ofReal (EpsSq α f) ∂MeasureTheory.volume from
              lintegral_congr (fun p => by ring)]
          rw [MeasureTheory.lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          ring
      _ ≤ ENNReal.ofReal (Real.exp (4 * c * ε)) * ENNReal.ofReal (EpsSq α f)
            * ENNReal.ofReal (Real.exp (2 * δ * ε)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          simpa using HkSqAux.Jker_exp_integral_le hρ hε (c := 0) (δ := δ) (le_refl 0) hδpos.le
      _ = ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε) * EpsSq α f) := by
          rw [show Real.exp ((4 * c + 2 * δ) * ε)
                = Real.exp (4 * c * ε) * Real.exp (2 * δ * ε) from by
              rw [← Real.exp_add]
              congr 1
              ring]
          rw [ENNReal.ofReal_mul
              (by positivity : (0 : ℝ) ≤ Real.exp (4 * c * ε) * Real.exp (2 * δ * ε)),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.exp (4 * c * ε))]
          ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.exp_pos _).le (EpsSq_nonneg α f))).mp hmain

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.StarPkg6Fields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.PhiStar (F0 Fb)

/-! ## The master constants -/



/-! ## Monomial absorption -/

/-- Three `M`-bounded factors and an `M`-power are dominated by `2^45·M^40`. -/
theorem mono3_le_big {M : ℝ} (hM : 1 ≤ M) {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37)
    {u v w : ℝ} (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w)
    (hwM : w ≤ M) : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 := by
  have hM0 : 0 ≤ M := by linarith
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ 45 := pow_le_pow_right₀ (by norm_num) hj
  have hleft : (2 : ℝ) ^ j * u * v * w ≤ 2 ^ 45 * (M * M * M) := by
    have ha : u * v ≤ M * M := mul_le_mul huM hvM hv0 hM0
    have hb : w ≤ M := hwM
    calc (2 : ℝ) ^ j * u * v * w = (2 ^ j * (u * v)) * w := by ring
      _ ≤ (2 ^ 45 * (M * M)) * M :=
          mul_le_mul (mul_le_mul h2 ha (by positivity) (by positivity)) hb hw0
            (mul_nonneg (by positivity) (by positivity))
      _ = 2 ^ 45 * (M * M * M) := by ring
  have hc' : M ^ c ≤ M ^ 37 := pow_le_pow_right₀ hM (by omega)
  calc (2 : ℝ) ^ j * u * v * w * M ^ c = ((2 : ℝ) ^ j * u * v * w) * M ^ c := rfl
    _ ≤ (2 ^ 45 * (M * M * M)) * M ^ 37 :=
        mul_le_mul hleft hc' (by positivity) (by positivity)
    _ = 2 ^ 45 * M ^ 40 := by ring




/-- A monomial is dominated by the unit budget. -/
theorem mono_le_unit {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37) {u v w : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M) :
    (2 : ℝ) ^ j * u * v * w * M ^ c * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 :=
    mono3_le_big hM hj hc hu0 huM hv0 hvM hw0 hwM
  have hS1 : S ≤ (α + 1) * S := by nlinarith
  calc (2 : ℝ) ^ j * u * v * w * M ^ c * S ≤ (2 ^ 45 * M ^ 40) * S :=
        mul_le_mul_of_nonneg_right h1 hS
    _ ≤ (2 ^ 45 * M ^ 40) * ((α + 1) * S) :=
        mul_le_mul_of_nonneg_left hS1 (by positivity)
    _ = (2 ^ 45 * M ^ 40) * (α + 1) * S := by ring

/-- A monomial with one factor of `α` is dominated by the unit budget. -/
theorem mono_le_unit_alpha {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37) {u v w : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M) :
    (2 : ℝ) ^ j * u * v * w * M ^ c * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 :=
    mono3_le_big hM hj hc hu0 huM hv0 hvM hw0 hwM
  have hαS : α * S ≤ (α + 1) * S := by nlinarith
  calc (2 : ℝ) ^ j * u * v * w * M ^ c * α * S
      = ((2 : ℝ) ^ j * u * v * w * M ^ c) * (α * S) := by ring
    _ ≤ (2 ^ 45 * M ^ 40) * ((α + 1) * S) :=
        mul_le_mul h1 hαS (by positivity) (by positivity)
    _ = (2 ^ 45 * M ^ 40) * (α + 1) * S := by ring

/-- Eight units fit into the final constant. -/
theorem eight_unit_le {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    8 * ((2 ^ 45 * M ^ 40) * (α + 1) * S) ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have hM0 : 0 ≤ M := by linarith
  have hM40 : (0 : ℝ) ≤ M ^ 40 := pow_nonneg hM0 40
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  have h7 : (8 : ℝ) * 2 ^ 45 ≤ 2 ^ 48 := by norm_num
  have h8 : 8 * 2 ^ 45 * M ^ 40 ≤ 2 ^ 48 * M ^ 40 :=
    mul_le_mul_of_nonneg_right h7 hM40
  have h9 : 8 * 2 ^ 45 * M ^ 40 * (α + 1) ≤ 2 ^ 48 * M ^ 40 * (α + 1) :=
    mul_le_mul_of_nonneg_right h8 hα1
  have h10 : 2 ^ 48 * M ^ 40 * (α + 1) ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) :=
    mul_le_mul_of_nonneg_right (by linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 ^ 48) hM40])
      hα1
  calc 8 * ((2 ^ 45 * M ^ 40) * (α + 1) * S) = (8 * 2 ^ 45 * M ^ 40) * (α + 1) * S := by ring
    _ ≤ (2 ^ 48 * M ^ 40) * (α + 1) * S := mul_le_mul_of_nonneg_right h9 hS
    _ ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := mul_le_mul_of_nonneg_right h10 hS


end Work.FTS.StrongPersist
end
end
