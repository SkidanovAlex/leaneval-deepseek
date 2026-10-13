/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSq_Jeps_le.lean`

**E1 for the strong-`ε` space `X`**: the log-coordinate mollifier `Jeps ρ ε` is bounded on the
weighted space `X` ((`EpsSq`, `EpsMem`) of `EpsSpace.lean`) up to a factor `e^{Cε}`:

  `EpsSq α (Jeps ρ ε f) ≤ e^{Cε} · EpsSq α f`,

where `EpsSq α f = ∫∫ (f · w / sin(2θ)^{γ/2})²` is the strongest weighted `L²` size carried by the
`ε`-scheme (`γ = 1 + α/10`), and `Jeps` is, in the coordinates `s = log z`, `ζ = log tan θ`, the
convolution with the probability density `Jker ρ ε`.

## Route

The proof follows the `HkSq_Jeps_le` pattern, specialised to the single slot `(j,i) = (0,0)`;
the ingredients live in the modules `EpsSrc` (delegated) and `EpsSqTools`:

1. `EpsSrc.ofReal_EpsSq_eq_lintegral`: `EpsSq` is the iterated `lintegral` of its integrand.
2. `EpsSqTools.pointwise_le`: Jensen (Cauchy–Schwarz) for the probability density `Jker ρ ε`, with
   the weight ratio `e^{2cε}` taken out via the shift comparison `Wt_shift_le`; carried out entirely
   in `ℝ≥0∞`, so no measurability of `f` is needed.
3. `EpsSqTools.shift_step`: in the log coordinates the shift `(z,θ) ↦ (zShift z p₁, thShift θ p₂)`
   is a translation, so only the Jacobian `logJac` has to be compared (`logJac_shift_le`).
4. `EpsSqTools.aemeasurable_shift_comp'`: the a.e. measurability of the shifted integrand, which is
   what makes Tonelli's theorem applicable in the assembly.
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one
import Submission.Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.Pointwise
import Submission.Work.FTS.StrongEps.EpsSqTools.Measurable
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift

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
