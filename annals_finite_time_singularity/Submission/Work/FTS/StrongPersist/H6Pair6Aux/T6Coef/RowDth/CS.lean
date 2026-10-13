/-
The iterated Cauchy–Schwarz inequality for a nonnegative weight on `Iz × Iθ`.

`cs_iterated` is the two-step (angular, then radial) Cauchy–Schwarz inequality

  `∫_z∫_θ ρ |A| |B| ≤ √(∫_z∫_θ ρ A²) · √(∫_z∫_θ ρ B²)`,

whose hypotheses are exactly the integrability of the two weighted squares (angular slices
and `z`-marginals); `cs_sqrt_le_ae` is the one-dimensional square-root form used in both steps.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

set_option maxHeartbeats 1600000

/-- The square-root form of the Cauchy–Schwarz inequality on a set, with a.e. nonnegativity. -/
theorem cs_sqrt_le_ae {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hAnn : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), 0 ≤ A x)
    (hBnn : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (hAnn.mono (fun x hx => (Real.sq_sqrt hx).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (hBnn.mono (fun x hx => (Real.sq_sqrt hx).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (hAnn.mono fun x hx => Real.sq_sqrt hx)
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (hBnn.mono fun x hx => Real.sq_sqrt hx)
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg_of_ae hAnn) _

/-- **Iterated Cauchy–Schwarz.**  For a weight `ρ` nonnegative on `Iz × Iθ` and functions
`A`, `B` whose weighted squares have integrable angular slices and integrable marginals,

`∫∫ ρ |A| |B| ≤ √(∫∫ ρ A²) · √(∫∫ ρ B²)`. -/
theorem cs_iterated {ρ A B : ℝ → ℝ → ℝ}
    (hρ : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hsA : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (A z θ) ^ 2) Work.Spaces.Iθ)
    (hsB : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (B z θ) ^ 2) Work.Spaces.Iθ)
    (hmA : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2) Work.Spaces.Iz)
    (hmB : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2 with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2 with hG
  have hFA : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 ≤ F z :=
    MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
  have hGA : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 ≤ G z :=
    MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
        ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hcongr : (∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
        = ∫ θ in Work.Spaces.Iθ, Real.sqrt (ρ z θ * (A z θ) ^ 2)
            * Real.sqrt (ρ z θ * (B z θ) ^ 2) := by
      refine integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_))
      show ρ z θ * |A z θ| * |B z θ|
        = Real.sqrt (ρ z θ * (A z θ) ^ 2) * Real.sqrt (ρ z θ * (B z θ) ^ 2)
      have hsq : (Real.sqrt (ρ z θ)) ^ 2 = ρ z θ := Real.sq_sqrt (hρ z hz θ hθ)
      have hmul : Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) = ρ z θ := by rw [← sq, hsq]
      have hA' : Real.sqrt (ρ z θ * (A z θ) ^ 2) = Real.sqrt (ρ z θ) * |A z θ| := by
        rw [Real.sqrt_mul (hρ z hz θ hθ), Real.sqrt_sq_eq_abs]
      have hB' : Real.sqrt (ρ z θ * (B z θ) ^ 2) = Real.sqrt (ρ z θ) * |B z θ| := by
        rw [Real.sqrt_mul (hρ z hz θ hθ), Real.sqrt_sq_eq_abs]
      calc ρ z θ * |A z θ| * |B z θ|
          = Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) * |A z θ| * |B z θ| := by rw [hmul]
        _ = (Real.sqrt (ρ z θ) * |A z θ|) * (Real.sqrt (ρ z θ) * |B z θ|) := by ring
        _ = Real.sqrt (ρ z θ * (A z θ) ^ 2) * Real.sqrt (ρ z θ * (B z θ) ^ 2) := by
              rw [hA', hB']
    rw [hcongr]
    exact cs_sqrt_le_ae (hsA z hz) (hsB z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hIθm
        (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
      (MeasureTheory.ae_restrict_of_forall_mem hIθm
        (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := by
    refine integral_mono_of_nonneg ?_ ?_ (MeasureTheory.ae_restrict_of_forall_mem hIzm hslice)
    · exact MeasureTheory.ae_restrict_of_forall_mem hIzm
        (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
          (fun θ hθ => mul_nonneg (mul_nonneg (hρ z hz θ hθ) (abs_nonneg _)) (abs_nonneg _)))
    · have hF_sq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hmA.congr (hFA.mono (fun z hz => (Real.sq_sqrt hz).symm))
      have hG_sq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hmB.congr (hGA.mono (fun z hz => (Real.sq_sqrt hz).symm))
      have hF_lp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable
          hmA.aestronglyMeasurable)).mpr hF_sq
      have hG_lp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable
          hmB.aestronglyMeasurable)).mpr hG_sq
      exact memLp_one_iff_integrable.mp (hF_lp.mul hG_lp)
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        cs_sqrt_le_ae hmA hmB hFA hGA
    _ = Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2) := by
        simp only [hF, hG]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
