import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Submission.Work.BoseFixB1S.AnovaInfra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PiLintegral` — the `ℝ≥0∞` (Tonelli) peel for the product measure

The Bochner peel `Work.BoseFixB1S.pi_peel` (in `AnovaInfra.lean`) requires the integrability of the
peeled function.  For the `L²`-theory of the ANOVA bound one also needs the *unconditional*
`ℝ≥0∞`-version — integrating the sliced `lintegral` of a nonnegative function over a product
measure multiplies by the mass of the peeled coordinate:

`∫⁻ x, (∫⁻ z, F (update x j z) ∂ν) ∂π = (ν univ) * ∫⁻ x, F x ∂π`.

Two consequences are recorded: the a.e. measurability of the sliced `lintegral` map, and the a.e.
finiteness of the slice `L²`-masses of an `L²` function (`ae_pi_slice_lintegral_lt_top`), which is
what makes the fibre Cauchy–Schwarz/Jensen step of the ANOVA bound legitimate.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

variable {α : Type*} [MeasurableSpace α]

/-- **The sliced `lintegral` map is a.e. strongly measurable.** -/
theorem aemeasurable_pi_slice_lintegral (ν : Measure α) [SigmaFinite ν]
    {k : ℕ} (j : Fin (k + 1)) {F : (Fin (k + 1) → α) → ℝ≥0∞}
    (hF : AEMeasurable F (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    AEMeasurable (fun x : Fin (k + 1) → α => ∫⁻ z, F (Function.update x j z) ∂ν)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  have hmp' : MeasurePreserving (e.symm) (ν.prod ρ)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    MeasurePreserving.symm e (measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j)
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hFe : AEMeasurable (fun p : α × (Fin k → α) => F (e.symm p)) (ν.prod ρ) :=
    hF.comp_quasiMeasurePreserving hmp'.quasiMeasurePreserving
  have hG : AEMeasurable (fun r : Fin k → α => ∫⁻ z, F (e.symm (z, r)) ∂ν) ρ :=
    hFe.lintegral_prod_left'
  have hGs : AEMeasurable (fun p : α × (Fin k → α) => ∫⁻ z, F (e.symm (z, p.2)) ∂ν)
      (ν.prod ρ) := hG.comp_snd
  refine (hmp'.aemeasurable_comp_iff hemb).mp ?_
  refine hGs.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply]
  congr 1
  funext z
  rw [piFinSuccAbove_update]

/-- **The `ℝ≥0∞` peel.**  The unconditional (Tonelli) form of `pi_peel`. -/
theorem pi_lintegral_peel (ν : Measure α) [SigmaFinite ν]
    {k : ℕ} (j : Fin (k + 1)) {F : (Fin (k + 1) → α) → ℝ≥0∞}
    (hF : AEMeasurable F (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∫⁻ x, (∫⁻ z, F (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = (ν Set.univ) * ∫⁻ x, F x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  let π : Measure (Fin (k + 1) → α) := Measure.pi (fun _ : Fin (k + 1) => ν)
  have hmp : MeasurePreserving e π (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod ρ) π := MeasurePreserving.symm e hmp
  have hFe : AEMeasurable (fun p : α × (Fin k → α) => F (e.symm p)) (ν.prod ρ) :=
    hF.comp_quasiMeasurePreserving hmp'.quasiMeasurePreserving
  have hG : AEMeasurable (fun r : Fin k → α => ∫⁻ z, F (e.symm (z, r)) ∂ν) ρ :=
    hFe.lintegral_prod_left'
  have hGs : AEMeasurable (fun p : α × (Fin k → α) => ∫⁻ z, F (e.symm (z, p.2)) ∂ν)
      (ν.prod ρ) := hG.comp_snd
  have hS : AEMeasurable (fun x : Fin (k + 1) → α => ∫⁻ z, F (Function.update x j z) ∂ν) π :=
    aemeasurable_pi_slice_lintegral ν j hF
  -- (1) transport the outer integral along `e.symm`
  have h1a : ∫⁻ x, (∫⁻ z, F (Function.update x j z) ∂ν) ∂π
      = ∫⁻ p, (∫⁻ z, F (Function.update (e.symm p) j z) ∂ν) ∂(ν.prod ρ) := by
    rw [← hmp'.map_eq]
    exact lintegral_map' (by rwa [hmp'.map_eq]) hmp'.aemeasurable
  have h1 : ∫⁻ x, (∫⁻ z, F (Function.update x j z) ∂ν) ∂π
      = ∫⁻ p, (∫⁻ z, F (e.symm (z, p.2)) ∂ν) ∂(ν.prod ρ) := by
    rw [h1a]
    apply lintegral_congr
    intro p
    congr 1
    funext z
    rw [piFinSuccAbove_update]
  -- (2) the peeled integrand does not depend on the first coordinate
  have h2 : ∫⁻ p, (∫⁻ z, F (e.symm (z, p.2)) ∂ν) ∂(ν.prod ρ)
      = (ν Set.univ) * ∫⁻ r, (∫⁻ z, F (e.symm (z, r)) ∂ν) ∂ρ := by
    rw [lintegral_prod (f := fun p : α × (Fin k → α) => ∫⁻ z, F (e.symm (z, p.2)) ∂ν) hGs]
    simp only [Prod.snd, Function.comp_apply]
    rw [lintegral_const, mul_comm]
  -- (3) Tonelli for the inner pair
  have hsw : AEMeasurable (fun z : (Fin k → α) × α => F (e.symm (z.2, z.1))) (ρ.prod ν) :=
    AEMeasurable.prod_swap hFe
  have h3 : ∫⁻ r, (∫⁻ z, F (e.symm (z, r)) ∂ν) ∂ρ
      = ∫⁻ p, F (e.symm p) ∂(ν.prod ρ) := by
    rw [lintegral_lintegral hsw]
    exact lintegral_prod_swap (fun p : α × (Fin k → α) => F (e.symm p))
  -- (4) transport back
  have h4 : ∫⁻ p, F (e.symm p) ∂(ν.prod ρ) = ∫⁻ x, F x ∂π := by
    rw [← hmp'.map_eq]
    exact (lintegral_map' (by rwa [hmp'.map_eq]) hmp'.aemeasurable).symm
  calc ∫⁻ x, (∫⁻ z, F (Function.update x j z) ∂ν) ∂π
      = ∫⁻ p, (∫⁻ z, F (e.symm (z, p.2)) ∂ν) ∂(ν.prod ρ) := h1
    _ = (ν Set.univ) * ∫⁻ r, (∫⁻ z, F (e.symm (z, r)) ∂ν) ∂ρ := h2
    _ = (ν Set.univ) * ∫⁻ p, F (e.symm p) ∂(ν.prod ρ) := by rw [h3]
    _ = (ν Set.univ) * ∫⁻ x, F x ∂π := by rw [h4]

/-- **A.e. finiteness of the slice `L²`-masses of an `L²` function.** -/
theorem ae_pi_slice_lintegral_lt_top (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    {k : ℕ} (j : Fin (k + 1)) {u : (Fin (k + 1) → α) → ℝ}
    (hum : AEStronglyMeasurable u (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hu2 : Integrable (fun x => (u x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      ∫⁻ z, ‖u (Function.update x j z)‖ₑ ^ 2 ∂ν < ∞ := by
  classical
  let π : Measure (Fin (k + 1) → α) := Measure.pi (fun _ : Fin (k + 1) => ν)
  have hF : AEMeasurable (fun x : Fin (k + 1) → α => ‖u x‖ₑ ^ 2) π :=
    hum.aemeasurable.enorm.pow_const 2
  have hUF : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂π < ∞ := by
    have hfin : ∫⁻ x, ‖(fun y => (u y) ^ 2) x‖ₑ ∂π < ⊤ :=
      (hasFiniteIntegral_iff_enorm).mp hu2.hasFiniteIntegral
    refine lt_of_eq_of_lt ?_ hfin
    apply lintegral_congr
    intro x
    rw [enorm_pow]
  have hpeel := pi_lintegral_peel ν j hF
  have hSfin : ∫⁻ x, (∫⁻ z, ‖u (Function.update x j z)‖ₑ ^ 2 ∂ν) ∂π ≠ ∞ := by
    rw [hpeel]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) hUF.ne
  have hmeas := aemeasurable_pi_slice_lintegral ν j hF
  exact MeasureTheory.ae_lt_top' hmeas hSfin

end Work.BoseFixB1S
