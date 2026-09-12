import Submission.Serre

/-!
# Mean of Serre's measure

Layer-2 brick: the identity function is integrable against the equilibrium
measure and against Serre's measure `ν`, and the first moment of

    μ = γ·ν + (1−γ)·μ_eq     (on `[a,b]`, `0 < a < b`, `0 ≤ γ ≤ 1`)

equals `γ·√(a·b) + (1−γ)·(a+b)/2`.

Supporting facts available (all proof-complete):
  `Submission.Equilibrium.equilibrium_mean a b : ∫ x, x ∂equilibrium a b = (a+b)/2`
  `Submission.Equilibrium.equilibrium_compl_Icc a b hab : equilibrium a b ((Icc a b)ᶜ) = 0`
  `Submission.Equilibrium.equilibrium_eq_restrict_Icc a b hab`
  `Submission.Serre.nu_mean (ha : 0 < a) (hab : a < b) : ∫ x, x ∂nu a b = √(a·b)`
  `Submission.Serre.serreMeasure γ a b = ENNReal.ofReal γ • nu a b + ENNReal.ofReal (1−γ) • equilibrium a b`
  (coefficients are ENNReal since `Measure` is an ENNReal-module).

Suggested route: (1) `id` is bounded on `[a,b]`, so integrable against
`equilibrium a b` and `nu a b` (both of which give mass 1 to `[a,b]`, via the
complement-zero and restriction lemmas); (2) expand the integral of the
combination by `MeasureTheory.integral_add`, `MeasureTheory.integral_smul_measure`
(ENNReal scalar → `c.toReal`), and the fact that `(ENNReal.ofReal γ).toReal = γ`
for `0 ≤ γ`; (3) feed in `equilibrium_mean` and `nu_mean`.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.SerreMean

open Submission.Equilibrium
open Submission.Serre

/-- Inversion maps the reciprocal interval `[1/b, 1/a]` into `[a,b]`
(for `0 < a < b`). -/
lemma invMap_mem_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b) {t : ℝ}
    (ht : t ∈ Set.Icc (b⁻¹) (a⁻¹)) : invMap t ∈ Set.Icc a b := by
  have hb : 0 < b := lt_trans ha hab
  have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hb) ht.1
  constructor
  · unfold invMap
    -- a ≤ t⁻¹, from t ≤ a⁻¹ (both sides positive)
    have hlt : a ≤ t⁻¹ := by
      have h := (inv_le_inv₀ (inv_pos.mpr ha) ht0).2 ht.2  -- (a⁻¹)⁻¹ ≤ t⁻¹
      simpa using h
    simpa using hlt
  · unfold invMap
    -- t⁻¹ ≤ b, from b⁻¹ ≤ t (both sides positive)
    have h := (inv_le_inv₀ ht0 (inv_pos.mpr hb)).2 ht.1  -- t⁻¹ ≤ (b⁻¹)⁻¹
    simpa using h

/-- The identity function is integrable with respect to the equilibrium measure
of `[a,b]` (finite measure supported on the bounded interval `[a,b]`). -/
lemma equilibrium_integrable_id {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun x : ℝ => x) (equilibrium a b) := by
  apply MeasureTheory.Integrable.of_mem_Icc (a := a) (b := b)
  · exact measurable_id.aemeasurable
  · -- the equilibrium measure gives no mass to the complement of `[a,b]`
    rw [MeasureTheory.ae_iff]
    exact equilibrium_compl_Icc a b hab

/-- The identity function is integrable with respect to Serre's measure `ν`. -/
lemma nu_integrable_id {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun x : ℝ => x) (nu a b) := by
  apply MeasureTheory.Integrable.of_mem_Icc (a := a) (b := b)
  · exact measurable_id.aemeasurable
  · -- `ν` gives no mass outside `[a,b]`: it is the image of the equilibrium
    -- measure of `[1/b, 1/a]` under inversion, and inversion maps that
    -- interval into `[a,b]`.
    have hb : 0 < b := lt_trans ha hab
    have h01 : b⁻¹ ≤ a⁻¹ := by
      exact (inv_le_inv₀ hb ha).2 hab.le
    have hνcompl : nu a b ((Set.Icc a b)ᶜ) = 0 := by
      unfold nu
      rw [Measure.map_apply invMap_measurable (MeasurableSet.compl isClosed_Icc.measurableSet)]
      apply measure_mono_null
      · intro t ht
        change t ∉ Set.Icc (b⁻¹) (a⁻¹)
        intro htIcc
        have hcontra : invMap t ∉ Set.Icc a b := by
          simpa using ht
        exact hcontra (invMap_mem_Icc ha hab htIcc)
      · exact equilibrium_compl_Icc (b⁻¹) (a⁻¹) h01
    rw [MeasureTheory.ae_iff]
    exact hνcompl

/-- First moment of Serre's measure on `[a,b]` (for `0 < a < b`, `0 ≤ γ ≤ 1`):
`∫ x dμ = γ·√(ab) + (1−γ)·(a+b)/2`. -/
lemma serre_mean {a b γ : ℝ} (ha : 0 < a) (hab : a < b) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∫ x : ℝ, x ∂serreMeasure γ a b) = γ * Real.sqrt (a * b) + (1 - γ) * (a + b) / 2 := by
  -- the identity is integrable against both summand measures
  have hI1 : Integrable (fun x : ℝ => x) (ENNReal.ofReal γ • nu a b) :=
    (nu_integrable_id ha hab).smul_measure ENNReal.ofReal_ne_top
  have hI2 : Integrable (fun x : ℝ => x) (ENNReal.ofReal (1 - γ) • equilibrium a b) :=
    (equilibrium_integrable_id hab.le).smul_measure ENNReal.ofReal_ne_top
  unfold serreMeasure
  -- integral over a sum of measures splits (both summands integrable)
  rw [MeasureTheory.integral_add_measure hI1 hI2]
  -- ENNReal scalar factors pull out as `c.toReal`
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal hγ0]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - γ)]
  -- first moments of `ν` and of the equilibrium measure
  rw [nu_mean ha hab]
  rw [equilibrium_mean]
  simp
  ring

end Submission.SerreMean
