import Mathlib
import Submission.Work.EKLC6Core.HaarSetup

/-!
# Conjugation scaling of Haar measure on a normalised closed subgroup of `SL₃(ℝ)`

Let `H ≤ SL₃(ℝ)` be a closed subgroup and `a ∈ SL₃(ℝ)` an element normalising it, i.e.
`a H a⁻¹ ⊆ H` and `a⁻¹ H a ⊆ H` (hypotheses `hn`, `hn'`).  Then conjugation by `a` restricts to a
topological group automorphism `Ψ` of `H`; the push-forward of a Haar measure `μ` on `H` by
`Ψ⁻¹` is again a Haar measure, hence a scalar multiple `c • μ` of `μ` by uniqueness of Haar
measure in a second countable locally compact group.  Reading this identity at the level of the
ambient group — the inclusion `H ↪ SL₃(ℝ)` intertwines `Ψ⁻¹` with conjugation by `a` — gives the
stated scaling of the push-forward `μ.map Subtype.val` under the map `g ↦ a g a⁻¹`.

This is the "general closed subgroup" version of `haar_uminus_scaling_full`, which treats the
horospherical subgroup `U⁻(t)`.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem haar_conj_scaling {H : Subgroup Work.EKLContract.SL3}
    (hH : IsClosed (H : Set Work.EKLContract.SL3)) (a : Work.EKLContract.SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H)
    (μ : MeasureTheory.Measure H) [MeasureTheory.Measure.IsHaarMeasure μ] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ s : Set Work.EKLContract.SL3, s ⊆ (H : Set Work.EKLContract.SL3) → MeasurableSet s →
        (μ.map (Subtype.val : H → Work.EKLContract.SL3))
            ((fun g : Work.EKLContract.SL3 => a * g * a⁻¹) '' s)
          = c * (μ.map (Subtype.val : H → Work.EKLContract.SL3)) s := by
  -- ## The closed subgroup `H` is locally compact and second countable
  haveI hLC : LocallyCompactSpace H := subgroup_locallyCompactSpace hH
  haveI hSC : SecondCountableTopology H := subgroup_secondCountableTopology hH
  -- ## Conjugation by `a` as a topological group automorphism of `H`
  let Ψ : H ≃ₜ* H := conjContinuousMulEquiv H a hn hn'
  have hΨsymm : ⇑(Ψ.symm) = (fun h : H => (⟨a⁻¹ * (h : SL3) * a, hn' h h.2⟩ : H)) := by
    funext h; rfl
  -- ## Uniqueness of Haar measure: the push-forward by `Ψ⁻¹` is a scalar multiple of `μ`
  haveI hν : (μ.map (⇑Ψ.symm)).IsHaarMeasure := inferInstance
  let c₀ : NNReal := (μ.map (⇑Ψ.symm)).haarScalarFactor μ
  have hc₀pos : 0 < c₀ :=
    Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map (⇑Ψ.symm)) μ
  have hEq : μ.map (⇑Ψ.symm) = c₀ • μ :=
    Measure.isMulLeftInvariant_eq_smul (μ.map (⇑Ψ.symm)) μ
  refine ⟨(c₀ : ENNReal), ENNReal.coe_ne_zero.mpr hc₀pos.ne', ENNReal.coe_ne_top, ?_⟩
  intro s _hsH hsm
  have hmeasVal : Measurable (Subtype.val : H → SL3) := continuous_subtype_val.measurable
  have hmeasΨ : Measurable (⇑Ψ.symm) := Ψ.symm.continuous.measurable
  have hconjm : MeasurableSet ((fun g : SL3 => a * g * a⁻¹) '' s) :=
    measurableSet_conjImage a hsm
  -- the preimage of the conjugated set under the inclusion is the preimage under `Ψ⁻¹`
  have hpre : Subtype.val ⁻¹' ((fun g : SL3 => a * g * a⁻¹) '' s)
      = ⇑Ψ.symm ⁻¹' (Subtype.val ⁻¹' s) := by
    rw [hΨsymm]
    exact subtype_preimage_conj_image H a hn hn' s
  have hsm' : MeasurableSet (Subtype.val ⁻¹' s) := hmeasVal hsm
  calc (μ.map (Subtype.val : H → SL3)) ((fun g : SL3 => a * g * a⁻¹) '' s)
      = μ (Subtype.val ⁻¹' ((fun g : SL3 => a * g * a⁻¹) '' s)) :=
        Measure.map_apply hmeasVal hconjm
    _ = μ (⇑Ψ.symm ⁻¹' (Subtype.val ⁻¹' s)) := by rw [hpre]
    _ = (μ.map (⇑Ψ.symm)) (Subtype.val ⁻¹' s) := (Measure.map_apply hmeasΨ hsm').symm
    _ = (c₀ • μ) (Subtype.val ⁻¹' s) := by rw [hEq]
    _ = (c₀ : ENNReal) * μ (Subtype.val ⁻¹' s) := by
        rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    _ = (c₀ : ENNReal) * (μ.map (Subtype.val : H → SL3)) s := by
        rw [Measure.map_apply hmeasVal hsm]

end Work.EKLC6Core
