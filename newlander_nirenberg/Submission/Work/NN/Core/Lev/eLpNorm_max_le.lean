import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.volume_polydisc

namespace Work.NN.Core.Lev

open MeasureTheory
open scoped ENNReal

/-- Auxiliary form of `eLpNorm_max_le`, stated for an abstract pair of measures `μ' ≤ μ`
with `μ'` of finite total mass.  With `C₂ := √(μ' univ).toReal + 2` one bounds the
`L²`-norm of `max ‖u‖ Λ` against `μ'` by `C₂` times `(eLpNorm u 2 μ + ofReal Λ)`: the
pointwise inequality `max ‖u z‖ Λ ≤ ‖u z‖ + Λ`, the triangle inequality, and
`eLpNorm_le_of_ae_bound` for the constant function `Λ` (whose `L²`-norm is
`√(μ' univ) · Λ`). -/
lemma eLpNorm_max_bound {α : Type*} [MeasurableSpace α] {μ μ' : Measure α}
    (hle : μ' ≤ μ) {Λ : ℝ} (hΛ : 0 ≤ Λ) {u : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (hV : μ' Set.univ < ∞) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      eLpNorm (fun z => max ‖u z‖ Λ) 2 μ'
        ≤ ENNReal.ofReal C₂ * (eLpNorm u 2 μ + ENNReal.ofReal Λ) := by
  set C₂ : ℝ := Real.sqrt (μ' Set.univ).toReal + 2 with hC₂def
  have hC₂1 : (1 : ℝ) ≤ C₂ := by
    rw [hC₂def]; linarith [Real.sqrt_nonneg (μ' Set.univ).toReal]
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le one_pos hC₂1
  refine ⟨C₂, hC₂pos, ?_⟩
  have hu' : AEStronglyMeasurable u μ' := hu.mono_measure hle
  have hf : AEStronglyMeasurable (fun z => max ‖u z‖ Λ) μ' := by
    have h1 : AEMeasurable (fun z => ‖u z‖) μ' := (hu'.norm).aemeasurable
    have h2 : AEMeasurable (fun _ : α => Λ) μ' := measurable_const.aemeasurable
    exact (h1.max h2).aestronglyMeasurable
  have step1 : eLpNorm (fun z => max ‖u z‖ Λ) 2 μ' ≤ eLpNorm (fun z => ‖u z‖ + Λ) 2 μ' := by
    apply eLpNorm_mono hf
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _)),
      abs_of_nonneg (add_nonneg (norm_nonneg _) hΛ)]
    exact max_le (le_add_of_nonneg_right hΛ) (le_add_of_nonneg_left (norm_nonneg _))
  have step2 : eLpNorm (fun z => ‖u z‖ + Λ) 2 μ'
      ≤ eLpNorm (fun z => ‖u z‖) 2 μ' + eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' := by
    have h := eLpNorm_add_le (f := fun z => ‖u z‖) (g := fun _ : α => (Λ : ℝ)) (p := 2)
      (μ := μ') (by norm_num : (1 : ENNReal) ≤ 2)
    exact h
  have hA' : eLpNorm (fun z => ‖u z‖) 2 μ' = eLpNorm u 2 μ' := eLpNorm_norm u hu'
  have hA'mono : eLpNorm u 2 μ' ≤ eLpNorm u 2 μ := eLpNorm_mono_measure u hle
  have hH : eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' ≤ ENNReal.ofReal C₂ * ENNReal.ofReal Λ := by
    have hbound := eLpNorm_le_of_ae_bound (f := fun _ : α => (Λ : ℝ)) (C := Λ) (p := 2) (μ := μ')
      aestronglyMeasurable_const
      (Filter.Eventually.of_forall (fun x => by
        simp [Real.norm_eq_abs, abs_of_nonneg hΛ]))
    have hpow : μ' Set.univ ^ ((2 : ENNReal).toReal)⁻¹ ≤ ENNReal.ofReal C₂ := by
      have h2 : ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
      rw [h2, ← ENNReal.ofReal_toReal (ne_of_lt hV),
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.sqrt_eq_rpow]
      rw [hC₂def]; linarith
    calc eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ'
        ≤ μ' Set.univ ^ ((2 : ENNReal).toReal)⁻¹ * ENNReal.ofReal Λ := hbound
      _ ≤ ENNReal.ofReal C₂ * ENNReal.ofReal Λ := mul_le_mul' hpow le_rfl
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal C₂ := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hC₂1
  calc eLpNorm (fun z => max ‖u z‖ Λ) 2 μ'
      ≤ eLpNorm (fun z => ‖u z‖) 2 μ' + eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' :=
        le_trans step1 step2
    _ = eLpNorm u 2 μ' + eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' := by rw [hA']
    _ ≤ eLpNorm u 2 μ + ENNReal.ofReal C₂ * ENNReal.ofReal Λ := add_le_add hA'mono hH
    _ ≤ ENNReal.ofReal C₂ * eLpNorm u 2 μ + ENNReal.ofReal C₂ * ENNReal.ofReal Λ :=
        add_le_add (le_mul_of_one_le_left' hone) le_rfl
    _ = ENNReal.ofReal C₂ * (eLpNorm u 2 μ + ENNReal.ofReal Λ) := by rw [mul_add]

theorem eLpNorm_max_le {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ'ρ : ∀ j, ρ' j < ρ j) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) {u : Work.NN.Core.Cn n → ℂ}
    (hu : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      MeasureTheory.eLpNorm (fun z => max ‖u z‖ Λ) 2
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ'))
        ≤ ENNReal.ofReal C₂ *
          (MeasureTheory.eLpNorm u 2
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
            + ENNReal.ofReal Λ) := by
  have hsub : Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ'ρ j))
  have hle : MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ')
      ≤ MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ) :=
    MeasureTheory.Measure.restrict_mono hsub le_rfl
  have hV : (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ')) Set.univ < ∞ := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Work.NN.Core.volume_polydisc (0 : Fin n → ℂ) ρ']
    apply ENNReal.prod_lt_top
    intro j _
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  exact eLpNorm_max_bound hle hΛ hu hV

end Work.NN.Core.Lev
