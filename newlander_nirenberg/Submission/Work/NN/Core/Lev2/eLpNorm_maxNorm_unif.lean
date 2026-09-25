import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.volume_polydisc
import Submission.Work.NN.Core.Lev.eLpNorm_max_le

namespace Work.NN.Core.Lev2

open MeasureTheory
open scoped ENNReal

/-- **Uniform form of the `max`-truncation estimate.**  For an abstract pair of measures `μ' ≤ μ`
with `μ'` of finite total mass, the constant `C := √(μ' univ).toReal + 2` — which depends only on
the measure `μ'`, not on `Λ` or on `u` — bounds the `L²`-norm of `max ‖u‖ Λ` against `μ'` by `C`
times `(eLpNorm u 2 μ + ofReal Λ)`.

This is the same estimate as `Work.NN.Core.Lev.eLpNorm_max_le`, but with the witness pulled out of
the `Λ`/`u` quantifiers: the chain of inequalities only ever uses the finiteness of `μ' univ`, and
the optimal constant `√(μ' univ)` is intrinsic to `μ'`. -/
lemma eLpNorm_max_bound_unif {α : Type*} [MeasurableSpace α] {μ μ' : Measure α}
    (hle : μ' ≤ μ) (hV : μ' Set.univ < ∞) :
    ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {u : α → ℂ}, AEStronglyMeasurable u μ →
      eLpNorm (fun z => max ‖u z‖ Λ) 2 μ'
        ≤ ENNReal.ofReal (Real.sqrt (μ' Set.univ).toReal + 2) *
          (eLpNorm u 2 μ + ENNReal.ofReal Λ) := by
  intro Λ hΛ u hu
  set C : ℝ := Real.sqrt (μ' Set.univ).toReal + 2 with hCdef
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]; linarith [Real.sqrt_nonneg (μ' Set.univ).toReal]
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
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
  have hH : eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' ≤ ENNReal.ofReal C * ENNReal.ofReal Λ := by
    have hbound := eLpNorm_le_of_ae_bound (f := fun _ : α => (Λ : ℝ)) (C := Λ) (p := 2) (μ := μ')
      aestronglyMeasurable_const
      (Filter.Eventually.of_forall (fun x => by
        simp [Real.norm_eq_abs, abs_of_nonneg hΛ]))
    have hpow : μ' Set.univ ^ ((2 : ENNReal).toReal)⁻¹ ≤ ENNReal.ofReal C := by
      have h2 : ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
      rw [h2, ← ENNReal.ofReal_toReal (ne_of_lt hV),
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.sqrt_eq_rpow]
      rw [hCdef]; linarith
    calc eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ'
        ≤ μ' Set.univ ^ ((2 : ENNReal).toReal)⁻¹ * ENNReal.ofReal Λ := hbound
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal Λ := mul_le_mul' hpow le_rfl
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hC1
  calc eLpNorm (fun z => max ‖u z‖ Λ) 2 μ'
      ≤ eLpNorm (fun z => ‖u z‖) 2 μ' + eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' :=
        le_trans step1 step2
    _ = eLpNorm u 2 μ' + eLpNorm (fun _ : α => (Λ : ℝ)) 2 μ' := by rw [hA']
    _ ≤ eLpNorm u 2 μ + ENNReal.ofReal C * ENNReal.ofReal Λ := add_le_add hA'mono hH
    _ ≤ ENNReal.ofReal C * eLpNorm u 2 μ + ENNReal.ofReal C * ENNReal.ofReal Λ :=
        add_le_add (le_mul_of_one_le_left' hone) le_rfl
    _ = ENNReal.ofReal C * (eLpNorm u 2 μ + ENNReal.ofReal Λ) := by rw [mul_add]

/-- **Uniform `L²` estimate for the truncated modulus.**  The `L²`-norm over the smaller polydisc
`polydisc 0 ρ'` of `max ‖u‖ Λ` is bounded by a constant `C₂`, *depending only on `ρ'`* (and
hence uniform in `Λ ≥ 0` and in the function `u`), times
`eLpNorm u 2 (volume.restrict (polydisc 0 ρ)) + ofReal Λ`.

The proof takes `C₂ := √((volume.restrict (polydisc 0 ρ')) univ).toReal + 2`, the intrinsic
constant of the (finite) measure `volume.restrict (polydisc 0 ρ')`, and applies
`eLpNorm_max_bound_unif` with `μ := volume.restrict (polydisc 0 ρ)`. -/
theorem eLpNorm_maxNorm_unif {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ'ρ : ∀ j, ρ' j < ρ j) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {u : Work.NN.Core.Cn n → ℂ},
        MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) →
        MeasureTheory.eLpNorm (fun z => max ‖u z‖ Λ) 2
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ'))
          ≤ ENNReal.ofReal C₂ *
            (MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
              + ENNReal.ofReal Λ) := by
  have hsub : Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ'ρ j))
  have hle : MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ')
      ≤ MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ) :=
    MeasureTheory.Measure.restrict_mono hsub le_rfl
  have hV : (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ')) Set.univ
      < ∞ := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Work.NN.Core.volume_polydisc (0 : Fin n → ℂ) ρ']
    apply ENNReal.prod_lt_top
    intro j _
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  refine ⟨Real.sqrt
      ((MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ')) Set.univ).toReal
      + 2, ?_, ?_⟩
  · linarith [Real.sqrt_nonneg
      ((MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ')) Set.univ).toReal]
  · intro Λ hΛ u hu
    exact eLpNorm_max_bound_unif hle hV hΛ hu

end Work.NN.Core.Lev2
