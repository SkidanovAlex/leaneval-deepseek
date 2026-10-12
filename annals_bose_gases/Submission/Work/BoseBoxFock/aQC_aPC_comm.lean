import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3Defs
import Submission.Work.BoseBoxFock.aPCPairAlg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aQC_aPC_comm`

The slot mean `aPC ℓ i` (the cube average of the state with the slot `i` replaced,
`aPC ℓ i Θ x = ℓ⁻³ ∫_{acube ℓ} Θ (x[i↦y]) dy`) and the complementary slot
`aQC ℓ j = 1 − aPC ℓ j` commute across *different* slots `i ≠ j`:

    `aQC ℓ j (aPC ℓ i Θ) = aPC ℓ i (aQC ℓ j Θ)`   (`i ≠ j`),

i.e. the two slot projections `P_i = aPC ℓ i` and `Q_j = aQC ℓ j` of FS's pair decomposition
commute (they act on different coordinates: the `i ≠ j` rows of the standard projection
algebra).

The proof has three ingredients, isolated below.

* **Integrability.**  A state `Θ` that is measurable and *everywhere* bounded by `C` has all
  its slot pullbacks integrable on the cube `acube ℓ`, and so do the pullbacks of the slot
  means `aPC ℓ j Θ` (`aPC_integrableOn_comp_update`, `aPC_integrableOn_aPC_comp_update`).
  This is what makes every Bochner integral below a genuine one, so no junk value arises.
  The slot-mean case goes through a *partial* Bochner integral
  (`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`), since `aPC ℓ j Θ` is itself an
  integral and hence only a.e. strongly measurable
  (`aPC_aesm_comp_update`).
* **Linearity.**  `aPC ℓ i` is additive, so it turns `aQC ℓ j Θ = Θ − aPC ℓ j Θ` into the
  difference of the two slot means (`aPC_sub_of_integrableOn`).
* **Fubini.**  For `i ≠ j` the two double cube integrals `∫_y∫_z Θ (x[j↦y][i↦z])` and
  `∫_z∫_y Θ (x[i↦z][j↦y])` coincide: the two coordinate updates commute
  (`Function.update_comm`) and the order of integration can be exchanged
  (`MeasureTheory.integral_integral_swap`) because the integrand is measurable and bounded on
  the square (`aPC_aPC_comm_of_bounded`).
-/

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Integrability of slot pullbacks of bounded measurable states -/

/-- **A measurable, everywhere bounded state has integrable slot pullbacks.**  For `x : X n`
and a slot `i`, the function `y ↦ Θ (x[i↦y])` is a.e. strongly measurable and bounded by `C`
on the cube `acube ℓ`, which has finite measure. -/
theorem aPC_integrableOn_comp_update {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ) {C : ℝ}
    (hC : ∀ x, ‖Θ x‖ ≤ C) (x : Submission.BoseGases.X n) :
    IntegrableOn (fun y : Sp => Θ (Function.update x i y))
      (Submission.BoseGases.acube ℓ) := by
  haveI : IsFiniteMeasure ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (by
      rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top)
  refine MeasureTheory.Integrable.of_bound ?_ C ?_
  · exact (hΘm.aestronglyMeasurable.comp_measurable
      ((Continuous.update (f := fun _ : Sp => x) continuous_const i continuous_id).measurable)
      ).restrict
  · exact Filter.Eventually.of_forall fun y => hC _

/-- **A slot pullback of a slot mean is a.e. strongly measurable.**  For a measurable state
`Θ`, the function `y ↦ aPC ℓ j Θ (x[i↦y])` is, up to the constant `ℓ⁻³`, the partial Bochner
integral of the jointly measurable, everywhere bounded function
`(y, w) ↦ Θ (x[i↦y][j↦w])` over the cube; `integral_prod_right'` is the Fubini measurability
statement that applies to such a partial integral. -/
theorem aPC_aesm_comp_update {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ) (x : Submission.BoseGases.X n) :
    AEStronglyMeasurable (fun y : Sp => aPC ℓ j Θ (Function.update x i y))
      ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) := by
  haveI : IsFiniteMeasure ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (by
      rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top)
  have hcont : Continuous (fun p : Sp × Sp => Function.update (Function.update x i p.1) j p.2) := by
    apply Continuous.update (f := fun p : Sp × Sp => Function.update x i p.1)
    · exact Continuous.update (f := fun _ : Sp × Sp => x) continuous_const i continuous_fst
    · exact continuous_snd
  have hjoint : AEStronglyMeasurable
      (fun p : Sp × Sp => Θ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))) :=
    (hΘm.comp hcont.measurable).aestronglyMeasurable
  have hpi : AEStronglyMeasurable
      (fun y : Sp => ∫ w : Sp, Θ (Function.update (Function.update x i y) j w)
        ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)))
      ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
    hjoint.integral_prod_right'
  refine (hpi.const_mul (((1 / ℓ ^ 3 : ℝ) : ℂ))).congr ?_
  filter_upwards with y
  exact rfl

/-- **A slot pullback of a slot mean is integrable**: it is a.e. strongly measurable
(`aPC_aesm_comp_update`) and everywhere bounded by the bound of the state (`norm_aPC_le`), on
a cube of finite measure. -/
theorem aPC_integrableOn_aPC_comp_update {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖Θ x‖ ≤ C) (x : Submission.BoseGases.X n) :
    IntegrableOn (fun y : Sp => aPC ℓ j Θ (Function.update x i y))
      (Submission.BoseGases.acube ℓ) := by
  haveI : IsFiniteMeasure ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (by
      rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top)
  exact MeasureTheory.Integrable.of_bound (aPC_aesm_comp_update hℓ i j hΘm x) C
    (Filter.Eventually.of_forall fun y => norm_aPC_le hℓ j hC0 hC _)

/-! ## 2. Linearity of the slot mean on a difference -/

/-- **`aPC ℓ i` is additive on a difference**: `aPC ℓ i (Ψ − Φ) = aPC ℓ i Ψ − aPC ℓ i Φ`
pointwise, with the integrability of the two pullbacks carried as hypotheses (the Bochner
integral is only additive for integrable functions). -/
theorem aPC_sub_of_integrableOn {n : ℕ} {ℓ : ℝ} (i : Fin n)
    (Ψ Φ : Submission.BoseGases.X n → ℂ) (x : Submission.BoseGases.X n)
    (hΨ : IntegrableOn (fun y : Sp => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ))
    (hΦ : IntegrableOn (fun y : Sp => Φ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    aPC ℓ i (Ψ - Φ) x = aPC ℓ i Ψ x - aPC ℓ i Φ x := by
  unfold aPC
  simp only [Pi.sub_apply]
  rw [MeasureTheory.integral_sub hΨ hΦ]
  ring

/-! ## 3. The two slot means commute (Fubini on the square `acube ℓ × acube ℓ`) -/

/-- **The slot means of two different slots commute**: for `i ≠ j` and a measurable state that
is everywhere bounded,

    `aPC ℓ j (aPC ℓ i Θ) = aPC ℓ i (aPC ℓ j Θ)`.

Both sides are `(ℓ⁻³)²` times `∫_y ∫_z Θ (x[j↦y][i↦z])` read in the two possible orders; the
integrand is bounded by `C` and measurable on the square, so the order of integration may be
exchanged (`MeasureTheory.integral_integral_swap`), and the two coordinate updates commute
because `i ≠ j` (`Function.update_comm`). -/
theorem aPC_aPC_comm_of_bounded {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    aPC ℓ j (aPC ℓ i Θ) = aPC ℓ i (aPC ℓ j Θ) := by
  obtain ⟨C, hC⟩ := hΘb
  haveI : IsFiniteMeasure ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (by
      rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_ne_top)
  funext x
  -- the update map `(y, z) ↦ x[j↦y][i↦z]` is continuous, hence the integrand is measurable
  have hcont : Continuous (fun p : Sp × Sp => Function.update (Function.update x j p.1) i p.2) := by
    apply Continuous.update (f := fun p : Sp × Sp => Function.update x j p.1)
    · exact Continuous.update (f := fun _ : Sp × Sp => x) continuous_const j continuous_fst
    · exact continuous_snd
  have hGsm : AEStronglyMeasurable
      (fun p : Sp × Sp => Θ (Function.update (Function.update x j p.1) i p.2))
      (((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))) :=
    (hΘm.comp hcont.measurable).aestronglyMeasurable
  have hGint : Integrable
      (fun p : Sp × Sp => Θ (Function.update (Function.update x j p.1) i p.2))
      (((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))) :=
    MeasureTheory.Integrable.of_bound hGsm C (Filter.Eventually.of_forall fun p => hC _)
  have hswap : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        Θ (Function.update (Function.update x j y) i z))
      = (∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        Θ (Function.update (Function.update x j y) i z)) :=
    MeasureTheory.integral_integral_swap
      (μ := (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))
      (ν := (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) hGint
  -- the two sides, with the constant `ℓ⁻³` moved out of the two integrals
  have hL : aPC ℓ j (aPC ℓ i Θ) x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (((1 / ℓ ^ 3 : ℝ) : ℂ) *
          ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            Θ (Function.update (Function.update x j y) i z)) := by
    unfold aPC
    rw [MeasureTheory.integral_const_mul]
  have hR : aPC ℓ i (aPC ℓ j Θ) x
      = ((1 / ℓ ^ 3 : ℝ) : ℂ) * (((1 / ℓ ^ 3 : ℝ) : ℂ) *
          ∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ,
            Θ (Function.update (Function.update x i z) j y)) := by
    unfold aPC
    rw [MeasureTheory.integral_const_mul]
  -- the two coordinate updates commute because `i ≠ j`
  have hpt : ∀ y z : Sp, Θ (Function.update (Function.update x j y) i z)
      = Θ (Function.update (Function.update x i z) j y) := by
    intro y z
    rw [Function.update_comm (a := j) (b := i) (Ne.symm hij) y z x]
  have hdouble : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        Θ (Function.update (Function.update x j y) i z))
      = (∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        Θ (Function.update (Function.update x i z) j y)) := by
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hpt y z)
  rw [hL, hR, hdouble]

/-! ## 4. The commutation of `aQC` with the slot mean of a different slot -/

theorem aQC_aPC_comm {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseBoxFock.aQC ℓ j (Work.BoseBoxFock.aPC ℓ i Θ)
      = Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.aQC ℓ j Θ) := by
  obtain ⟨C, hC⟩ := hΘb
  have hcomm := aPC_aPC_comm_of_bounded hℓ hij hΘm ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC fun _ => 0)
  funext x
  -- the two integrability inputs of the linearity of `aPC ℓ i`
  have hle : IntegrableOn (fun y : Sp => Θ (Function.update x i y))
      (Submission.BoseGases.acube ℓ) :=
    aPC_integrableOn_comp_update hℓ i hΘm hC x
  have hle2 : IntegrableOn (fun y : Sp => aPC ℓ j Θ (Function.update x i y))
      (Submission.BoseGases.acube ℓ) :=
    aPC_integrableOn_aPC_comp_update hℓ i j hΘm hC0 hC x
  have hsub := aPC_sub_of_integrableOn i Θ (aPC ℓ j Θ) x hle hle2
  calc aQC ℓ j (aPC ℓ i Θ) x
      = aPC ℓ i Θ x - aPC ℓ j (aPC ℓ i Θ) x := rfl
    _ = aPC ℓ i Θ x - aPC ℓ i (aPC ℓ j Θ) x := by rw [congrFun hcomm x]
    _ = aPC ℓ i (aQC ℓ j Θ) x := hsub.symm

end Work.BoseBoxFock
