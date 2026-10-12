import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxFrameDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.stronglyMeasurable_frameIntegrand`

The `q`-frame integrand `frameIntegrand volA Ac χ Ψ` (see `BoxFrameDefs`) is the sum of the
squares of the two genuine windowed-mode contents.  Here we record that its uncurrying
`(q, x) ↦ frameIntegrand volA Ac χ Ψ q x` is strongly measurable for a measurable box `Ac`,
a continuous window `χ` and a continuous trial state `Ψ`.

The proof is the standard parametric-integral measurability argument:

* `measurable_setIntegral_param` — `q ↦ ∫_{w∈A} ψ q w` is measurable for a jointly measurable
  `ψ`;
* `measurable_fibreMean_mul_param` — the slot integral
  `(q, x) ↦ ∫_{z∈A} h q z · Φ(x_{i←z}) dz` is measurable for jointly measurable `h` and
  measurable `Φ` (this is the parametric version of
  `Work.BoseFixB1.measurable_fibreMean_mul`);
* `measurable_boxWinModeReGen_uncurry`, `measurable_boxWinModeImGen_uncurry` — the windowed mode
  weights are jointly measurable in `(q, z)`, because `χ` is continuous and the fibre means
  `q ↦ ∫_{Ac} χ cos⟪q,·⟫` are measurable by the first item;
* `measurable_boxTauAnnGen_param` — assembling the slot sum.

The three hypotheses `ha`, `hvolpos`, `hAc` of the target are not needed for measurability and
play no role below.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Parametric integrals -/

/-- **Parametric set integral.**  If `ψ : α × E3 → ℝ` is jointly measurable and `A` is a
measurable set, then `q ↦ ∫_{w∈A} ψ q w` is measurable. -/
theorem measurable_setIntegral_param {α : Type*} [MeasurableSpace α] {A : Set E3}
    (hAm : MeasurableSet A) {ψ : α → E3 → ℝ} (hψ : Measurable (Function.uncurry ψ)) :
    Measurable (fun q : α => ∫ w in A, ψ q w) := by
  have huncurry : Measurable (Function.uncurry (fun (q : α) (w : E3) =>
      A.indicator (fun _ => (1 : ℝ)) w * ψ q w)) := by
    refine Measurable.mul ?_ hψ
    exact (measurable_const.indicator hAm).comp measurable_snd
  have hsm := StronglyMeasurable.integral_prod_right (ν := (volume : Measure E3))
      (f := fun (q : α) (w : E3) => A.indicator (fun _ => (1 : ℝ)) w * ψ q w)
      huncurry.stronglyMeasurable
  have hEq : (fun q : α => ∫ w, A.indicator (fun _ => (1 : ℝ)) w * ψ q w)
      = fun q : α => ∫ w in A, ψ q w := by
    funext q
    rw [← MeasureTheory.integral_indicator (μ := (volume : Measure E3)) hAm
      (f := fun w : E3 => ψ q w)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    by_cases hw : w ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hw]
  rw [hEq] at hsm
  exact hsm.measurable

/-- **Parametric fibre mean.**  If `h : α × E3 → ℝ` is jointly measurable and `Φ` is
measurable, then the slot integral `(q, x) ↦ ∫_{z∈A} h q z · Φ(x_{i←z}) dz` is measurable. -/
theorem measurable_fibreMean_mul_param {N : ℕ} {A : Set E3} (hAm : MeasurableSet A)
    {α : Type*} [MeasurableSpace α] (i : Fin N)
    {h : α → E3 → ℝ} (hhm : Measurable (Function.uncurry h))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) :
    Measurable (fun p : α × Submission.BoseGases.X N =>
      ∫ z in A, h p.1 z * Φ (Function.update p.2 i z)) := by
  have hproj : Measurable (fun p : (α × Submission.BoseGases.X N) × E3 =>
      (p.1.1, p.2)) := (measurable_fst.fst).prodMk measurable_snd
  have hproj2 : Measurable (fun p : (α × Submission.BoseGases.X N) × E3 =>
      (p.1.2, p.2)) := (measurable_fst.snd).prodMk measurable_snd
  have hupd : Measurable (fun q : Submission.BoseGases.X N × E3 =>
      Function.update q.1 i q.2) := (continuous_fst.update i continuous_snd).measurable
  have huncurry : Measurable (Function.uncurry (fun (p : α × Submission.BoseGases.X N)
      (z : E3) => A.indicator (fun _ => (1 : ℝ)) z * h p.1 z * Φ (Function.update p.2 i z))) := by
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact (measurable_const.indicator hAm).comp measurable_snd
    · exact hhm.comp hproj
    · exact hΦm.comp (hupd.comp hproj2)
  have hsm := StronglyMeasurable.integral_prod_right (ν := (volume : Measure E3))
      (f := fun (p : α × Submission.BoseGases.X N) (z : E3) =>
        A.indicator (fun _ => (1 : ℝ)) z * h p.1 z * Φ (Function.update p.2 i z))
      huncurry.stronglyMeasurable
  have hEq : (fun p : α × Submission.BoseGases.X N =>
        ∫ z, A.indicator (fun _ => (1 : ℝ)) z * h p.1 z * Φ (Function.update p.2 i z))
      = fun p : α × Submission.BoseGases.X N =>
          ∫ z in A, h p.1 z * Φ (Function.update p.2 i z) := by
    funext p
    rw [← MeasureTheory.integral_indicator (μ := (volume : Measure E3)) hAm
      (f := fun z : E3 => h p.1 z * Φ (Function.update p.2 i z))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    by_cases hz : z ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hEq] at hsm
  exact hsm.measurable

/-! ## Joint measurability of the windowed mode weights -/

/-- The genuine real part of the mean-free windowed mode is jointly measurable in `(q, z)`. -/
theorem measurable_boxWinModeReGen_uncurry {volA : ℝ} {A : Set E3} (hAm : MeasurableSet A)
    {χ : E3 → ℝ} (hχ : Continuous χ) :
    Measurable (Function.uncurry (boxWinModeReGen volA A χ)) := by
  have hcos : Measurable (fun q : E3 => ∫ w in A, χ w * Real.cos (inner ℝ q w)) :=
    measurable_setIntegral_param hAm
      ((hχ.comp continuous_snd).mul (Real.continuous_cos.comp continuous_inner)).measurable
  unfold boxWinModeReGen
  refine Measurable.mul ((measurable_const.indicator hAm).comp measurable_snd) ?_
  refine Measurable.sub ?_ ?_
  · exact ((hχ.comp continuous_snd).mul (Real.continuous_cos.comp continuous_inner)).measurable
  · exact measurable_const.mul (hcos.comp measurable_fst)

/-- The genuine imaginary part of the mean-free windowed mode is jointly measurable in `(q, z)`. -/
theorem measurable_boxWinModeImGen_uncurry {volA : ℝ} {A : Set E3} (hAm : MeasurableSet A)
    {χ : E3 → ℝ} (hχ : Continuous χ) :
    Measurable (Function.uncurry (boxWinModeImGen volA A χ)) := by
  have hsin : Measurable (fun q : E3 => ∫ w in A, χ w * Real.sin (inner ℝ q w)) :=
    measurable_setIntegral_param hAm
      ((hχ.comp continuous_snd).mul (Real.continuous_sin.comp continuous_inner)).measurable
  unfold boxWinModeImGen
  refine Measurable.neg ?_
  refine Measurable.mul ((measurable_const.indicator hAm).comp measurable_snd) ?_
  refine Measurable.sub ?_ ?_
  · exact ((hχ.comp continuous_snd).mul (Real.continuous_sin.comp continuous_inner)).measurable
  · exact measurable_const.mul (hsin.comp measurable_fst)

/-! ## The parametric one-slot sum -/

/-- `(q, x) ↦ boxTauAnnGen volA A (g q) Ψ x` is measurable whenever the weights `g` are jointly
measurable and `Ψ` is measurable. -/
theorem measurable_boxTauAnnGen_param {N : ℕ} (volA : ℝ) {A : Set E3} (hAm : MeasurableSet A)
    {α : Type*} [MeasurableSpace α] {g : α → E3 → ℝ} (hgm : Measurable (Function.uncurry g))
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) :
    Measurable (fun p : α × Submission.BoseGases.X N => boxTauAnnGen volA A (g p.1) Ψ p.2) := by
  have hsum : Measurable (fun p : α × Submission.BoseGases.X N =>
      ∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (p.2 i)
        * ∫ z in A, g p.1 z * Ψ (Function.update p.2 i z)) := by
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator hAm).comp ((measurable_pi_apply i).comp measurable_snd)
    · exact measurable_fibreMean_mul_param hAm i hgm hΨm
  have hgoal : (fun p : α × Submission.BoseGases.X N => boxTauAnnGen volA A (g p.1) Ψ p.2)
      = fun p : α × Submission.BoseGases.X N =>
          (Real.sqrt volA)⁻¹ * ∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (p.2 i)
            * ∫ z in A, g p.1 z * Ψ (Function.update p.2 i z) := rfl
  rw [hgoal]
  exact hsum.const_mul _

/-! ## The frame integrand -/

theorem stronglyMeasurable_frameIntegrand {N : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    MeasureTheory.StronglyMeasurable
      (Function.uncurry (Work.BoseFixB1.frameIntegrand volA Ac χ Ψ)) := by
  have hRe : Measurable (fun p : E3 × Submission.BoseGases.X (N + 1) =>
      boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ p.1) Ψ p.2) :=
    measurable_boxTauAnnGen_param volA hAcm
      (measurable_boxWinModeReGen_uncurry (volA := volA) hAcm hχc) hΨ.measurable
  have hIm : Measurable (fun p : E3 × Submission.BoseGases.X (N + 1) =>
      boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ p.1) Ψ p.2) :=
    measurable_boxTauAnnGen_param volA hAcm
      (measurable_boxWinModeImGen_uncurry (volA := volA) hAcm hχc) hΨ.measurable
  apply Measurable.stronglyMeasurable
  have hgoal : (Function.uncurry (frameIntegrand volA Ac χ Ψ))
      = fun p : E3 × Submission.BoseGases.X (N + 1) =>
          (boxTauAnnGen volA Ac (boxWinModeReGen volA Ac χ p.1) Ψ p.2) ^ 2
            + (boxTauAnnGen volA Ac (boxWinModeImGen volA Ac χ p.1) Ψ p.2) ^ 2 := rfl
  rw [hgoal]
  exact (hRe.pow_const 2).add (hIm.pow_const 2)

end Work.BoseFixB1
