import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxOpA
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxTauGenMeasToolbox` — measurability/boundedness for the box one-slot
operators at **merely measurable** weights

The corpus lemmas for `Work.BoseFixB1.boxOpG A f h` / `boxOpZ A f h` (adjointness, commutator,
positivity) are stated for *continuous* slot weights `f`, `h`, which is more than is needed.  The
Bogoliubov bound `Work.BoseFixB1.boxTauGen_mode_bound_meas` needs them for weights that are only
a.e. measurable and bounded with support in the box, so this module collects the elementary
measurability/integrability facts in that generality.

Main items:

* `update_mem_abox_toolbox` — inserting a point of `A ⊆ acube ℓ` into a slot stays in the box;
* `measurable_fibreMean_mul` — `x ↦ ∫_{z∈A} h z · Φ(x|i↦z) dz` is measurable for measurable
  `h`, `Φ`;
* `abs_fibreMean_mul_le` — the same fibre mean is bounded by `max Ch 0·max CΦ 0·|A|` on the box;
* `setIntegral_acube_eq_of_vanishes_off` — `∫_{acube ℓ} h·φ = ∫_A h·φ` for `h` vanishing off
  `A ⊆ acube ℓ`;
* `integrableOn_boxOpG_slot` — integrability of the one-slot integrand on the box;
* `measurable_boxOpG_toolbox`, `measurable_boxOpZ_toolbox` — measurability of `boxOpG`/`boxOpZ`;
* `abs_boxOpG_le_toolbox`, `abs_boxOpZ_le_toolbox` — boundedness of `boxOpG`/`boxOpZ` on the box.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Inserting a point of `A ⊆ acube ℓ` into one slot keeps a box configuration in the box. -/
theorem update_mem_abox_toolbox {n : ℕ} {ℓ : ℝ} {A : Set E3} (hAc : A ⊆ acube ℓ)
    {x : X n} (hx : x ∈ abox n ℓ) (i : Fin n) {u : E3} (hu : u ∈ A) :
    Function.update x i u ∈ abox n ℓ := by
  intro k
  rw [Function.update_apply]
  by_cases hk : k = i
  · rw [if_pos hk]; exact hAc hu
  · rw [if_neg hk]; exact hx k

/-! ## 1. The fibre mean with a `z`-dependent weight -/

theorem measurable_fibreMean_mul {N : ℕ} {A : Set E3} (hAm : MeasurableSet A) (i : Fin N)
    {h : E3 → ℝ} (hhm : Measurable h) {Φ : X N → ℝ} (hΦm : Measurable Φ) :
    Measurable (fun x : X N => ∫ z in A, h z * Φ (Function.update x i z)) := by
  have huncurry : Measurable (Function.uncurry (fun (x : X N) (z : E3) =>
      A.indicator (fun _ => (1 : ℝ)) z * h z * Φ (Function.update x i z))) := by
    refine Measurable.mul ?_ ?_
    · exact ((measurable_const.indicator hAm).comp measurable_snd).mul (hhm.comp measurable_snd)
    · exact hΦm.comp (continuous_fst.update i continuous_snd).measurable
  have hsm := StronglyMeasurable.integral_prod_right (ν := (volume : Measure E3))
      (f := fun (x : X N) (z : E3) =>
        A.indicator (fun _ => (1 : ℝ)) z * h z * Φ (Function.update x i z))
      huncurry.stronglyMeasurable
  have hEq : (fun x : X N =>
        ∫ z, A.indicator (fun _ => (1 : ℝ)) z * h z * Φ (Function.update x i z))
      = fun x : X N => ∫ z in A, h z * Φ (Function.update x i z) := by
    funext x
    rw [← MeasureTheory.integral_indicator (μ := (volume : Measure E3)) hAm
      (f := fun z : E3 => h z * Φ (Function.update x i z))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    by_cases hz : z ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hEq] at hsm
  exact hsm.measurable

/-- The fibre mean of a bounded weight is bounded on the box by `max Ch 0·max CΦ 0·|A|`. -/
theorem abs_fibreMean_mul_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hAc : A ⊆ acube ℓ)
    {h : E3 → ℝ} {Ch : ℝ} (hhb : ∀ z, |h z| ≤ Ch)
    {Φ : X N → ℝ} {CΦ : ℝ} (hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ CΦ)
    {x : X N} (hx : x ∈ abox N ℓ) (i : Fin N) :
    |∫ z in A, h z * Φ (Function.update x i z)| ≤ max Ch 0 * max CΦ 0 * (volume A).toReal := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hb : ∀ z ∈ A, ‖h z * Φ (Function.update x i z)‖ ≤ max Ch 0 * max CΦ 0 := by
    intro z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (le_trans (hhb z) (le_max_left _ _))
      (le_trans (hΦb _ (update_mem_abox_toolbox hAc hx i hz)) (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3)) (s := A)
    (f := fun z : E3 => h z * Φ (Function.update x i z)) (C := max Ch 0 * max CΦ 0) hfin hb
  rwa [Real.norm_eq_abs, MeasureTheory.Measure.real] at h

/-! ## 2. Localisation of a cube integral to `A` -/

/-- `∫_{acube ℓ} h·φ = ∫_A h·φ` when `h` vanishes off `A ⊆ acube ℓ`. -/
theorem setIntegral_acube_eq_of_vanishes_off {ℓ : ℝ} {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {h : E3 → ℝ} (h0 : ∀ z, z ∉ A → h z = 0) (φ : E3 → ℝ) :
    (∫ y in acube ℓ, h y * φ y) = ∫ y in A, h y * φ y := by
  have hpt : ∀ y, (acube ℓ).indicator (fun y => h y * φ y) y
      = A.indicator (fun y => h y * φ y) y := by
    intro y
    by_cases hyA : y ∈ A
    · have hyc : y ∈ acube ℓ := hAc hyA
      rw [Set.indicator_of_mem hyc, Set.indicator_of_mem hyA]
    · by_cases hyc : y ∈ acube ℓ
      · rw [Set.indicator_of_mem hyc, Set.indicator_of_notMem hyA, h0 y hyA, zero_mul]
      · rw [Set.indicator_of_notMem hyc, Set.indicator_of_notMem (fun hh => hyc (hAc hh))]
  calc (∫ y in acube ℓ, h y * φ y)
      = ∫ y, (acube ℓ).indicator (fun y => h y * φ y) y :=
        (MeasureTheory.integral_indicator (μ := (volume : Measure E3))
          (f := fun y => h y * φ y) (acube_measurable ℓ)).symm
    _ = ∫ y, A.indicator (fun y => h y * φ y) y := by
        rw [show (fun y => (acube ℓ).indicator (fun y => h y * φ y) y)
            = (fun y => A.indicator (fun y => h y * φ y) y) from funext hpt]
    _ = ∫ y in A, h y * φ y :=
        MeasureTheory.integral_indicator (μ := (volume : Measure E3))
          (f := fun y => h y * φ y) hAm

/-! ## 3. Integrability of the one-slot integrand -/

theorem integrableOn_boxOpG_slot {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hAm : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {f h : E3 → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    {Cf Ch : ℝ} (hfw : ∀ z, |f z| ≤ Cf) (hhw : ∀ z, |h z| ≤ Ch)
    {Ψ : X (N + 1) → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ abox (N + 1) ℓ, |Ψ x| ≤ CΨ) (i : Fin (N + 1)) :
    IntegrableOn (fun x : X (N + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
          * ∫ z in A, h z * Ψ (Function.update x i z)) (abox (N + 1) ℓ) volume := by
  have hfib : ∀ x ∈ abox (N + 1) ℓ, |∫ z in A, h z * Ψ (Function.update x i z)|
      ≤ max Ch 0 * max CΨ 0 * (volume A).toReal :=
    fun x hx => abs_fibreMean_mul_le hℓ hAc hhw hΨb hx i
  refine Work.BoseFixB1S.integrableOn_mul_of_bound hℓ ?_
    (measurable_fibreMean_mul hAm i hhm hΨm)
    (Cf := max Cf 0) (Cg := max Ch 0 * max CΨ 0 * (volume A).toReal) ?_ hfib
  · exact ((measurable_const.indicator hAm).comp (measurable_pi_apply i)).mul
      (hfm.comp (measurable_pi_apply i))
  · intro x hx
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    rw [abs_mul]
    simpa using mul_le_mul h1 (le_trans (hfw (x i)) (le_max_left Cf (0:ℝ)))
      (abs_nonneg _) zero_le_one

/-! ## 4. Measurability and boundedness of `boxOpG` / `boxOpZ` -/

theorem measurable_boxOpG_toolbox {N : ℕ} {A : Set E3} (hAm : MeasurableSet A)
    {f h : E3 → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ) :
    Measurable (boxOpG A f h Ψ) := by
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (((measurable_const.indicator hAm).comp (measurable_pi_apply i)).mul
    (hfm.comp (measurable_pi_apply i))).mul (measurable_fibreMean_mul hAm i hhm hΨm)

theorem measurable_boxOpZ_toolbox {N : ℕ} {A : Set E3} (hAm : MeasurableSet A)
    {f h : E3 → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ) :
    Measurable (boxOpZ A f h Ψ) := by
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (hfm.comp (measurable_pi_apply i)).mul (measurable_fibreMean_mul hAm i hhm hΨm)

theorem abs_boxOpG_le_toolbox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {f h : E3 → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    {Cf Ch : ℝ} (hfw : ∀ z, |f z| ≤ Cf) (hhw : ∀ z, |h z| ≤ Ch)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ CΨ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |boxOpG A f h Ψ x| ≤ C := by
  refine ⟨(N : ℝ) * (max Cf 0 * (max Ch 0 * max CΨ 0 * (volume A).toReal)),
    mul_nonneg (Nat.cast_nonneg N) (by positivity), fun x hx => ?_⟩
  calc |boxOpG A f h Ψ x|
      = |∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
            * ∫ z in A, h z * Ψ (Function.update x i z)| := rfl
    _ ≤ ∑ i : Fin N, |A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
            * ∫ z in A, h z * Ψ (Function.update x i z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (max Cf 0 * (max Ch 0 * max CΨ 0 * (volume A).toReal)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
          by_cases hxi : x i ∈ A <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
        have h2 : |∫ z in A, h z * Ψ (Function.update x i z)|
            ≤ max Ch 0 * max CΨ 0 * (volume A).toReal :=
          abs_fibreMean_mul_le hℓ hAc hhw hΨb hx i
        rw [abs_mul, abs_mul]
        have h3 : |A.indicator (fun _ => (1 : ℝ)) (x i)| * |f (x i)| ≤ max Cf 0 := by
          simpa using mul_le_mul h1 (le_trans (hfw (x i)) (le_max_left Cf (0:ℝ)))
            (abs_nonneg _) zero_le_one
        exact mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
    _ = (N : ℝ) * (max Cf 0 * (max Ch 0 * max CΨ 0 * (volume A).toReal)) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

theorem abs_boxOpZ_le_toolbox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {f h : E3 → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    {Cf Ch : ℝ} (hfw : ∀ z, |f z| ≤ Cf) (hhw : ∀ z, |h z| ≤ Ch)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ CΨ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |boxOpZ A f h Ψ x| ≤ C := by
  refine ⟨(N : ℝ) * (max Cf 0 * (max Ch 0 * max CΨ 0 * (volume A).toReal)),
    mul_nonneg (Nat.cast_nonneg N) (by positivity), fun x hx => ?_⟩
  calc |boxOpZ A f h Ψ x|
      = |∑ i : Fin N, f (x i) * ∫ z in A, h z * Ψ (Function.update x i z)| := rfl
    _ ≤ ∑ i : Fin N, |f (x i) * ∫ z in A, h z * Ψ (Function.update x i z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (max Cf 0 * (max Ch 0 * max CΨ 0 * (volume A).toReal)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h2 : |∫ z in A, h z * Ψ (Function.update x i z)|
            ≤ max Ch 0 * max CΨ 0 * (volume A).toReal :=
          abs_fibreMean_mul_le hℓ hAc hhw hΨb hx i
        rw [abs_mul]
        exact mul_le_mul (le_trans (hfw _) (le_max_left _ _)) h2 (abs_nonneg _) (by positivity)
    _ = (N : ℝ) * (max Cf 0 * (max Ch 0 * max CΨ 0 * (volume A).toReal)) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

end Work.BoseFixB1
