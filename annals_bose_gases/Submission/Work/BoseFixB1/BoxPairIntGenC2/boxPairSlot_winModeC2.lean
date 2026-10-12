import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseFixB1.BoxPairIntGen.Defs
import Submission.Work.BoseFixB1.Core.boxCoreQVBundle
import Submission.Work.BoseFixB1.Core.coreAbstract
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the centred cube and the box projections -/

lemma volume_subset_acube_lt_top_c2 {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) : (volume A : ℝ≥0∞) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono hAc) ?_
  rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
  exact ENNReal.ofReal_lt_top

lemma abs_sub_le_abs_add_c2 (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

lemma abs_indicator_one_le_c2 (A : Set E3) (y : E3) :
    |A.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy]; norm_num
  · rw [Set.indicator_of_notMem hy]; norm_num

lemma boxQInd_eq_indicator_mul_c2 {n : ℕ} (volA : ℝ) (A : Set E3) (j : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (v : Submission.BoseGases.X n) :
    Work.UBBInputs8.boxQInd volA A j Ψ v
      = A.indicator (fun _ => (1 : ℝ)) (v j)
        * (Ψ v - (1 / volA) * ∫ z in A, Ψ (Function.update v j z)) := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  ring

/-- The box mean `volA⁻¹ ∫_A F` is bounded by `M` when `F` is. -/
lemma mean_bound_c2 {ℓ volA M : ℝ} {A : Set E3} (hℓ : 0 < ℓ)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {F : E3 → ℝ} (hF : ∀ w ∈ A, |F w| ≤ M) :
    |(1 / volA) * ∫ w in A, F w| ≤ M := by
  have hfin : (volume A : ℝ≥0∞) < ⊤ := volume_subset_acube_lt_top_c2 hℓ hAc
  have hb : |∫ w in A, F w| ≤ M * volA := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A) (f := F) (C := M)
      hfin (fun w hw => by rw [Real.norm_eq_abs]; exact hF w hw)
    rwa [Real.norm_eq_abs, ← hvolAr] at h
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hvolpos)]
  calc (1 / volA) * |∫ w in A, F w| ≤ (1 / volA) * (M * volA) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M := by field_simp

/-- A bound for `Φ` over the image of `acube ℓ × acube ℓ` under the double insertion. -/
lemma exists_ins2_bound_c2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X (N + 2) → ℝ}
    (hΦc : Continuous Φ) (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : Submission.BoseGases.X N) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ → z ∈ Submission.BoseGases.acube ℓ →
        |Φ (Submission.BoseGases.ins2 i j' y z x)| ≤ M := by
  have hcont : Continuous (fun p : E3 × E3 => Submission.BoseGases.ins2 i j' p.1 p.2 x) :=
    Submission.BoseGases.continuous_ins2_uncurry i j' x
  have hK : IsCompact
      ((fun p : E3 × E3 => Submission.BoseGases.ins2 i j' p.1 p.2 x)
        '' (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :=
    ((Submission.BoseGases.acube_compact hℓ).prod
      (Submission.BoseGases.acube_compact hℓ)).image hcont
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y z hy hz => ?_⟩
  have h1 := hC _ (Set.mem_image_of_mem _ (Set.mk_mem_prod hy hz))
  rw [Real.norm_eq_abs] at h1
  exact le_trans h1 (le_max_left _ _)

/-- The mean-free box projection is bounded by twice the state bound. -/
lemma abs_boxQInd_le_two_mul_c2 {N : ℕ} {ℓ volA M : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (x : Submission.BoseGases.X N)
    (hM : ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ →
      z ∈ Submission.BoseGases.acube ℓ → |Φ (Submission.BoseGases.ins2 i j' y z x)| ≤ M) :
    ∀ y t : E3, t ∈ Submission.BoseGases.acube ℓ →
      |Work.UBBInputs8.boxQInd volA A i Φ (Submission.BoseGases.ins2 i j' y t x)| ≤ 2 * M := by
  intro y t ht
  rw [boxQInd_eq_indicator_mul_c2, Submission.BoseGases.ins2_apply_i]
  have hupd : (∫ z in A, Φ (Function.update (Submission.BoseGases.ins2 i j' y t x) i z))
      = ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x) :=
    setIntegral_congr_fun hA (fun z _ => by rw [Submission.BoseGases.ins2_update_i])
  rw [hupd]
  by_cases hy : y ∈ A
  · have hInt : |(1 / volA) * ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x)| ≤ M :=
      mean_bound_c2 hℓ hAc hvolAr hvolpos hM0
        (F := fun z => Φ (Submission.BoseGases.ins2 i j' z t x))
        (fun z hz => hM z t (hAc hz) ht)
    have h2 : |Φ (Submission.BoseGases.ins2 i j' y t x)
        - (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x)| ≤ 2 * M := by
      calc |Φ (Submission.BoseGases.ins2 i j' y t x)
            - (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x)|
          ≤ |Φ (Submission.BoseGases.ins2 i j' y t x)|
            + |(1 / volA) * ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x)| :=
            abs_sub_le_abs_add_c2 _ _
        _ ≤ M + M := add_le_add (hM y t (hAc hy) ht) hInt
        _ = 2 * M := by ring
    calc |A.indicator (fun _ => (1 : ℝ)) y
          * (Φ (Submission.BoseGases.ins2 i j' y t x)
            - (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x))|
        = |A.indicator (fun _ => (1 : ℝ)) y|
          * |Φ (Submission.BoseGases.ins2 i j' y t x)
            - (1 / volA) * ∫ z in A, Φ (Submission.BoseGases.ins2 i j' z t x)| := abs_mul _ _
      _ ≤ 1 * (2 * M) :=
          mul_le_mul (abs_indicator_one_le_c2 A y) h2 (abs_nonneg _) (by linarith)
      _ = 2 * M := by ring
  · rw [Set.indicator_of_notMem hy, zero_mul, abs_zero]
    linarith

/-- Pointwise bound for the doubly projected state on `A × A`. -/
lemma abs_boxCoreQ_le_c2 {N : ℕ} {ℓ volA M : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (x : Submission.BoseGases.X N)
    (hM : ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ →
      z ∈ Submission.BoseGases.acube ℓ → |Φ (Submission.BoseGases.ins2 i j' y z x)| ≤ M)
    {y z : E3} (hy : y ∈ A) (hz : z ∈ A) :
    |Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z| ≤ 4 * M := by
  rw [Work.BoseFixB1.boxCoreQ_indicator i j' x hy hz]
  have h1 : |Φ (Submission.BoseGases.ins2 i j' y z x)| ≤ M := hM y z (hAc hy) (hAc hz)
  have h2 : |(1 / volA) * ∫ w in A, Φ (Submission.BoseGases.ins2 i j' w z x)| ≤ M :=
    mean_bound_c2 hℓ hAc hvolAr hvolpos hM0
      (F := fun w => Φ (Submission.BoseGases.ins2 i j' w z x))
      (fun w hw => hM w z (hAc hw) (hAc hz))
  have h3 : |(1 / volA) * ∫ w in A,
      (Φ (Submission.BoseGases.ins2 i j' y w x)
        - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w x))| ≤ 2 * M := by
    refine mean_bound_c2 (M := 2 * M) hℓ hAc hvolAr hvolpos (by linarith)
      (F := fun w => Φ (Submission.BoseGases.ins2 i j' y w x)
        - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w x)) (fun w hw => ?_)
    calc |Φ (Submission.BoseGases.ins2 i j' y w x)
          - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w x)|
        ≤ |Φ (Submission.BoseGases.ins2 i j' y w x)|
          + |(1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w x)| :=
          abs_sub_le_abs_add_c2 _ _
      _ ≤ M + M := add_le_add (hM y w (hAc hy) (hAc hw))
          (mean_bound_c2 hℓ hAc hvolAr hvolpos hM0
            (F := fun v => Φ (Submission.BoseGases.ins2 i j' v w x))
            (fun v hv => hM v w (hAc hv) (hAc hw)))
      _ = 2 * M := by ring

  calc |(Φ (Submission.BoseGases.ins2 i j' y z x)
          - (1 / volA) * ∫ w in A, Φ (Submission.BoseGases.ins2 i j' w z x))
        - (1 / volA) * ∫ w in A,
            (Φ (Submission.BoseGases.ins2 i j' y w x)
              - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w x))|
      ≤ |Φ (Submission.BoseGases.ins2 i j' y z x)
          - (1 / volA) * ∫ w in A, Φ (Submission.BoseGases.ins2 i j' w z x)|
        + |(1 / volA) * ∫ w in A,
            (Φ (Submission.BoseGases.ins2 i j' y w x)
              - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w x))| :=
          abs_sub_le_abs_add_c2 _ _
    _ ≤ (M + M) + 2 * M :=
        add_le_add (le_trans (abs_sub_le_abs_add_c2 _ _) (add_le_add h1 h2)) h3
    _ = 4 * M := by ring

/-! ## Measurability of the doubly projected state -/

lemma measurable_boxCoreQ_snd_c2 {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : Submission.BoseGases.X N) (y : E3) :
    Measurable (fun z : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z) := by
  have hΨ : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
    Work.SlotWord.measurable_boxQInd volA A hA i hΦ.measurable
  have hQ : Measurable
      (Work.UBBInputs8.boxQInd volA A (i.succAbove j') (Work.UBBInputs8.boxQInd volA A i Φ)) :=
    Work.SlotWord.measurable_boxQInd volA A hA (i.succAbove j') hΨ
  show Measurable (fun z : E3 => Work.UBBInputs8.boxQInd volA A (i.succAbove j')
      (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y z x))
  exact hQ.comp (Submission.BoseGases.continuous_ins2_snd i j' y x).measurable

lemma measurable_boxCoreQ_fst_c2 {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : Submission.BoseGases.X N) (z : E3) :
    Measurable (fun y : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z) := by
  have hΨ : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
    Work.SlotWord.measurable_boxQInd volA A hA i hΦ.measurable
  have hQ : Measurable
      (Work.UBBInputs8.boxQInd volA A (i.succAbove j') (Work.UBBInputs8.boxQInd volA A i Φ)) :=
    Work.SlotWord.measurable_boxQInd volA A hA (i.succAbove j') hΨ
  show Measurable (fun y : E3 => Work.UBBInputs8.boxQInd volA A (i.succAbove j')
      (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y z x))
  exact hQ.comp (Submission.BoseGases.continuous_ins2_fst i j' z x).measurable

/-! ## Mean-freeness of the box projection on a fibre -/

/-- The `j`-slot fibre of `Q_{A,j}Ψ` has vanishing integral over `A`. -/
lemma boxQInd_update_slice_zero_c2 {n : ℕ} {volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hvolAr : volA = ((volume : Measure E3).real A)) (hvolne : volA ≠ 0)
    (hfin : (volume A : ℝ≥0∞) < ⊤) {Ψ : Submission.BoseGases.X n → ℝ} (j : Fin n)
    (c : Submission.BoseGases.X n)
    (hInt : IntegrableOn (fun y => Ψ (Function.update c j y)) A) :
    (∫ y in A, Work.UBBInputs8.boxQInd volA A j Ψ (Function.update c j y)) = 0 := by
  set I : ℝ := ∫ y in A, Ψ (Function.update c j y) with hI
  have key : ∀ y : E3, Work.UBBInputs8.boxQInd volA A j Ψ (Function.update c j y)
      = A.indicator (fun _ => (1 : ℝ)) y * (Ψ (Function.update c j y) - (1 / volA) * I) := by
    intro y
    rw [boxQInd_eq_indicator_mul_c2]
    have h1 : (Function.update c j y) j = y := Function.update_self j y c
    rw [h1]
    have h2 : (∫ z in A, Ψ (Function.update (Function.update c j y) j z)) = I := by
      rw [hI]
      refine setIntegral_congr_fun hA (fun z _ => ?_)
      rw [Function.update_idem]
    rw [h2]
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have h1int : IntegrableOn
      (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) y * Ψ (Function.update c j y)) A := by
    refine hInt.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with y hy
    rw [Set.indicator_of_mem hy, one_mul]
  have h2int : IntegrableOn
      (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) y * ((1 / volA) * I)) A := by
    have hbase : IntegrableOn (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) y) A :=
      Integrable.of_bound ((measurable_const.indicator hA).aestronglyMeasurable) 1
        (Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_eq_abs]; exact abs_indicator_one_le_c2 A y))
    exact (show Integrable (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) y)
        ((volume : Measure E3).restrict A) from hbase).mul_const _
  have hA1 : (∫ y in A, A.indicator (fun _ => (1 : ℝ)) y * Ψ (Function.update c j y)) = I := by
    rw [hI]
    exact setIntegral_congr_fun hA (fun y hy => by rw [Set.indicator_of_mem hy, one_mul])
  have hone : (∫ y in A, A.indicator (fun _ => (1 : ℝ)) y) = volA := by
    rw [show (∫ y in A, A.indicator (fun _ => (1 : ℝ)) y) = (∫ y in A, (1 : ℝ)) from
      setIntegral_congr_fun hA (fun y hy => Set.indicator_of_mem hy _)]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact hvolAr.symm
  have hA2 : (∫ y in A, A.indicator (fun _ => (1 : ℝ)) y * ((1 / volA) * I)) = I := by
    rw [show (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) y * ((1 / volA) * I))
        = fun y : E3 => ((1 / volA) * I) * A.indicator (fun _ => (1 : ℝ)) y from by
          funext y; ring]
    rw [MeasureTheory.integral_const_mul, hone]
    field_simp
  rw [show (∫ y in A, Work.UBBInputs8.boxQInd volA A j Ψ (Function.update c j y))
      = ∫ y in A, (A.indicator (fun _ => (1 : ℝ)) y * Ψ (Function.update c j y)
          - A.indicator (fun _ => (1 : ℝ)) y * ((1 / volA) * I)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun y => by
          simp only [key]; ring))]
  rw [MeasureTheory.integral_sub h1int h2int, hA1, hA2, sub_self]

/-! ## Mean-freeness of the doubly projected state -/

lemma boxCoreQ_mean_zero_snd_c2 {N : ℕ} {ℓ volA M : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : Submission.BoseGases.X N)
    (hM : ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ →
      z ∈ Submission.BoseGases.acube ℓ → |Φ (Submission.BoseGases.ins2 i j' y z x)| ≤ M) :
    ∀ y : E3, (∫ z in A, Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z) = 0 := by
  have hfin : (volume A : ℝ≥0∞) < ⊤ := volume_subset_acube_lt_top_c2 hℓ hAc
  have hvolne : volA ≠ 0 := ne_of_gt hvolpos
  have hΨb := abs_boxQInd_le_two_mul_c2 hA hℓ hAc hvolAr hvolpos hM0 i j' x hM
  have hΨm : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
    Work.SlotWord.measurable_boxQInd volA A hA i hΦ.measurable
  intro y
  have hInt : IntegrableOn
      (fun z : E3 => (Work.UBBInputs8.boxQInd volA A i Φ)
        (Function.update (Submission.BoseGases.ins2 i j' y 0 x) (i.succAbove j') z)) A := by
    have hfun : (fun z : E3 => (Work.UBBInputs8.boxQInd volA A i Φ)
        (Function.update (Submission.BoseGases.ins2 i j' y 0 x) (i.succAbove j') z))
        = fun z => (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y z x) := by
      funext z
      rw [Submission.BoseGases.ins2_update_succ]
    rw [hfun]
    refine IntegrableOn.of_bound hfin
      (hΨm.comp (Submission.BoseGases.continuous_ins2_snd i j' y x).measurable).aestronglyMeasurable
      (2 * M) ?_
    rw [MeasureTheory.ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall (fun z hz => by
      rw [Real.norm_eq_abs]
      exact hΨb y z (hAc hz))
  have hkey : (fun z : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z)
      = fun z => Work.UBBInputs8.boxQInd volA A (i.succAbove j')
          (Work.UBBInputs8.boxQInd volA A i Φ)
          (Function.update (Submission.BoseGases.ins2 i j' y 0 x) (i.succAbove j') z) := by
    funext z
    simp only [Work.BoseFixB1.boxCoreQ, Submission.BoseGases.ins2_update_succ]
  rw [hkey]
  exact boxQInd_update_slice_zero_c2 hA hvolAr hvolne hfin (i.succAbove j') _ hInt

lemma boxCoreQ_mean_zero_fst_c2 {N : ℕ} {ℓ volA M : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : Submission.BoseGases.X N)
    (hM : ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ →
      z ∈ Submission.BoseGases.acube ℓ → |Φ (Submission.BoseGases.ins2 i j' y z x)| ≤ M) :
    ∀ z : E3, (∫ y in A, Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z) = 0 := by
  have hfin : (volume A : ℝ≥0∞) < ⊤ := volume_subset_acube_lt_top_c2 hℓ hAc
  have hvolne : volA ≠ 0 := ne_of_gt hvolpos
  have hΨb := abs_boxQInd_le_two_mul_c2 hA hℓ hAc hvolAr hvolpos hM0 i j' x hM
  have hΨm : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
    Work.SlotWord.measurable_boxQInd volA A hA i hΦ.measurable
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  -- the `i`-slot fibre of `Q_A,i Φ` is mean-free
  have hzero : ∀ z : E3, z ∈ A →
      (∫ y in A, (Work.UBBInputs8.boxQInd volA A i Φ)
        (Submission.BoseGases.ins2 i j' y z x)) = 0 := by
    intro z hz
    have hInt : IntegrableOn
        (fun y : E3 => Φ (Function.update (Submission.BoseGases.ins2 i j' 0 z x) i y)) A := by
      have hfun : (fun y : E3 => Φ (Function.update (Submission.BoseGases.ins2 i j' 0 z x) i y))
          = fun y => Φ (Submission.BoseGases.ins2 i j' y z x) := by
        funext y
        rw [Submission.BoseGases.ins2_update_i]
      rw [hfun]
      refine IntegrableOn.of_bound hfin
        (hΦ.measurable.comp
          (Submission.BoseGases.continuous_ins2_fst i j' z x).measurable).aestronglyMeasurable
        M ?_
      rw [MeasureTheory.ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall (fun y hy => by
        rw [Real.norm_eq_abs]
        exact hM y z (hAc hy) (hAc hz))
    have hslice := boxQInd_update_slice_zero_c2 (Ψ := Φ)
      hA hvolAr hvolne hfin i (Submission.BoseGases.ins2 i j' 0 z x) hInt
    rwa [show (fun y : E3 => Work.UBBInputs8.boxQInd volA A i Φ
          (Function.update (Submission.BoseGases.ins2 i j' 0 z x) i y))
        = fun y => Work.UBBInputs8.boxQInd volA A i Φ
            (Submission.BoseGases.ins2 i j' y z x) from
          funext fun y => by rw [Submission.BoseGases.ins2_update_i]] at hslice
  -- joint integrability of the mixed integrand, for Fubini
  have hjoint : Integrable
      (Function.uncurry (fun y w : E3 => (Work.UBBInputs8.boxQInd volA A i Φ)
        (Submission.BoseGases.ins2 i j' y w x)))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ (2 * M) ?_
    · exact (hΨm.comp (Submission.BoseGases.continuous_ins2_uncurry i j' x).measurable).aestronglyMeasurable
    · rw [Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
      exact Filter.Eventually.of_forall (fun q hq => by
        rw [Real.norm_eq_abs]
        exact hΨb q.1 q.2 (hAc hq.2))
  have hswapint : (∫ y in A, ∫ w in A,
      (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y w x)) = 0 := by
    rw [MeasureTheory.integral_integral_swap hjoint]
    rw [show (∫ w in A, ∫ y in A,
        (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y w x))
        = ∫ w in A, (0 : ℝ) from
      integral_congr_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem hA] with w hw
        exact hzero w hw)]
    simp
  intro z
  by_cases hz : z ∈ A
  · have hpoint : ∀ y : E3, Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z
        = A.indicator (fun _ => (1 : ℝ)) z
          * ((Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y z x)
            - (1 / volA) * ∫ w in A,
                (Work.UBBInputs8.boxQInd volA A i Φ)
                  (Submission.BoseGases.ins2 i j' y w x)) := by
      intro y
      rw [Work.BoseFixB1.boxCoreQ, boxQInd_eq_indicator_mul_c2]
      rw [Submission.BoseGases.ins2_apply_succ]
      have hupd : (∫ z' in A, (Work.UBBInputs8.boxQInd volA A i Φ)
            (Function.update (Submission.BoseGases.ins2 i j' y z x) (i.succAbove j') z'))
          = ∫ w in A, (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y w x) :=
        setIntegral_congr_fun hA (fun w _ => by rw [Submission.BoseGases.ins2_update_succ])
      rw [hupd]
    have hm1 : IntegrableOn (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) z
        * (Work.UBBInputs8.boxQInd volA A i Φ)
          (Submission.BoseGases.ins2 i j' y z x)) A := by
      refine IntegrableOn.of_bound hfin
        ((measurable_const.mul (hΨm.comp
          (Submission.BoseGases.continuous_ins2_fst i j' z x).measurable)).aestronglyMeasurable)
        (|A.indicator (fun _ => (1 : ℝ)) z| * (2 * M)) ?_
      rw [MeasureTheory.ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall (fun y hy => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hΨb y z (hAc hz)) (abs_nonneg _))
    have hm2 : IntegrableOn (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ∫ w in A, (Work.UBBInputs8.boxQInd volA A i Φ)
            (Submission.BoseGases.ins2 i j' y w x))) A := by
      have hj : Integrable (fun q : E3 × E3 => A.indicator (fun _ => (1 : ℝ)) z
          * ((1 / volA) * (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' q.1 q.2 x)))
          (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
        refine Integrable.of_bound ?_
          (|A.indicator (fun _ => (1 : ℝ)) z| * (|1 / volA| * (2 * M))) ?_
        · exact (measurable_const.mul (measurable_const.mul
            (hΨm.comp
              (Submission.BoseGases.continuous_ins2_uncurry i j' x).measurable))).aestronglyMeasurable
        · rw [Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
          exact Filter.Eventually.of_forall (fun q hq => by
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hΨb q.1 q.2 (hAc hq.2)) (abs_nonneg _))
              (abs_nonneg _))
      refine (show Integrable (fun y : E3 => A.indicator (fun _ => (1 : ℝ)) z
          * ((1 / volA) * (∫ w in A, (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y w x))))
          ((volume : Measure E3).restrict A) from ?_)
      refine (hj.integral_prod_left).congr ?_
      filter_upwards with y
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [show (∫ y in A, Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z)
        = ∫ y in A, (A.indicator (fun _ => (1 : ℝ)) z
              * (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y z x)
            - A.indicator (fun _ => (1 : ℝ)) z * ((1 / volA) * ∫ w in A,
                (Work.UBBInputs8.boxQInd volA A i Φ)
                  (Submission.BoseGases.ins2 i j' y w x))) from
          integral_congr_ae (Filter.Eventually.of_forall (fun y => by
            simp only [hpoint]; ring))]
    rw [MeasureTheory.integral_sub hm1 hm2]
    have hA1 : (∫ y in A, A.indicator (fun _ => (1 : ℝ)) z
        * (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y z x)) = 0 := by
      rw [MeasureTheory.integral_const_mul, hzero z hz, mul_zero]
    have hA2 : (∫ y in A, A.indicator (fun _ => (1 : ℝ)) z * ((1 / volA) * ∫ w in A,
        (Work.UBBInputs8.boxQInd volA A i Φ) (Submission.BoseGases.ins2 i j' y w x))) = 0 := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hswapint]
      ring
    rw [hA1, hA2, sub_self]
  · have h0 : (fun y : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z) = fun _ => (0 : ℝ) :=
      funext (fun y => Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_right i j' x hz)
    rw [h0]
    simp

/-! ## The two one-variable means appearing in `boxCoreQ_indicator` -/

/-- `volA⁻¹ ∫_{w∈A} Φ(ins2 i j' w z r2)`: the slot mean of `Φ` in the first distinguished slot. -/
noncomputable def coreMz {N : ℕ} (volA : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) (z : E3) : ℝ :=
  (1 / volA) * ∫ w in A, Φ (Submission.BoseGases.ins2 i j' w z r2)

/-- `volA⁻¹ ∫_{w∈A} (Φ(ins2 i j' y w r2) − volA⁻¹∫_{v∈A} Φ(ins2 i j' v w r2))`. -/
noncomputable def coreNy {N : ℕ} (volA : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) (y : E3) : ℝ :=
  (1 / volA) * ∫ w in A,
    (Φ (Submission.BoseGases.ins2 i j' y w r2)
      - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w r2))

/-- Measurability of a parametric integral with a continuous uncurried integrand. -/
lemma measurable_parametric_integral_c2 {A : Set E3} {f : E3 → E3 → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    Measurable (fun z : E3 => ∫ w in A, f z w) :=
  (hf.stronglyMeasurable.integral_prod_right
    (ν := (volume : Measure E3).restrict A)).measurable

lemma coreMz_measurable {N : ℕ} {volA : ℝ} {A : Set E3}
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (r2 : Submission.BoseGases.X N) :
    Measurable (coreMz volA A Φ i j' r2) := by
  have hcont : Continuous
      (Function.uncurry (fun z w : E3 => Φ (Submission.BoseGases.ins2 i j' w z r2))) :=
    hΦ.comp ((Submission.BoseGases.continuous_ins2_uncurry i j' r2).comp
      (continuous_snd.prodMk continuous_fst))
  have h := measurable_parametric_integral_c2 (A := A) hcont
  show Measurable (fun z : E3 => (1 / volA) * ∫ w in A,
    Φ (Submission.BoseGases.ins2 i j' w z r2))
  exact h.const_mul _

lemma coreNy_eq_c2 {N : ℕ} {volA : ℝ} {A : Set E3}
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) (y : E3)
    (h1 : IntegrableOn (fun w : E3 => Φ (Submission.BoseGases.ins2 i j' y w r2)) A)
    (h2 : IntegrableOn (fun w : E3 => (1 / volA) * ∫ v in A,
      Φ (Submission.BoseGases.ins2 i j' v w r2)) A) :
    coreNy volA A Φ i j' r2 y
      = (1 / volA) * (∫ w in A, Φ (Submission.BoseGases.ins2 i j' y w r2))
        - (1 / volA) * (∫ w in A, (1 / volA) * ∫ v in A,
            Φ (Submission.BoseGases.ins2 i j' v w r2)) := by
  rw [coreNy]
  congr 1
  rw [MeasureTheory.integral_sub h1 h2, MeasureTheory.integral_const_mul]
  ring

lemma coreNy_measurable {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (r2 : Submission.BoseGases.X N) :
    Measurable (coreNy volA A Φ i j' r2) := by
  obtain ⟨M, hM0, hM⟩ := exists_ins2_bound_c2 hℓ hΦ i j' r2
  have hfin : (volume A : ℝ≥0∞) < ⊤ := volume_subset_acube_lt_top_c2 hℓ hAc
  have hIntΦ : ∀ y : E3, IntegrableOn
      (fun w : E3 => Φ (Submission.BoseGases.ins2 i j' y w r2)) A := by
    intro y
    have hcy : Continuous (fun w : E3 => Φ (Submission.BoseGases.ins2 i j' y w r2)) :=
      hΦ.comp (Submission.BoseGases.continuous_ins2_snd i j' y r2)
    obtain ⟨Cy, hCy⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
      hcy.continuousOn
    refine MeasureTheory.IntegrableOn.of_bound hfin hcy.measurable.aestronglyMeasurable Cy ?_
    rw [MeasureTheory.ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall (fun w hw => hCy w (hAc hw))
  have hIntg : IntegrableOn (fun w : E3 => (1 / volA) * ∫ v in A,
      Φ (Submission.BoseGases.ins2 i j' v w r2)) A := by
    have hcg : Measurable (fun w : E3 => ∫ v in A,
        Φ (Submission.BoseGases.ins2 i j' v w r2)) :=
      measurable_parametric_integral_c2 (A := A)
        (f := fun w v : E3 => Φ (Submission.BoseGases.ins2 i j' v w r2))
        (hΦ.comp ((Submission.BoseGases.continuous_ins2_uncurry i j' r2).comp
          (continuous_snd.prodMk continuous_fst)))
    have hb : ∀ w ∈ A, |∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w r2)| ≤ M * volA := by
      intro w hw
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
        (f := fun v => Φ (Submission.BoseGases.ins2 i j' v w r2)) (C := M) hfin
        (fun v hv => by rw [Real.norm_eq_abs]; exact hM v w (hAc hv) (hAc hw))
      rwa [Real.norm_eq_abs, MeasureTheory.measureReal_def, ← hvolA] at h
    refine MeasureTheory.IntegrableOn.of_bound hfin
      (hcg.const_mul (1 / volA)).aestronglyMeasurable (|1 / volA| * (M * volA)) ?_
    rw [MeasureTheory.ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall (fun w hw => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb w hw) (abs_nonneg _))
  have heq : coreNy volA A Φ i j' r2 = fun y : E3 =>
      (1 / volA) * (∫ w in A, Φ (Submission.BoseGases.ins2 i j' y w r2))
        - (1 / volA) * (∫ w in A, (1 / volA) * ∫ v in A,
            Φ (Submission.BoseGases.ins2 i j' v w r2)) :=
    funext (fun y => coreNy_eq_c2 i j' r2 y (hIntΦ y) hIntg)
  rw [heq]
  have hP : Measurable (fun y : E3 =>
      (1 / volA) * (∫ w in A, Φ (Submission.BoseGases.ins2 i j' y w r2))) :=
    (measurable_parametric_integral_c2 (A := A)
      (f := fun y w : E3 => Φ (Submission.BoseGases.ins2 i j' y w r2))
      (hΦ.comp (Submission.BoseGases.continuous_ins2_uncurry i j' r2))).const_mul _
  exact hP.sub (measurable_const :
    Measurable (fun _ : E3 => (1 / volA) * (∫ w in A, (1 / volA) * ∫ v in A,
      Φ (Submission.BoseGases.ins2 i j' v w r2))))

lemma coreMz_bound {N : ℕ} {ℓ volA M : ℝ} {A : Set E3} (hℓ : 0 < ℓ)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N)
    (hM : ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ →
      z ∈ Submission.BoseGases.acube ℓ → |Φ (Submission.BoseGases.ins2 i j' y z r2)| ≤ M) :
    ∀ z ∈ A, |coreMz volA A Φ i j' r2 z| ≤ M := by
  intro z hz
  rw [coreMz]
  exact mean_bound_c2 hℓ hAc hvolAr hvolpos hM0
    (F := fun w => Φ (Submission.BoseGases.ins2 i j' w z r2))
    (fun w hw => hM w z (hAc hw) (hAc hz))

lemma coreNy_bound {N : ℕ} {ℓ volA M : ℝ} {A : Set E3} (hℓ : 0 < ℓ)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolAr : volA = ((volume : Measure E3).real A)) (hvolpos : 0 < volA) (hM0 : 0 ≤ M)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N)
    (hM : ∀ y z : E3, y ∈ Submission.BoseGases.acube ℓ →
      z ∈ Submission.BoseGases.acube ℓ → |Φ (Submission.BoseGases.ins2 i j' y z r2)| ≤ M) :
    ∀ y ∈ A, |coreNy volA A Φ i j' r2 y| ≤ 2 * M := by
  intro y hy
  rw [coreNy]
  refine mean_bound_c2 (M := 2 * M) hℓ hAc hvolAr hvolpos (by linarith)
    (F := fun w => Φ (Submission.BoseGases.ins2 i j' y w r2)
      - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w r2)) (fun w hw => ?_)
  calc |Φ (Submission.BoseGases.ins2 i j' y w r2)
        - (1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w r2)|
      ≤ |Φ (Submission.BoseGases.ins2 i j' y w r2)|
        + |(1 / volA) * ∫ v in A, Φ (Submission.BoseGases.ins2 i j' v w r2)| :=
        abs_sub_le_abs_add_c2 _ _
    _ ≤ M + M := add_le_add (hM y w (hAc hy) (hAc hw))
        (mean_bound_c2 hℓ hAc hvolAr hvolpos hM0
          (F := fun v => Φ (Submission.BoseGases.ins2 i j' v w r2))
          (fun v hv => hM v w (hAc hv) (hAc hw)))
    _ = 2 * M := by ring

/-- The pointwise decomposition of the difference `Φ − Q_{j'}Q_i Φ` on `A × A`. -/
lemma coreQ_decomp {N : ℕ} {volA : ℝ} {A : Set E3}
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) {y z : E3} (hy : y ∈ A) (hz : z ∈ A) :
    (Φ (Submission.BoseGases.ins2 i j' y z r2) : ℂ)
        - Work.BoseFixB1.boxCoreKc volA A Φ i j' r2 y z
      = ((coreMz volA A Φ i j' r2 z + coreNy volA A Φ i j' r2 y : ℝ) : ℂ) := by
  have h1 := Work.BoseFixB1.boxCoreQ_indicator (volA := volA) (A := A) (Φ := Φ) i j' r2 hy hz
  rw [Work.BoseFixB1.boxCoreKc, h1]
  simp only [coreMz, coreNy]
  push_cast
  ring

/-! ## The windowed mode: measurability and bound -/

lemma boxWinModeC_measurable_c2 {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    {χ : E3 → ℝ} (hχ : Continuous χ) (p : E3) :
    Measurable (Work.BoseFixB1.boxWinModeC volA A χ p) := by
  have h1 : Measurable (fun z : E3 => A.indicator (fun _ => (1 : ℂ)) z) :=
    measurable_const.indicator hA
  have h2 : Measurable (fun z : E3 =>
      (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))) :=
    (Complex.continuous_ofReal.measurable.comp hχ.measurable).mul
      (Complex.measurable_exp.comp (by fun_prop))
  have h3 : Measurable (fun _ : E3 =>
      ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
        (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) :=
    measurable_const
  exact h1.mul (h2.sub h3)

lemma boxWinModeC_eq_zero_of_notMem_c2 {volA : ℝ} {A : Set E3} {χ : E3 → ℝ} {p z : E3}
    (hz : z ∉ A) : Work.BoseFixB1.boxWinModeC volA A χ p z = 0 := by
  simp only [Work.BoseFixB1.boxWinModeC, Set.indicator_of_notMem hz, zero_mul]

lemma boxWinModeC_norm_le_c2 {volA ℓ B : ℝ} {A : Set E3} {χ : E3 → ℝ} (hℓ : 0 < ℓ)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    (hB : 0 ≤ B) (hχB : ∀ z, ‖χ z‖ ≤ B) (p : E3) :
    ∀ z : E3, ‖Work.BoseFixB1.boxWinModeC volA A χ p z‖ ≤ 2 * B := by
  have hfin : (MeasureTheory.volume : Measure E3) A < ⊤ := volume_subset_acube_lt_top_c2 hℓ hAc
  have hInt : ‖∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))‖
      ≤ B * volA := by
    have h1 : ‖∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))‖
        ≤ B * (MeasureTheory.volume : Measure E3).real A := by
      refine norm_setIntegral_le_of_norm_le_const hfin (fun w _ => ?_)
      simp only [Complex.norm_mul, Complex.norm_exp]
      simpa using hχB w
    rw [MeasureTheory.measureReal_def, ← hvolA] at h1
    exact h1
  intro z
  by_cases hz : z ∈ A
  · rw [Work.BoseFixB1.boxWinModeC, Set.indicator_of_mem hz, one_mul]
    have h1 : ‖(χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))‖ ≤ B := by
      simp only [Complex.norm_mul, Complex.norm_exp]
      simpa using hχB z
    have h2 : ‖((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
        (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))‖ ≤ B := by
      have hnorm : ‖((volA⁻¹ : ℝ) : ℂ)‖ = |volA⁻¹| := by simp
      rw [Complex.norm_mul, hnorm, abs_inv, abs_of_pos hvolpos]
      refine le_trans (mul_le_mul_of_nonneg_left hInt (by positivity)) (le_of_eq ?_)
      rw [mul_comm B volA, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hvolpos), one_mul]
    calc ‖(χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
          - ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
              (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))‖
        ≤ ‖(χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))‖
          + ‖((volA⁻¹ : ℝ) : ℂ) * ∫ w in A,
              (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))‖ :=
          norm_sub_le _ _
      _ ≤ B + B := add_le_add h1 h2
      _ = 2 * B := by ring
  · rw [boxWinModeC_eq_zero_of_notMem_c2 hz, norm_zero]
    linarith

theorem boxPairSlot_winModeC2 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (r2 : Submission.BoseGases.X N)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.boxPairSlot A Φ (Work.BoseFixB1.boxWinModeC volA A χ (-p))
        (Work.BoseFixB1.boxWinModeC volA A χ p) i j' r2
      = ∫ y in A, ∫ z in A,
          (χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
            * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                  (Work.UBBInputs8.boxQInd volA A i Φ))
                (Submission.BoseGases.ins2 i j' y z r2) : ℂ) := by
  have hfin : (volume A : ℝ≥0∞) < ⊤ := volume_subset_acube_lt_top_c2 hℓ hAc
  have hvolAr : volA = ((volume : Measure E3).real A) := by
    rw [MeasureTheory.measureReal_def]; exact hvolA
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨Cχ, hCχ⟩ := hχs.exists_bound_of_continuous hχc
  have hB0 : 0 ≤ max Cχ 0 := le_max_right _ _
  have hχB : ∀ z : E3, ‖χ z‖ ≤ max Cχ 0 := fun z => le_trans (hCχ z) (le_max_left _ _)
  obtain ⟨M, hM0, hM⟩ := exists_ins2_bound_c2 hℓ hΦ i j' r2
  -- a.e. membership in `A × A`
  have haemem : ∀ᵐ q ∂((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A),
      q.1 ∈ A ∧ q.2 ∈ A := by
    have h := MeasureTheory.self_mem_ae_restrict (μ := (volume : Measure (E3 × E3)))
      (hA.prod hA)
    rw [MeasureTheory.Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    filter_upwards [h] with q hq
    exact Set.mem_prod.mp hq
  -- bounds for the two mode factors
  have hC1b : ‖boxCoreC volA A (boxCoreU χ p)‖ ≤ max Cχ 0 := by
    have h1 : ‖∫ w in A, boxCoreU χ p w‖ ≤ max Cχ 0 * volA := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
        (f := fun w => boxCoreU χ p w) (C := max Cχ 0) hfin
        (fun w _ => by rw [boxCore_norm_boxCoreU]; exact hχB w)
      rwa [← hvolAr] at h
    rw [boxCoreC, Complex.norm_mul]
    have hnorm : ‖((volA⁻¹ : ℝ) : ℂ)‖ = |volA⁻¹| := by simp
    rw [hnorm, abs_inv, abs_of_pos hvolpos]
    calc volA⁻¹ * ‖∫ w in A, boxCoreU χ p w‖ ≤ volA⁻¹ * (max Cχ 0 * volA) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = max Cχ 0 := by field_simp
  have hC2b : ‖boxCoreC volA A (boxCoreV χ p)‖ ≤ max Cχ 0 := by
    have h1 : ‖∫ w in A, boxCoreV χ p w‖ ≤ max Cχ 0 * volA := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
        (f := fun w => boxCoreV χ p w) (C := max Cχ 0) hfin
        (fun w _ => by rw [boxCore_norm_boxCoreV]; exact hχB w)
      rwa [← hvolAr] at h
    rw [boxCoreC, Complex.norm_mul]
    have hnorm : ‖((volA⁻¹ : ℝ) : ℂ)‖ = |volA⁻¹| := by simp
    rw [hnorm, abs_inv, abs_of_pos hvolpos]
    calc volA⁻¹ * ‖∫ w in A, boxCoreV χ p w‖ ≤ volA⁻¹ * (max Cχ 0 * volA) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = max Cχ 0 := by field_simp
  have hUb : ∀ y : E3, ‖boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p)‖ ≤ 2 * max Cχ 0 := by
    intro y
    calc ‖boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p)‖
        ≤ ‖boxCoreU χ p y‖ + ‖boxCoreC volA A (boxCoreU χ p)‖ := norm_sub_le _ _
      _ ≤ max Cχ 0 + max Cχ 0 :=
          add_le_add (by rw [boxCore_norm_boxCoreU]; exact hχB y) hC1b
      _ = 2 * max Cχ 0 := by ring
  have hVb : ∀ z : E3, ‖boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p)‖ ≤ 2 * max Cχ 0 := by
    intro z
    calc ‖boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p)‖
        ≤ ‖boxCoreV χ p z‖ + ‖boxCoreC volA A (boxCoreV χ p)‖ := norm_sub_le _ _
      _ ≤ max Cχ 0 + max Cχ 0 :=
          add_le_add (by rw [boxCore_norm_boxCoreV]; exact hχB z) hC2b
      _ = 2 * max Cχ 0 := by ring
  have hGm_bd : ∀ z : E3, ‖boxWinModeC volA A χ (-p) z‖ ≤ 2 * max Cχ 0 :=
    boxWinModeC_norm_le_c2 hℓ hAc hvolA hvolpos hB0 hχB (-p)
  have hGp_bd : ∀ z : E3, ‖boxWinModeC volA A χ p z‖ ≤ 2 * max Cχ 0 :=
    boxWinModeC_norm_le_c2 hℓ hAc hvolA hvolpos hB0 hχB p
  have hGm_meas : Measurable (boxWinModeC volA A χ (-p)) := boxWinModeC_measurable_c2 hA hχc (-p)
  have hGp_meas : Measurable (boxWinModeC volA A χ p) := boxWinModeC_measurable_c2 hA hχc p
  have hUcont : Continuous (fun y : E3 => boxCoreU χ p y) := Work.BoseFixB1.Core.continuous_boxCoreU hχc p
  have hVcont : Continuous (fun z : E3 => boxCoreV χ p z) := Work.BoseFixB1.Core.continuous_boxCoreV hχc p
  have hQb : ∀ y z : E3, y ∈ A → z ∈ A →
      ‖boxCoreKc volA A Φ i j' r2 y z‖ ≤ 4 * M := by
    intro y z hy hz
    rw [boxCoreKc, Complex.norm_real, Real.norm_eq_abs]
    exact abs_boxCoreQ_le_c2 hA hℓ hAc hvolAr hvolpos hM0 i j' r2 hM hy hz
  have hQmeas2 : Measurable (fun q : E3 × E3 => boxCoreKc volA A Φ i j' r2 q.1 q.2) :=
    Complex.continuous_ofReal.measurable.comp
      ((Work.SlotWord.measurable_boxQInd volA A hA (i.succAbove j')
        (Work.SlotWord.measurable_boxQInd volA A hA i hΦ.measurable)).comp
        (Submission.BoseGases.continuous_ins2_uncurry i j' r2).measurable)
  have hMzmeas : Measurable (coreMz volA A Φ i j' r2) := coreMz_measurable hΦ i j' r2
  have hNymeas : Measurable (coreNy volA A Φ i j' r2) := coreNy_measurable hA hℓ hAc hvolA hΦ i j' r2
  -- mean-freeness of the two mode factors
  have hUmz : (∫ y in A, (boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p))) = 0 := by
    rw [show (∫ y in A, (boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p)))
        = (∫ y in A, boxWinModeC volA A χ (-p) y) from
      setIntegral_congr_fun hA (fun y hy => (boxWinModeC_neg_eq p hy).symm)]
    exact boxWinModeC_integral_zero hA hχc hχs hχsupp hvolA hvolpos (-p)
  have hVv : (∫ z in A, (boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p))) = 0 := by
    rw [show (∫ z in A, (boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p)))
        = (∫ z in A, boxWinModeC volA A χ p z) from
      setIntegral_congr_fun hA (fun z hz => (boxWinModeC_pos_eq p hz).symm)]
    exact boxWinModeC_integral_zero hA hχc hχs hχsupp hvolA hvolpos p
  -- integrability of the various integrands on the product measure
  have hintF1 : Integrable (fun q : E3 × E3 =>
      boxWinModeC volA A χ (-p) q.1 * boxWinModeC volA A χ p q.2
        * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ (((2 * max Cχ 0) * (2 * max Cχ 0)) * M) ?_
    · exact (((hGm_meas.comp measurable_fst).mul (hGp_meas.comp measurable_snd)).mul
        (Complex.continuous_ofReal.measurable.comp
          (hΦ.measurable.comp
            (Submission.BoseGases.continuous_ins2_uncurry i j' r2).measurable))).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul
      · apply mul_le_mul
        · exact hGm_bd q.1
        · exact hGp_bd q.2
        · positivity
        · positivity
      · exact hM q.1 q.2 (hAc hq.1) (hAc hq.2)
      · positivity
      · positivity
  have hintF4 : Integrable (fun q : E3 × E3 => (χ q.1 : ℂ) * (χ q.2 : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ p (q.1 - q.2) : ℝ) : ℂ))
      * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ))
          (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℂ))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ ((max Cχ 0) * (max Cχ 0) * 1 * (4 * M)) ?_
    · exact ((((Complex.continuous_ofReal.measurable.comp
          (hχc.measurable.comp measurable_fst)).mul
        (Complex.continuous_ofReal.measurable.comp
          (hχc.measurable.comp measurable_snd))).mul
        (Complex.measurable_exp.comp (by fun_prop))).mul hQmeas2).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      have hexp : ‖Complex.exp (Complex.I * ((inner ℝ p (q.1 - q.2) : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]; simp
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · exact hχB q.1
          · exact hχB q.2
          · positivity
          · positivity
        · exact hexp
        · positivity
        · positivity
      · exact hQb q.1 q.2 hq.1 hq.2
      · positivity
      · positivity
  have hintG1 : Integrable (fun q : E3 × E3 =>
      (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
        * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ (((2 * max Cχ 0) * (2 * max Cχ 0)) * M) ?_
    · exact ((((hUcont.measurable.sub measurable_const).comp measurable_fst).mul
        ((hVcont.measurable.sub measurable_const).comp measurable_snd)).mul
        (Complex.continuous_ofReal.measurable.comp
          (hΦ.measurable.comp
            (Submission.BoseGases.continuous_ins2_uncurry i j' r2).measurable))).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul
      · apply mul_le_mul
        · exact hUb q.1
        · exact hVb q.2
        · positivity
        · positivity
      · exact hM q.1 q.2 (hAc hq.1) (hAc hq.2)
      · positivity
      · positivity
  have hintG2 : Integrable (fun q : E3 × E3 =>
      (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
        * boxCoreKc volA A Φ i j' r2 q.1 q.2)
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ (((2 * max Cχ 0) * (2 * max Cχ 0)) * (4 * M)) ?_
    · exact ((((hUcont.measurable.sub measurable_const).comp measurable_fst).mul
        ((hVcont.measurable.sub measurable_const).comp measurable_snd)).mul
        hQmeas2).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      rw [Complex.norm_mul, Complex.norm_mul]
      apply mul_le_mul
      · apply mul_le_mul
        · exact hUb q.1
        · exact hVb q.2
        · positivity
        · positivity
      · exact hQb q.1 q.2 hq.1 hq.2
      · positivity
      · positivity
  have hintG3 : Integrable (fun q : E3 × E3 =>
      boxCoreU χ p q.1 * boxCoreV χ p q.2 * boxCoreKc volA A Φ i j' r2 q.1 q.2)
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ (((max Cχ 0) * (max Cχ 0)) * (4 * M)) ?_
    · exact (((hUcont.measurable.comp measurable_fst).mul
        (hVcont.measurable.comp measurable_snd)).mul hQmeas2).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      rw [Complex.norm_mul, Complex.norm_mul]
      apply mul_le_mul
      · apply mul_le_mul
        · rw [boxCore_norm_boxCoreU]; exact hχB q.1
        · rw [boxCore_norm_boxCoreV]; exact hχB q.2
        · positivity
        · positivity
      · exact hQb q.1 q.2 hq.1 hq.2
      · positivity
      · positivity
  have hintP1 : Integrable (fun q : E3 × E3 =>
      (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * ((boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * ((coreMz volA A Φ i j' r2 q.2 : ℝ) : ℂ)))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ ((2 * max Cχ 0) * ((2 * max Cχ 0) * M)) ?_
    · exact (((hUcont.measurable.sub measurable_const).comp measurable_fst).mul
        (((hVcont.measurable.sub measurable_const).comp measurable_snd).mul
          (Complex.continuous_ofReal.measurable.comp (hMzmeas.comp measurable_snd)))).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb := coreMz_bound hℓ hAc hvolAr hvolpos hM0 i j' r2 hM q.2 hq.2
      apply mul_le_mul
      · exact hUb q.1
      · apply mul_le_mul
        · exact hVb q.2
        · exact hb
        · positivity
        · positivity
      · positivity
      · positivity
  have hintP2 : Integrable (fun q : E3 × E3 =>
      ((boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
          * ((coreNy volA A Φ i j' r2 q.1 : ℝ) : ℂ))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p)))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ (((2 * max Cχ 0) * (2 * M)) * (2 * max Cχ 0)) ?_
    · exact ((((hUcont.measurable.sub measurable_const).comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp (hNymeas.comp measurable_fst))).mul
        ((hVcont.measurable.sub measurable_const).comp measurable_snd)).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb := coreNy_bound hℓ hAc hvolAr hvolpos hM0 i j' r2 hM q.1 hq.1
      apply mul_le_mul
      · apply mul_le_mul
        · exact hUb q.1
        · exact hb
        · positivity
        · positivity
      · exact hVb q.2
      · positivity
      · positivity
  -- the abstract `Q`-mean-freeness bundle
  have hsliceK : ∀ y : E3, Integrable (fun z : E3 => boxCoreKc volA A Φ i j' r2 y z)
      ((volume : Measure E3).restrict A) := by
    intro y
    by_cases hy : y ∈ A
    · refine Integrable.of_bound
        (hQmeas2.comp (continuous_const.prodMk continuous_id).measurable).aestronglyMeasurable
        (4 * M) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
      exact hQb y z hy hz
    · have h0 : (fun z : E3 => boxCoreKc volA A Φ i j' r2 y z) = fun _ => (0 : ℂ) := by
        funext z
        rw [boxCoreKc, Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_left i j' r2 hy,
          Complex.ofReal_zero]
      rw [h0]
      exact integrable_zero _ _ _
  have hsliceVK : ∀ y : E3, Integrable
      (fun z : E3 => boxCoreV χ p z * boxCoreKc volA A Φ i j' r2 y z)
      ((volume : Measure E3).restrict A) := by
    intro y
    by_cases hy : y ∈ A
    · refine Integrable.of_bound ?_ ((max Cχ 0) * (4 * M)) ?_
      · exact ((hVcont.measurable.mul
          (hQmeas2.comp (continuous_const.prodMk continuous_id).measurable))).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
        rw [Complex.norm_mul]
        apply mul_le_mul
        · rw [boxCore_norm_boxCoreV]; exact hχB z
        · exact hQb y z hy hz
        · positivity
        · positivity
    · have h0 : (fun z : E3 => boxCoreV χ p z * boxCoreKc volA A Φ i j' r2 y z)
          = fun _ => (0 : ℂ) := by
        funext z
        rw [boxCoreKc, Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_left i j' r2 hy,
          Complex.ofReal_zero, mul_zero]
      rw [h0]
      exact integrable_zero _ _ _
  have hvK : Integrable
      (Function.uncurry (fun y z : E3 => boxCoreV χ p z * boxCoreKc volA A Φ i j' r2 y z))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ ((max Cχ 0) * (4 * M)) ?_
    · exact (((hVcont.measurable.comp measurable_snd).mul hQmeas2)).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      simp only [Function.uncurry]
      rw [Complex.norm_mul]
      apply mul_le_mul
      · rw [boxCore_norm_boxCoreV]; exact hχB q.2
      · exact hQb q.1 q.2 hq.1 hq.2
      · positivity
      · positivity
  have huvK : Integrable
      (Function.uncurry (fun y z : E3 =>
        boxCoreU χ p y * (boxCoreV χ p z * boxCoreKc volA A Φ i j' r2 y z)))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine Integrable.of_bound ?_ ((max Cχ 0) * ((max Cχ 0) * (4 * M))) ?_
    · exact ((hUcont.measurable.comp measurable_fst).mul
        ((hVcont.measurable.comp measurable_snd).mul hQmeas2)).aestronglyMeasurable
    · filter_upwards [haemem] with q hq
      simp only [Function.uncurry]
      rw [Complex.norm_mul, Complex.norm_mul]
      apply mul_le_mul
      · rw [boxCore_norm_boxCoreU]; exact hχB q.1
      · apply mul_le_mul
        · rw [boxCore_norm_boxCoreV]; exact hχB q.2
        · exact hQb q.1 q.2 hq.1 hq.2
        · positivity
        · positivity
      · positivity
      · positivity
  have hsliceKr : ∀ y : E3, Integrable
      (fun z : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z)
      ((volume : Measure E3).restrict A) := by
    intro y
    by_cases hy : y ∈ A
    · refine Integrable.of_bound
        (measurable_boxCoreQ_snd_c2 hA hΦ i j' r2 y).aestronglyMeasurable (4 * M) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
      rw [Real.norm_eq_abs]
      exact abs_boxCoreQ_le_c2 hA hℓ hAc hvolAr hvolpos hM0 i j' r2 hM hy hz
    · have h0 : (fun z : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z)
          = fun _ => (0 : ℝ) :=
        funext (fun z => Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_left i j' r2 hy)
      rw [h0]
      exact integrable_zero _ _ _
  have hsliceKf : ∀ z : E3, Integrable
      (fun y : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z)
      ((volume : Measure E3).restrict A) := by
    intro z
    by_cases hz : z ∈ A
    · refine Integrable.of_bound
        (measurable_boxCoreQ_fst_c2 hA hΦ i j' r2 z).aestronglyMeasurable (4 * M) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hA] with y hy
      rw [Real.norm_eq_abs]
      exact abs_boxCoreQ_le_c2 hA hℓ hAc hvolAr hvolpos hM0 i j' r2 hM hy hz
    · have h0 : (fun y : E3 => Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z)
          = fun _ => (0 : ℝ) :=
        funext (fun y => Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_right i j' r2 hz)
      rw [h0]
      exact integrable_zero _ _ _
  have hmz : ∀ y : E3, (∫ z, boxCoreKc volA A Φ i j' r2 y z
      ∂((volume : Measure E3).restrict A)) = 0 := by
    intro y
    rw [show (∫ z, boxCoreKc volA A Φ i j' r2 y z ∂((volume : Measure E3).restrict A))
        = (((∫ z in A, Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z) : ℝ) : ℂ) from
      Complex.ofRealCLM.integral_comp_comm
        (φ := fun z => Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z) (hsliceKr y)]
    rw [boxCoreQ_mean_zero_snd_c2 hA hℓ hAc hvolAr hvolpos hM0 hΦ i j' r2 hM y,
      Complex.ofReal_zero]
  have hmy : ∀ z : E3, (∫ y, boxCoreKc volA A Φ i j' r2 y z
      ∂((volume : Measure E3).restrict A)) = 0 := by
    intro z
    rw [show (∫ y, boxCoreKc volA A Φ i j' r2 y z ∂((volume : Measure E3).restrict A))
        = (((∫ y in A, Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z) : ℝ) : ℂ) from
      Complex.ofRealCLM.integral_comp_comm
        (φ := fun y => Work.BoseFixB1.boxCoreQ volA A Φ i j' r2 y z) (hsliceKf z)]
    rw [boxCoreQ_mean_zero_fst_c2 hA hℓ hAc hvolAr hvolpos hM0 hΦ i j' r2 hM z,
      Complex.ofReal_zero]
  -- the four steps
  have hstep1 : (∫ q : E3 × E3, boxWinModeC volA A χ (-p) q.1 * boxWinModeC volA A χ p q.2
        * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)))
      = ∫ q : E3 × E3, (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
        * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    apply integral_congr_ae
    filter_upwards [haemem] with q hq
    rw [boxWinModeC_neg_eq p hq.1, boxWinModeC_pos_eq p hq.2]
  have hstep2 : (∫ q : E3 × E3, (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
        * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)))
      = ∫ q : E3 × E3, (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
        * boxCoreKc volA A Φ i j' r2 q.1 q.2
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    rw [← sub_eq_zero, ← MeasureTheory.integral_sub hintG1 hintG2]
    rw [show (∫ q : E3 × E3,
          ((boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
            * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
          - (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
            * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * boxCoreKc volA A Φ i j' r2 q.1 q.2)
          ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)))
        = ∫ q : E3 × E3,
            (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
              * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
              * ((coreMz volA A Φ i j' r2 q.2 + coreNy volA A Φ i j' r2 q.1 : ℝ) : ℂ)
          ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) from by
      apply integral_congr_ae
      filter_upwards [haemem] with q hq
      rw [show (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
            * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
          - (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
            * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * boxCoreKc volA A Φ i j' r2 q.1 q.2
          = (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
            * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * (((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)
                - boxCoreKc volA A Φ i j' r2 q.1 q.2) from by ring]
      rw [coreQ_decomp i j' r2 hq.1 hq.2]]
    rw [show (∫ q : E3 × E3,
          (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
            * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
            * ((coreMz volA A Φ i j' r2 q.2 + coreNy volA A Φ i j' r2 q.1 : ℝ) : ℂ)
          ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)))
        = ∫ q : E3 × E3,
            ((boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
                * ((boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
                    * ((coreMz volA A Φ i j' r2 q.2 : ℝ) : ℂ))
              + ((boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
                  * ((coreNy volA A Φ i j' r2 q.1 : ℝ) : ℂ))
                * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p)))
          ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) from by
      apply integral_congr_ae
      filter_upwards with q
      push_cast
      ring]
    rw [MeasureTheory.integral_add hintP1 hintP2]
    rw [MeasureTheory.integral_prod_mul
      (f := fun y : E3 => boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p))
      (g := fun z : E3 => (boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p))
        * ((coreMz volA A Φ i j' r2 z : ℝ) : ℂ))]
    rw [MeasureTheory.integral_prod_mul
      (f := fun y : E3 => (boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p))
        * ((coreNy volA A Φ i j' r2 y : ℝ) : ℂ))
      (g := fun z : E3 => boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p))]
    rw [hUmz, hVv]
    ring
  have hstep3 : (∫ q : E3 × E3, (boxCoreU χ p q.1 - boxCoreC volA A (boxCoreU χ p))
        * (boxCoreV χ p q.2 - boxCoreC volA A (boxCoreV χ p))
        * boxCoreKc volA A Φ i j' r2 q.1 q.2
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)))
      = ∫ q : E3 × E3, boxCoreU χ p q.1 * boxCoreV χ p q.2
        * boxCoreKc volA A Φ i j' r2 q.1 q.2
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    rw [MeasureTheory.integral_prod _ hintG2, MeasureTheory.integral_prod _ hintG3]
    exact Work.BoseFixB1.Core.coreAbstract (μ := (volume : Measure E3).restrict A)
      (K := fun y z => boxCoreKc volA A Φ i j' r2 y z)
      (u := fun y => boxCoreU χ p y) (v := fun z => boxCoreV χ p z)
      (C₁ := boxCoreC volA A (boxCoreU χ p)) (C₂ := boxCoreC volA A (boxCoreV χ p))
      hsliceK hsliceVK hvK huvK hmz hmy
  have hstep4 : (∫ q : E3 × E3, boxCoreU χ p q.1 * boxCoreV χ p q.2
        * boxCoreKc volA A Φ i j' r2 q.1 q.2
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)))
      = ∫ q : E3 × E3, (χ q.1 : ℂ) * (χ q.2 : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ p (q.1 - q.2) : ℝ) : ℂ))
        * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ))
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℂ)
        ∂(((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    apply integral_congr_ae
    filter_upwards with q
    have h1 : boxCoreKc volA A Φ i j' r2 q.1 q.2
        = ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ))
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℂ) := rfl
    rw [h1, ← boxCoreU_mul_boxCoreV χ p q.1 q.2]
  rw [Work.BoseFixB1.boxPairSlot]
  rw [← MeasureTheory.integral_prod (fun q : E3 × E3 =>
      boxWinModeC volA A χ (-p) q.1 * boxWinModeC volA A χ p q.2
        * ((Φ (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℝ) : ℂ)) hintF1]
  rw [← MeasureTheory.integral_prod (fun q : E3 × E3 =>
      (χ q.1 : ℂ) * (χ q.2 : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ p (q.1 - q.2) : ℝ) : ℂ))
        * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ))
            (Submission.BoseGases.ins2 i j' q.1 q.2 r2) : ℂ)) hintF4]
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

end Work.BoseFixB1.BoxPairIntGenC2
