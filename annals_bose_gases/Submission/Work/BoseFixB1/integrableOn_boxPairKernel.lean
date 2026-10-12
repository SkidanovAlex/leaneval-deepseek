import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Pair
import Submission.Work.BoseFixB1.WinPair.integrableOn_win_pair_box
import Submission.Work.BoseFixB1S.boxPQw_mass_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open scoped Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A real-valued continuous function with compact support is bounded in absolute value. -/
private lemma exists_abs_le_of_hasCompactSupport {f : E3 → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hf
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : |f x| ≤ C := by simpa [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

theorem integrableOn_boxPairKernel {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWint : MeasureTheory.Integrable W)
    {i j : Fin (N + 2)} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (N + 2) =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        * (χ (x i) * χ (x j) * W (x i - x j)))
      (Submission.BoseGases.abox (N + 2) ℓ) MeasureTheory.volume := by
  have hΦcont : Continuous Φ := hΦc.continuous
  have hΦm : Measurable Φ := hΦcont.measurable
  -- a bound for `Φ` on the analysis box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (N + 2) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (N + 2) ℓ) (f := Φ) hΦcont.continuousOn
  have hCΦ : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ, |Φ x| ≤ C :=
    fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  -- a bound for the window `χ`
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_abs_le_of_hasCompactSupport hχc.continuous hχs
  -- normalise both bounds to be nonnegative
  obtain ⟨B, hB0, hΦB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Φ x| ≤ B :=
    ⟨max C 0, le_max_right _ _, fun x hx => (hCΦ x hx).trans (le_max_left _ _)⟩
  obtain ⟨Cc, hCc0, hχb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, |χ z| ≤ C :=
    ⟨max Cχ 0, le_max_right _ _, fun z => (hCχ z).trans (le_max_left _ _)⟩
  have hvolreal : volA = MeasureTheory.volume.real A := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  -- the two box projections are bounded on the box
  have hP : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| ≤ B :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hA hvolA hAc i
      (fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hA hvolA hAc j hΦB x hx)
  have hQ : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * B := by
    have h1 : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
        |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * B :=
      Work.BoseFixB1S.abs_boxQInd_le hℓ hvolpos hA hvolreal hAc i hΦB
    have h2 : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
        |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 2 * (2 * B) :=
      Work.BoseFixB1S.abs_boxQInd_le (N := N + 2) hℓ hvolpos hA hvolreal hAc j h1
    intro x hx
    have h3 := h2 x hx
    linarith
  -- the dominating function `K·|W(xᵢ − xⱼ)|` is integrable on the box
  set K : ℝ := B * (4 * B) * (Cc * Cc) with hKdef
  have hbase : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (N + 2) =>
      |W (x i - x j)|) (Submission.BoseGases.abox (N + 2) ℓ) MeasureTheory.volume :=
    Submission.BoseGases.integrableOn_abs_sub_abox hℓ hWint i j hij
  have hmaj : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X (N + 2) => K * |W (x i - x j)|)
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X (N + 2))).restrict
        (Submission.BoseGases.abox (N + 2) ℓ)) :=
    MeasureTheory.Integrable.const_mul hbase K
  -- measurability of the integrand
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i
      (Work.UBBInputs8.boxPInd volA A j Φ)) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i
      (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm)
  have hQm : Measurable (Work.UBBInputs8.boxQInd volA A j
      (Work.UBBInputs8.boxQInd volA A i Φ)) :=
    Work.BoseFixB1S.measurable_boxQInd volA hA j
      (Work.BoseFixB1S.measurable_boxQInd volA hA i hΦm)
  have hχim : Measurable (fun x : Submission.BoseGases.X (N + 2) => χ (x i)) :=
    hχc.continuous.measurable.comp (measurable_pi_apply i)
  have hχjm : Measurable (fun x : Submission.BoseGases.X (N + 2) => χ (x j)) :=
    hχc.continuous.measurable.comp (measurable_pi_apply j)
  have hWaesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (N + 2) => W (x i - x j))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X (N + 2))).restrict
        (Submission.BoseGases.abox (N + 2) ℓ)) :=
    (Work.BoseFixB1.WinPair.aemeasurable_comp_pair hℓ hWint.aemeasurable i j hij).aestronglyMeasurable
  have haesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X (N + 2) =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          * (χ (x i) * χ (x j) * W (x i - x j)))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X (N + 2))).restrict
        (Submission.BoseGases.abox (N + 2) ℓ)) :=
    (hPm.aestronglyMeasurable.mul hQm.aestronglyMeasurable).mul
      ((hχim.aestronglyMeasurable.mul hχjm.aestronglyMeasurable).mul hWaesm)
  -- the pointwise domination
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable (N + 2) ℓ)] with x hx
  have h1 := hP x hx
  have h2 := hQ x hx
  have h3 := hχb (x i)
  have h4 := hχb (x j)
  have hb1 : (0 : ℝ) ≤ B * (4 * B) := mul_nonneg hB0 (by linarith)
  have hb2 : (0 : ℝ) ≤ Cc * Cc * |W (x i - x j)| :=
    mul_nonneg (mul_nonneg hCc0 hCc0) (abs_nonneg _)
  have hb3 : (0 : ℝ) ≤ |W (x i - x j)| := abs_nonneg _
  rw [Real.norm_eq_abs]
  calc |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          * (χ (x i) * χ (x j) * W (x i - x j))|
      = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x|
          * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x|
          * (|χ (x i)| * |χ (x j)| * |W (x i - x j)|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
    _ ≤ B * (4 * B) * (Cc * Cc * |W (x i - x j)|) :=
        mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hB0)
          (mul_le_mul_of_nonneg_right (mul_le_mul h3 h4 (abs_nonneg _) hCc0) hb3)
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)) hb1
    _ = K * |W (x i - x j)| := by rw [hKdef]; ring

end Work.BoseFixB1
