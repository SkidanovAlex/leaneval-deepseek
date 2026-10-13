import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.integral_finset_sum_le
import Submission.Work.EllipticEst.Core.HkSqLHSv2Pointwise
import Submission.Work.EllipticEst.Core.HkSqLHSv2Meas
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice-level reduction for `HkSqLHS_le_summands_v2`

For a fixed `z`, the iterated-integral definition of `HkSq` reduces, at the level of the
angular integral, to the sum of the summands appearing in `HkSqLHS_le_summands_v2`:

`∫_θ HkIntegrand α k (α • D_z∂_θV) z θ ≤ α² (∑_r mixIntS(D_z^rV)(z) + ∑_{i,j} mixedIntS α i j V (z))`.

The proof is

* `v2_zBlock_ae`, `v2_mixedBlock_ae` (a.e. identification of the two blocks of `HkIntegrand`);
* `integral_add_le_nonneg` and `integral_finset_sum_le` subadditivity of the Bochner integral
  for nonnegative a.e.-measurable functions (this is where the `AEMeasurable` facts
  `v2_aesm_zSummand`, `v2_aesm_mSummand` are consumed, and where the junk-value convention of
  the Bochner integral is used in the helpful direction);
* `v2_sliceId`, `v2_mixedId` identification of the single-slice integrals with `mixIntS`,
  `mixedIntS`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-! ## Subadditivity of the Bochner integral, two-term case -/

/-- `∫ (f + g) ≤ ∫ f + ∫ g` for nonnegative a.e.-measurable functions (the two-term case of
`integral_finset_sum_le`). -/
theorem integral_add_le_nonneg {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ a, (f a + g a) ∂μ ≤ ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  have h := integral_finset_sum_le (μ := μ) (s := Finset.range 2) (ι := ℕ)
    (f := fun i : ℕ => fun a => if i = 0 then f a else g a) ?hm ?hn
  · have h1 : ∀ a, (∑ i ∈ Finset.range 2, (if i = 0 then f a else g a)) = f a + g a := by
      intro a
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    have h2 : (∑ i ∈ Finset.range 2, ∫ a, (if i = 0 then f a else g a) ∂μ)
        = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1), h2] at h
    exact h
  · intro i _
    by_cases hi : i = 0
    · simpa only [hi, if_true] using hf
    · simpa only [if_neg hi] using hg
  · intro i _
    by_cases hi : i = 0
    · simpa only [hi, if_true] using hf0
    · simpa only [if_neg hi] using hg0

/-- A finite sum of a.e.-measurable real functions is a.e.-measurable, in the pointwise form
`a ↦ ∑ i ∈ s, f i a`. -/
theorem aemeasurable_finset_sum_apply {ι α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s : Finset ι} {f : ι → α → ℝ}
    (h : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∑ i ∈ s, f i a) μ := by
  have hmain : AEMeasurable (∑ i ∈ s, f i) μ := Finset.aemeasurable_sum s h
  refine (aemeasurable_congr ?_).mpr hmain
  exact Filter.Eventually.of_forall (fun a => by simp only [Finset.sum_apply])

/-! ## The single-slice identifications -/

/-- The `θ`-integral of one pure `D_z`-summand is the corresponding `mixIntS`. -/
theorem v2_sliceId (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = mixIntS u z := by
  show _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))

/-- The `θ`-integral of one mixed summand is the corresponding `mixedIntS`. -/
theorem v2_mixedId (α : ℝ) (i j : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
      = mixedIntS α i j u z := by
  show _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth u) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))

/-! ## Measurability and nonnegativity of the blocks -/

/-- The pure `D_z` block is a.e. strongly measurable as a function of `θ`. -/
theorem v2_aesm_zSummand {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  exact aemeasurable_finset_sum_apply (fun r _ => by
    simpa only [Work.FTS.EllipticEst.thEta] using
      v2_aesm_slice ((hV.DzIter r).pth.Dz) (-(Work.Spaces.eta)) z hz)

/-- The mixed block is a.e. strongly measurable as a function of `θ`. -/
theorem v2_aesm_mSummand {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (α : ℝ)
    (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  exact aemeasurable_finset_sum_apply (fun i _ => aemeasurable_finset_sum_apply (fun j _ => by
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      simpa only [Work.FTS.EllipticEst.thGam] using
        v2_aesm_slice ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α)) z hz
    · simp only [if_neg hc]
      exact aemeasurable_const))

/-- The pure `D_z` block is nonnegative a.e. -/
theorem v2_nn_zSummand (k : ℕ) {V : ℝ → ℝ → ℝ} (z : ℝ) :
    0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  refine Finset.sum_nonneg (fun r _ => ?_)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Work.FTS.EllipticEst.thEta_nonneg hθ)

/-- The mixed block is nonnegative a.e. -/
theorem v2_nn_mSummand (α : ℝ) (k : ℕ) {V : ℝ → ℝ → ℝ} (z : ℝ) :
    0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0) := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [if_pos hc]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thGam_nonneg hθ)
  · simp only [if_neg hc]
    exact le_refl 0

/-! ## The two blocks of the slice inequality -/

/-- The pure `D_z` block of the slice inequality. -/
theorem v2_zSlice_le (k : ℕ) {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z := by
  intro z hz
  refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (s := Finset.range (k + 1)) (f := fun r : ℕ => fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) ?_ ?_) ?_
  · intro r _
    simpa only [Work.FTS.EllipticEst.thEta] using
      v2_aesm_slice ((hV.DzIter r).pth.Dz) (-(Work.Spaces.eta)) z hz
  · intro r _
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  · exact Finset.sum_le_sum (fun r _ => le_of_eq (v2_sliceId (Work.Spaces.DzIter r V) z))

/-- The mixed block of the slice inequality. -/
theorem v2_mSlice_le (k : ℕ) {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0 := by
  intro z hz
  refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (s := Finset.range (k + 1)) (f := fun i : ℕ => fun θ : ℝ =>
      ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
        else 0) ?_ ?_) ?_
  · intro i _
    exact aemeasurable_finset_sum_apply (fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        simpa only [Work.FTS.EllipticEst.thGam] using
          v2_aesm_slice ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α)) z hz
      · simp only [if_neg hc]
        exact aemeasurable_const)
  · intro i _
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    refine Finset.sum_nonneg (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Work.FTS.EllipticEst.thGam_nonneg hθ)
    · simp only [if_neg hc]
      exact le_refl 0
  · refine Finset.sum_le_sum (fun i _ => ?_)
    refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (s := Finset.range (k + 1)) (f := fun j : ℕ => fun θ : ℝ =>
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
        else 0) ?_ ?_) ?_
    · intro j _
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        simpa only [Work.FTS.EllipticEst.thGam] using
          v2_aesm_slice ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α)) z hz
      · simp only [if_neg hc]
        exact aemeasurable_const
    · intro j _
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Work.FTS.EllipticEst.thGam_nonneg hθ)
      · simp only [if_neg hc]
        exact le_refl 0
    · refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact le_of_eq (v2_mixedId α i j V z)
      · simp only [if_neg hc]
        exact le_of_eq (MeasureTheory.integral_zero ℝ ℝ)

/-! ## The slice inequality -/

/-- **The slice-level reduction.**  For `0 < α`, `V` of class `C^∞` on the open quadrant and
`z ∈ [0,∞)`, the angular integral of `HkIntegrand α k (α • D_z∂_θV)` is bounded by `α²` times
the two families of summands of `HkSqLHS_le_summands_v2`. -/
theorem v2_slice_le (k : ℕ) {α : ℝ} {V : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)) := by
  intro z hz
  have h3a := v2_zBlock_ae (k := k) (α := α) (V := V) hV z hz
  have h3b := v2_mixedBlock_ae (k := k) (α := α) hα (V := V) hV z hz
  have hcomb : (fun θ : ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ =>
        α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
            else 0)) := by
    filter_upwards [h3a, h3b] with θ h1 h2
    simp only [Work.Spaces.HkIntegrand]
    beta_reduce at h1 h2
    rw [h1, h2]
  have hfac : (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                  * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
              else 0)))
      = α ^ 2 * ∫ θ in Work.Spaces.Iθ,
          ((∑ r ∈ Finset.range (k + 1),
              (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                    * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
                else 0)) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  rw [MeasureTheory.integral_congr_ae hcomb, hfac]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
  refine le_trans (integral_add_le_nonneg (v2_aesm_zSummand hV k z hz)
    (v2_aesm_mSummand hV α k z hz) (v2_nn_zSummand (V := V) k z)
    (v2_nn_mSummand α k (V := V) z)) ?_
  exact add_le_add (v2_zSlice_le k hV z hz) (v2_mSlice_le (α := α) k hV z hz)

end Work.EllipticEst.Core
