import Mathlib
import Submission.Work.Analysis.CzShift.Defs
import Submission.Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d_banach

namespace Work.Analysis.CzShift

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval Topology

/-- For `a ≤ b`, a set integral over `Ioo a b` is the corresponding interval integral. -/
lemma setIntegral_Ioo_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → E) :
    ∫ x in Set.Ioo a b, f x = ∫ x in a..b, f x := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]

/-- The `toReal`-volume of `Ioo a b` for `a ≤ b`. -/
lemma volumeReal_Ioo (a b : ℝ) (hab : a ≤ b) :
    (volume : Measure ℝ).real (Set.Ioo a b) = b - a := by
  rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- The one-dimensional vector-valued Calderón--Zygmund decomposition, with the extra
conclusions needed for the weak-type `(1,1)` bound of Theorem `cz-shift`: `g` is integrable with
`∫‖g‖ ≤ 2∫‖f‖` and `∫⁻‖g‖² ≤ 4α∫‖f‖`, and each bad function has mean zero on its interval.

The base decomposition is available in this repository as
`Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d_banach`
(module `Submission.Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d_banach`);
the work here is extracting the additional conclusions. -/
theorem cz_decomp_1d_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) (hf : MeasureTheory.Integrable f) (α : ℝ) (hα : 0 < α) :
    ∃ (A c : ℕ → ℝ) (g : ℝ → E) (b : ℕ → ℝ → E),
      (∀ j, A j ≤ c j) ∧
      (∀ j k, j ≠ k → Disjoint (Set.Ioo (A j) (c j)) (Set.Ioo (A k) (c k))) ∧
      (∀ j, α * (c j - A j) ≤ ∫ x in (A j)..(c j), ‖f x‖) ∧
      (∀ j, ∫ x in (A j)..(c j), ‖f x‖ ≤ 2 * α * (c j - A j)) ∧
      (∀ j, ∀ x, b j x = if x ∈ Set.Ioo (A j) (c j)
          then f x - (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) else 0) ∧
      (∀ x, x ∉ ⋃ j, Set.Ioo (A j) (c j) → g x = f x) ∧
      (∀ j, ∀ x ∈ Set.Ioo (A j) (c j), g x = (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t)) ∧
      (∀ᵐ x ∂MeasureTheory.volume, x ∉ ⋃ j, Set.Ioo (A j) (c j) → ‖f x‖ ≤ α) ∧
      (∀ᵐ x ∂MeasureTheory.volume, ‖g x‖ ≤ 2 * α) ∧
      (MeasureTheory.volume (⋃ j, Set.Ioo (A j) (c j))
          ≤ ENNReal.ofReal (α⁻¹ * ∫ x, ‖f x‖)) ∧
      (∀ᵐ x ∂MeasureTheory.volume, f x = g x + ∑' j, b j x) ∧
      MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume ∧
      (∫ x, ‖g x‖ ≤ 2 * ∫ x, ‖f x‖) ∧
      (∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ≤ ENNReal.ofReal (4 * α * ∫ x, ‖f x‖)) ∧
      (∀ j, ∫ x in (A j)..(c j), ‖b j x‖ ≤ 2 * ∫ x in (A j)..(c j), ‖f x‖) ∧
      (∀ j, ∫ x in Set.Ioo (A j) (c j), b j x = 0) := by
  classical
  obtain ⟨A, c, g, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d_banach f hf α hα
  have hfn : Integrable (fun x => ‖f x‖) volume := hf.norm
  -- ### abbreviations
  set avg : ℕ → E := fun j => (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) with havg
  have havg_apply : ∀ j, avg j = (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) := fun j => by rw [havg]
  set U : Set ℝ := ⋃ j, Set.Ioo (A j) (c j) with hUdef
  have hUmem : ∀ x, x ∈ U ↔ ∃ j, x ∈ Set.Ioo (A j) (c j) := by
    intro x; rw [hUdef]; exact Set.mem_iUnion
  have hUmeas : MeasurableSet U := by
    rw [hUdef]; exact MeasurableSet.iUnion (fun j => measurableSet_Ioo)
  have hdisj : Pairwise (Function.onFun Disjoint (fun j => Set.Ioo (A j) (c j))) :=
    fun i j hij => h2 i j hij
  have hUfin : volume U ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ h10
    exact ENNReal.ofReal_ne_top
  -- ### pointwise structure of the bad functions
  have hb_dflt : ∀ j x, b j x = if x ∈ Set.Ioo (A j) (c j) then f x - avg j else 0 :=
    fun j x => by simpa only [havg_apply j] using h5 j x
  have h7avg : ∀ j x, x ∈ Set.Ioo (A j) (c j) → g x = avg j :=
    fun j x hx => by simpa only [havg_apply j] using h7 j x hx
  have hnotI : ∀ x j, x ∉ Set.Ioo (A j) (c j) → b j x = 0 := by
    intro x j hx; rw [hb_dflt j x, if_neg hx]
  have huniq : ∀ x j k, x ∈ Set.Ioo (A j) (c j) → x ∈ Set.Ioo (A k) (c k) → j = k := by
    intro x j k hj hk
    by_contra hne
    exact (Set.disjoint_left.mp (h2 j k hne)) hj hk
  have htsum_eq : ∀ x j, x ∈ Set.Ioo (A j) (c j) → (∑' k, b k x) = b j x := by
    intro x j hj
    exact tsum_eq_single j (fun k hk => hnotI x k (fun hmem => hk (huniq x k j hmem hj)))
  have htsum_zero : ∀ x, x ∉ U → (∑' k, b k x) = 0 := by
    intro x hx
    rw [tsum_congr (fun k => hnotI x k (fun hmem => hx ((hUmem x).mpr ⟨k, hmem⟩))), tsum_zero]
  have hconv : ∀ x, Tendsto (fun n => (∑ j ∈ Finset.range n, b j) x) atTop (𝓝 (∑' j, b j x)) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨j₀, hj₀⟩ := (hUmem x).mp hx
      have hz : ∀ k, k ≠ j₀ → b k x = 0 :=
        fun k hk => hnotI x k (fun hmem => hk (huniq x k j₀ hmem hj₀))
      have hhs : HasSum (fun k => b k x) (b j₀ x) := hasSum_single j₀ hz
      rw [htsum_eq x j₀ hj₀]
      simpa only [Finset.sum_apply] using hhs.tendsto_sum_nat
    · have hz : ∀ k, b k x = 0 := fun k => hnotI x k (fun hmem => hx ((hUmem x).mpr ⟨k, hmem⟩))
      have htz : (∑' k, b k x) = 0 := by rw [tsum_congr hz, tsum_zero]
      rw [htz]
      have hzero : (fun n : ℕ => (∑ j ∈ Finset.range n, b j) x) = fun _ => (0 : E) := by
        funext n
        simpa only [Finset.sum_apply] using Finset.sum_eq_zero (fun j _ => hz j)
      rw [hzero]
      exact tendsto_const_nhds
  have hpt : ∀ x, g x = f x - ∑' j, b j x := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨j₀, hj₀⟩ := (hUmem x).mp hx
      have hw : b j₀ x = f x - avg j₀ := by rw [hb_dflt j₀ x, if_pos hj₀]
      rw [htsum_eq x j₀ hj₀, hw, h7avg j₀ x hj₀]
      abel
    · rw [htsum_zero x hx, sub_zero]
      exact h6 x hx
  -- ### measurability of `g`
  have hb_meas : ∀ j, AEStronglyMeasurable (b j) volume := by
    intro j
    have hh : b j = fun x => (Set.Ioo (A j) (c j)).indicator (fun y => f y - avg j) x := by
      funext x
      rw [hb_dflt j x]
      by_cases hx : x ∈ Set.Ioo (A j) (c j)
      · rw [if_pos hx, Set.indicator_of_mem hx]
      · rw [if_neg hx, Set.indicator_of_notMem hx]
    rw [hh]
    exact ((hf.aestronglyMeasurable.sub aestronglyMeasurable_const).indicator measurableSet_Ioo)
  have hSmeas : AEStronglyMeasurable (fun x => ∑' j, b j x) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x => (∑ j ∈ Finset.range n, b j) x)
      (fun n => Finset.aestronglyMeasurable_sum (Finset.range n) (fun j _ => hb_meas j))
      (Filter.Eventually.of_forall hconv)
  have h12 : AEStronglyMeasurable g volume := by
    refine (hf.aestronglyMeasurable.sub hSmeas).congr ?_
    filter_upwards with x
    exact (hpt x).symm
  -- ### integrability of `‖g‖`
  have hUind : Integrable (U.indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hUmeas]
    exact integrableOn_const (C := (1 : ℝ)) hUfin enorm_ne_top
  have hIntg : Integrable (fun x => ‖g x‖) volume := by
    refine Integrable.mono' (hfn.add (hUind.const_mul (2 * α))) h12.norm ?_
    filter_upwards [h9] with x hx9
    show ‖‖g x‖‖ ≤ ‖f x‖ + 2 * α * U.indicator (fun _ : ℝ => (1 : ℝ)) x
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU, mul_one, norm_norm]
      linarith [hx9, norm_nonneg (f x)]
    · rw [Set.indicator_of_notMem hxU, mul_zero, add_zero, norm_norm, h6 x hxU]
  -- ### the key estimate for one interval
  have havg_le : ∀ j, (c j - A j) * ‖avg j‖ ≤ ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := by
    intro j
    by_cases hAc : c j = A j
    · rw [hAc, sub_self, zero_mul, Set.Ioo_self, MeasureTheory.setIntegral_empty]
    · have hlt : A j < c j := lt_of_le_of_ne (h1 j) (Ne.symm hAc)
      have hpos : 0 < c j - A j := sub_pos.mpr hlt
      rw [setIntegral_Ioo_eq_intervalIntegral (A j) (c j) (h1 j) (fun x => ‖f x‖), havg_apply j]
      calc (c j - A j) * ‖(c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t)‖
          = (c j - A j) * ((c j - A j)⁻¹ * ‖∫ t in (A j)..(c j), f t‖) := by
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
        _ ≤ (c j - A j) * ((c j - A j)⁻¹ * ∫ t in (A j)..(c j), ‖f t‖) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (intervalIntegral.norm_integral_le_integral_norm (le_of_lt hlt))
                (le_of_lt (inv_pos.mpr hpos))) (le_of_lt hpos)
        _ = ∫ t in (A j)..(c j), ‖f t‖ := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
  -- ### the `L¹` bound on the good function
  have h13 : ∫ x, ‖g x‖ ≤ 2 * ∫ x, ‖f x‖ := by
    have hUle : (∫ x in U, ‖g x‖) ≤ ∫ x in U, ‖f x‖ := by
      have h1' : (∫ x in U, ‖g x‖) = ∑' j, ∫ x in Set.Ioo (A j) (c j), ‖g x‖ := by
        rw [hUdef]
        exact integral_iUnion (fun j => measurableSet_Ioo) hdisj hIntg.integrableOn
      have h2' : (∫ x in U, ‖f x‖) = ∑' j, ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := by
        rw [hUdef]
        exact integral_iUnion (fun j => measurableSet_Ioo) hdisj hfn.integrableOn
      rw [h1', h2']
      refine Summable.tsum_le_tsum (fun j => ?_) ?_ ?_
      · calc (∫ x in Set.Ioo (A j) (c j), ‖g x‖)
            = ∫ x in Set.Ioo (A j) (c j), ‖avg j‖ := by
              apply setIntegral_congr_fun measurableSet_Ioo
              intro x hx
              show ‖g x‖ = ‖avg j‖
              rw [h7avg j x hx]
          _ = (c j - A j) * ‖avg j‖ := by
              rw [setIntegral_const, smul_eq_mul, volumeReal_Ioo (A j) (c j) (h1 j)]
          _ ≤ ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := havg_le j
      · exact (hasSum_integral_iUnion (fun j => measurableSet_Ioo) hdisj hIntg.integrableOn).summable
      · exact (hasSum_integral_iUnion (fun j => measurableSet_Ioo) hdisj hfn.integrableOn).summable
    have hcompl : (∫ x in Uᶜ, ‖g x‖) = ∫ x in Uᶜ, ‖f x‖ := by
      apply setIntegral_congr_fun hUmeas.compl
      intro x hx
      show ‖g x‖ = ‖f x‖
      rw [h6 x hx]
    calc (∫ x, ‖g x‖)
        = (∫ x in U, ‖g x‖) + ∫ x in Uᶜ, ‖g x‖ := (integral_add_compl hUmeas hIntg).symm
      _ ≤ (∫ x in U, ‖f x‖) + ∫ x in Uᶜ, ‖f x‖ := add_le_add hUle (le_of_eq hcompl)
      _ = ∫ x, ‖f x‖ := integral_add_compl hUmeas hfn
      _ ≤ 2 * ∫ x, ‖f x‖ := by
          have h0 : (0 : ℝ) ≤ ∫ x, ‖f x‖ := integral_nonneg (fun x => norm_nonneg (f x))
          linarith
  -- ### the `L²` (lintegral) bound on the good function
  have h14 : ∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ≤ ENNReal.ofReal (4 * α * ∫ x, ‖f x‖) := by
    have hmeas_g : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable h12.norm.aemeasurable
    have hfin : (∫⁻ x, ENNReal.ofReal ‖g x‖) = ENNReal.ofReal (∫ x, ‖g x‖) :=
      (ofReal_integral_eq_lintegral_ofReal hIntg
        (Eventually.of_forall (fun x => norm_nonneg (g x)))).symm
    calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ)
        = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
          apply lintegral_congr
          intro x
          rw [show ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) = ENNReal.ofReal ‖g x‖ ^ (2 : ℕ)
                from ENNReal.rpow_natCast _ 2,
              ENNReal.ofReal_pow (norm_nonneg (g x))]
      _ ≤ ∫⁻ x, ENNReal.ofReal (2 * α * ‖g x‖) := by
          apply lintegral_mono_ae
          filter_upwards [h9] with x hx
          apply ENNReal.ofReal_le_ofReal
          calc ‖g x‖ ^ 2 = ‖g x‖ * ‖g x‖ := by ring
            _ ≤ (2 * α) * ‖g x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ = ENNReal.ofReal (2 * α) * ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
          rw [← lintegral_const_mul'' (ENNReal.ofReal (2 * α)) hmeas_g]
          apply lintegral_congr
          intro x
          exact ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * α)
      _ ≤ ENNReal.ofReal (4 * α * ∫ x, ‖f x‖) := by
          rw [hfin, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * α)]
          apply ENNReal.ofReal_le_ofReal
          calc 2 * α * ∫ x, ‖g x‖ ≤ 2 * α * (2 * ∫ x, ‖f x‖) :=
                mul_le_mul_of_nonneg_left h13 (by linarith)
            _ = 4 * α * ∫ x, ‖f x‖ := by ring
  -- ### the bad functions
  have h15set : ∀ j, (∫ x in Set.Ioo (A j) (c j), ‖b j x‖)
      ≤ 2 * ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := by
    intro j
    have hsmeas : MeasurableSet (Set.Ioo (A j) (c j)) := measurableSet_Ioo
    have hfinj : volume (Set.Ioo (A j) (c j)) ≠ ∞ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hIf : IntegrableOn (fun x => ‖f x‖) (Set.Ioo (A j) (c j)) volume := hfn.integrableOn
    have hIc : IntegrableOn (fun _ : ℝ => ‖avg j‖) (Set.Ioo (A j) (c j)) volume :=
      integrableOn_const (C := ‖avg j‖) hfinj enorm_ne_top
    have hIv : IntegrableOn (fun _ : ℝ => avg j) (Set.Ioo (A j) (c j)) volume :=
      integrableOn_const (C := avg j) hfinj enorm_ne_top
    have hIg : IntegrableOn (fun x => ‖f x - avg j‖) (Set.Ioo (A j) (c j)) volume :=
      (hf.integrableOn.sub hIv).norm
    have hIsum : IntegrableOn (fun x => ‖f x‖ + ‖avg j‖) (Set.Ioo (A j) (c j)) volume :=
      hIf.add hIc
    calc (∫ x in Set.Ioo (A j) (c j), ‖b j x‖)
        = ∫ x in Set.Ioo (A j) (c j), ‖f x - avg j‖ := by
          apply setIntegral_congr_fun hsmeas
          intro x hx
          show ‖b j x‖ = ‖f x - avg j‖
          rw [hb_dflt j x, if_pos hx]
      _ ≤ ∫ x in Set.Ioo (A j) (c j), (‖f x‖ + ‖avg j‖) :=
          setIntegral_mono_ae hIg hIsum (Eventually.of_forall (fun x => norm_sub_le _ _))
      _ = (∫ x in Set.Ioo (A j) (c j), ‖f x‖) + ∫ x in Set.Ioo (A j) (c j), ‖avg j‖ :=
          integral_add hIf hIc
      _ = (∫ x in Set.Ioo (A j) (c j), ‖f x‖) + (c j - A j) * ‖avg j‖ := by
          rw [setIntegral_const, smul_eq_mul, volumeReal_Ioo (A j) (c j) (h1 j)]
      _ ≤ (∫ x in Set.Ioo (A j) (c j), ‖f x‖) + ∫ x in Set.Ioo (A j) (c j), ‖f x‖ :=
          add_le_add le_rfl (havg_le j)
      _ = 2 * ∫ x in Set.Ioo (A j) (c j), ‖f x‖ := by ring
  have h15 : ∀ j, (∫ x in (A j)..(c j), ‖b j x‖) ≤ 2 * ∫ x in (A j)..(c j), ‖f x‖ := by
    intro j
    rw [← setIntegral_Ioo_eq_intervalIntegral (A j) (c j) (h1 j) (fun x => ‖b j x‖),
      ← setIntegral_Ioo_eq_intervalIntegral (A j) (c j) (h1 j) (fun x => ‖f x‖)]
    exact h15set j
  have h16 : ∀ j, (∫ x in Set.Ioo (A j) (c j), b j x) = 0 := by
    intro j
    by_cases hAc : c j = A j
    · have hnil : Set.Ioo (A j) (c j) = ∅ := by rw [hAc, Set.Ioo_self]
      simp [hnil]
    · have hlt : A j < c j := lt_of_le_of_ne (h1 j) (Ne.symm hAc)
      have hpos : 0 < c j - A j := sub_pos.mpr hlt
      rw [setIntegral_Ioo_eq_intervalIntegral (A j) (c j) (h1 j) (b j)]
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (A j) (c j) → b j x = f x - avg j := by
        have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c j := by
          rw [MeasureTheory.ae_iff]
          simp
        filter_upwards [hne] with x hxne hmem
        rw [Set.uIoc_of_le (h1 j)] at hmem
        rw [hb_dflt j x, if_pos ⟨hmem.1, lt_of_le_of_ne hmem.2 hxne⟩]
      rw [intervalIntegral.integral_congr_ae hae,
        intervalIntegral.integral_sub (hf.intervalIntegrable) (intervalIntegrable_const (c := avg j)),
        intervalIntegral.integral_const, havg_apply j]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul, sub_self]
  exact ⟨A, c, g, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

end Work.Analysis.CzShift
