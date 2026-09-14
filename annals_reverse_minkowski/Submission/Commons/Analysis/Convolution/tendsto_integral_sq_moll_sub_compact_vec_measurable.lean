import Mathlib.MeasureTheory.Function.L2Space
import Submission.Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq
import Submission.Commons.Analysis.Convolution.tendsto_lintegral_translate_sub_vec
import Submission.Commons.Analysis.Convolution.aemeasurable_uncurry_ofReal_mul_enorm_sq
import Submission.Commons.Analysis.Measure.tendsto_iSup_closedBall_nhds_zero
import Submission.Commons.Measure.Integral.integral_smoothing_rpow_le_of_integrable

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal Pointwise

section Vec

variable {n m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)

/-- The squared `L²`-mass of a `MemLp 2` function into `ℝᵐ` is finite. -/
theorem lintegral_enorm_rpow_two_lt_top_vec {u : X → Y}
    (hu : MemLp u 2 (volume : Measure X)) :
    ∫⁻ z, ‖u z‖ₑ ^ (2:ℝ) < ⊤ := by
  have hInt : Integrable (fun z : X => ‖u z‖ ^ (2:ℝ)) (volume : Measure X) := by
    simpa using hu.integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
  have hfin : ∫⁻ z, ‖(‖u z‖ ^ (2:ℝ))‖ₑ < ⊤ :=
    MeasureTheory.hasFiniteIntegral_iff_enorm.mp hInt.2
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  apply lintegral_congr
  intro z
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) 2),
    show ‖u z‖ₑ = ENNReal.ofReal ‖u z‖ by simp [enorm],
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]

/-- **A.e.-measurability of the convolution integrand** (vector-valued). -/
theorem aemeasurable_uncurry_ofReal_mul_enorm_sq_vec {ρ : X → ℝ}
    (hρi : Integrable ρ (volume : Measure X)) (u : X → Y)
    (hu : MemLp u 2 (volume : Measure X)) :
    AEMeasurable (Function.uncurry fun x y : X =>
        ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ 2)
      ((volume : Measure X).prod (volume : Measure X)) := by
  have hρa : AEMeasurable ρ (volume : Measure X) := hρi.aestronglyMeasurable.aemeasurable
  have hua : AEMeasurable u (volume : Measure X) := hu.aestronglyMeasurable.aemeasurable
  have h1 : AEMeasurable (fun p : X × X => ENNReal.ofReal (ρ p.2))
      ((volume : Measure X).prod (volume : Measure X)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hρa.comp_snd
  have hT : Measurable (fun p : X × X => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hsurj : AEMeasurable u (((volume : Measure X).prod (volume : Measure X)).map
      (fun p : X × X => p.1 - p.2)) :=
    hua.mono' (map_sub_prod_absolutelyContinuous (E := X))
  have h2 : AEMeasurable (fun p : X × X => u (p.1 - p.2))
      ((volume : Measure X).prod (volume : Measure X)) :=
    hsurj.comp_aemeasurable' hT.aemeasurable
  have h3 : AEMeasurable (fun p : X × X => u p.1)
      ((volume : Measure X).prod (volume : Measure X)) := hua.comp_fst
  have h5 : AEMeasurable (fun p : X × X => ‖u (p.1 - p.2) - u p.1‖ₑ)
      ((volume : Measure X).prod (volume : Measure X)) := (h2.sub h3).enorm
  have h6 : AEMeasurable (fun p : X × X => ‖u (p.1 - p.2) - u p.1‖ₑ ^ 2)
      ((volume : Measure X).prod (volume : Measure X)) := h5.pow_const 2
  exact h1.mul h6

/-- For `ρ ∈ L¹` and `u ∈ L²`, the weighted `L²`-mass of `u` is finite for a.e. `x`. -/
theorem ae_lintegral_enorm_mul_enorm_rpow_two_lt_top_vec {ρ : X → ℝ} {u : X → Y}
    (hρi : Integrable ρ (volume : Measure X)) (hu : MemLp u 2 (volume : Measure X)) :
    ∀ᵐ x ∂(volume : Measure X),
      (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ)) < ⊤ := by
  set F : X → ℝ≥0∞ := fun x => ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ) with hFdef
  have hΦ : AEMeasurable (Function.uncurry fun (x y : X) =>
      ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ)) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : X × X => ‖ρ p.2‖ₑ) (volume.prod volume) :=
      hρi.aestronglyMeasurable.enorm.comp_snd
    have h2 : AEMeasurable (fun p : X × X => ‖u (p.1 - p.2)‖ₑ) (volume.prod volume) :=
      (hu.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    exact h1.mul (h2.pow_const (2:ℝ))
  have hFae : AEMeasurable F volume := by
    rw [hFdef]; exact hΦ.lintegral_prod_right'
  have hInt : ∫⁻ x, F x ∂volume < ⊤ := by
    rw [hFdef]
    rw [lintegral_lintegral_swap hΦ]
    have hinner : ∀ y : X,
        (∫⁻ x, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ))
          = ‖ρ y‖ₑ * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) := by
      intro y
      rw [lintegral_const_mul'']
      · congr 1
        exact lintegral_sub_right_eq_self (fun z => ‖u z‖ₑ ^ (2:ℝ)) y
      · exact (hu.aestronglyMeasurable.enorm.pow_const (2:ℝ)).comp_quasiMeasurePreserving
          (by simpa [sub_eq_add_neg] using
            (measurePreserving_add_right volume (-y)).quasiMeasurePreserving)
    simp_rw [hinner]
    calc ∫⁻ y, ‖ρ y‖ₑ * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ))
        = (∫⁻ y, ‖ρ y‖ₑ) * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) :=
          lintegral_mul_const'' _ hρi.aestronglyMeasurable.enorm
      _ < ⊤ := ENNReal.mul_lt_top hρi.2 (lintegral_enorm_rpow_two_lt_top_vec hu)
  exact ae_lt_top' hFae (ne_of_lt hInt)

/-- If `ρ ∈ L¹` and `u ∈ L²`, then `y ↦ ρ y • u (x - y)` is Bochner integrable for a.e. `x`. -/
theorem ae_integrable_smul_convolution_vec {ρ : X → ℝ} {u : X → Y}
    (hρi : Integrable ρ (volume : Measure X)) (hu : MemLp u 2 (volume : Measure X)) :
    ∀ᵐ x ∂(volume : Measure X), Integrable (fun y => ρ y • u (x - y)) (volume : Measure X) := by
  filter_upwards [ae_lintegral_enorm_mul_enorm_rpow_two_lt_top_vec hρi hu] with x hx
  have hsub : AEStronglyMeasurable (fun y : X => u (x - y)) (volume : Measure X) :=
    hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  refine ⟨hρi.aestronglyMeasurable.smul hsub, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hfa : AEMeasurable (fun y : X => ‖u (x - y)‖ₑ) (volume : Measure X) := hsub.enorm
  have hga : AEMeasurable (fun y : X => ‖ρ y‖ₑ) (volume : Measure X) :=
    hρi.aestronglyMeasurable.enorm
  have hCS := Commons.Measure.Integral.lintegral_mul_pow_le (ν := (volume : Measure X)) (q := 2)
    (by norm_num) hfa hga
  rw [show (∫⁻ y, ‖u (x - y)‖ₑ * ‖ρ y‖ₑ) = ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ from
        lintegral_congr fun y => mul_comm _ _,
      show (∫⁻ y, ‖u (x - y)‖ₑ ^ (2:ℝ) * ‖ρ y‖ₑ)
        = ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ) from
        lintegral_congr fun y => mul_comm _ _,
      show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hCS
  have hbound : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) ^ (2:ℝ) < ⊤ :=
    lt_of_le_of_lt hCS (ENNReal.mul_lt_top hx hρi.2)
  have hfin' : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) < ⊤ := by
    by_contra hc
    rw [not_lt] at hc
    have htop : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) = ⊤ := top_le_iff.mp hc
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hbound
    exact lt_irrefl _ hbound
  exact lt_of_eq_of_lt (lintegral_congr fun y => by rw [enorm_smul]) hfin'

/-- **Convolution is close to the identity in a weighted `L²` sense** (vector-valued). -/
theorem enorm_convolution_sub_le_vec {ρ : X → ℝ}
    (hρnn : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ (volume : Measure X))
    (hρ1 : ∫ x, ρ x ∂(volume : Measure X) = 1)
    (u : X → Y) (hu : MemLp u 2 (volume : Measure X)) :
    ∀ᵐ x ∂(volume : Measure X),
      ‖(∫ y, ρ y • u (x - y) ∂(volume : Measure X)) - u x‖ₑ ^ 2
        ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ 2 ∂(volume : Measure X) := by
  filter_upwards [ae_integrable_smul_convolution_vec hρi hu] with x hx
  have hconst : ∫ y, ρ y • u x ∂(volume : Measure X) = u x := by
    rw [integral_smul_const, hρ1, one_smul]
  have hsplit : (∫ y, ρ y • u (x - y) ∂(volume : Measure X)) - u x
      = ∫ y, ρ y • (u (x - y) - u x) ∂(volume : Measure X) := by
    conv_lhs => rw [← hconst]
    rw [← integral_sub hx (hρi.smul_const (u x))]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_sub]
  rw [hsplit]
  have hD : ‖∫ y, ρ y • (u (x - y) - u x) ∂(volume : Measure X)‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ∂(volume : Measure X) := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    rw [enorm_smul, Real.enorm_eq_ofReal (hρnn y)]
  have hD2 : ‖∫ y, ρ y • (u (x - y) - u x) ∂(volume : Measure X)‖ₑ ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ∂(volume : Measure X)) ^ (2:ℝ) :=
    ENNReal.rpow_le_rpow hD (by norm_num)
  have hfa : AEMeasurable (fun y : X => ‖u (x - y) - u x‖ₑ) (volume : Measure X) := by
    have hsub : AEStronglyMeasurable (fun y : X => u (x - y)) (volume : Measure X) :=
      hu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    exact (hsub.sub aestronglyMeasurable_const).enorm
  have hga : AEMeasurable (fun y : X => ENNReal.ofReal (ρ y)) (volume : Measure X) :=
    hρi.aemeasurable.ennreal_ofReal
  have ha1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(volume : Measure X) = 1 :=
    lintegral_ofReal_eq_one hρnn hρi hρ1
  have hCS := Commons.Measure.Integral.lintegral_mul_pow_le (ν := (volume : Measure X)) (q := 2)
    (by norm_num) hfa hga
  rw [show (∫⁻ y, ‖u (x - y) - u x‖ₑ * ENNReal.ofReal (ρ y))
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ from
        lintegral_congr fun y => mul_comm _ _,
      show (∫⁻ y, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (ρ y))
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) from
        lintegral_congr fun y => mul_comm _ _,
      ha1, show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, mul_one] at hCS
  simpa [ENNReal.rpow_two] using hD2.trans hCS

/-- **`L²`-convergence of mollification** (vector-valued).  If `ρ i` is a family of nonnegative
approximate identities on `ℝⁿ` (`∫ ρ i = 1`) whose supports shrink to `{0}`
(`ρ i x = 0` whenever `R i < ‖x‖`, with `R i → 0`), then convolving with `ρ i` converges to the
identity in `L²(ℝⁿ, ℝᵐ)`. -/
theorem tendsto_lintegral_convolution_sub_sq_vec {ι : Type*} {l : Filter ι}
    (ρ : ι → X → ℝ) (R : ι → ℝ)
    (hρnn : ∀ i x, 0 ≤ ρ i x)
    (hρi : ∀ i, Integrable (ρ i) (volume : Measure X))
    (hρ1 : ∀ i, ∫ x, ρ i x ∂(volume : Measure X) = 1)
    (hRpos : ∀ i, 0 ≤ R i) (hR : Tendsto R l (nhds 0))
    (hRs : ∀ i, ∀ x, R i < ‖x‖ → ρ i x = 0)
    (u : X → Y) (hu : MemLp u 2 (volume : Measure X)) :
    Tendsto (fun i => ∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure X)) - u x‖ ^ 2)
        ∂(volume : Measure X)) l (nhds 0) := by
  let G : X → ℝ≥0∞ := fun y => ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂(volume : Measure X)
  have hGtend : Tendsto G (nhds 0) (nhds 0) := by
    have h := tendsto_lintegral_translate_sub_vec_general (F := Y) u hu
    refine h.congr' (Eventually.of_forall fun y => ?_)
    simp only [G]
    exact lintegral_congr fun x => ofReal_norm_sq_eq_enorm _
  have hS : Tendsto (fun i => ⨆ y ∈ Metric.closedBall (0 : X) (R i), G y) l (nhds 0) :=
    Commons.Analysis.Measure.tendsto_iSup_closedBall_nhds_zero hGtend R hR
  have hbound : ∀ i, (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure X)) - u x‖ ^ 2)
        ∂(volume : Measure X))
      ≤ ⨆ y ∈ Metric.closedBall (0 : X) (R i), G y := by
    intro i
    calc (∫⁻ x, ENNReal.ofReal
            (‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure X)) - u x‖ ^ 2)
            ∂(volume : Measure X))
        = ∫⁻ x, ‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure X)) - u x‖ₑ ^ (2:ℝ)
            ∂(volume : Measure X) :=
          lintegral_congr fun x => ofReal_norm_sq_eq_enorm _
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ i y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ)
            ∂(volume : Measure X) ∂(volume : Measure X) := by
          apply lintegral_mono_ae
          filter_upwards [enorm_convolution_sub_le_vec (hρnn i) (hρi i) (hρ1 i) u hu] with x hx
          simpa only [ENNReal.rpow_two] using hx
      _ = ∫⁻ y, ENNReal.ofReal (ρ i y) * G y ∂(volume : Measure X) := by
          rw [MeasureTheory.lintegral_lintegral_swap
            (f := fun x y => ENNReal.ofReal (ρ i y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ))
            (by
              have h := aemeasurable_uncurry_ofReal_mul_enorm_sq_vec (hρi i) u hu
              simpa only [ENNReal.rpow_two] using h)]
          apply lintegral_congr; intro y
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (∫⁻ y, ENNReal.ofReal (ρ i y) ∂(volume : Measure X)) *
            (⨆ y ∈ Metric.closedBall (0 : X) (R i), G y) := by
          by_cases hStop : (⨆ y ∈ Metric.closedBall (0 : X) (R i), G y) = ⊤
          · rw [hStop, lintegral_ofReal_eq_one (hρnn i) (hρi i) (hρ1 i), one_mul]
            exact le_top
          · rw [← MeasureTheory.lintegral_mul_const' _ _ hStop]
            apply lintegral_mono; intro y
            by_cases h : ρ i y = 0
            · simp [h]
            · have hy : y ∈ Metric.closedBall (0 : X) (R i) := by
                by_contra hcon
                refine h (hRs i y ?_)
                have hle : ¬ dist y 0 ≤ R i := fun hc => hcon (Metric.mem_closedBall.mpr hc)
                have := not_le.mp hle
                simpa [dist_eq_norm] using this
              have hle : G y ≤ ⨆ z ∈ Metric.closedBall (0 : X) (R i), G z :=
                le_iSup₂_of_le y hy le_rfl
              exact mul_le_mul_right hle (ENNReal.ofReal (ρ i y))
      _ = ⨆ y ∈ Metric.closedBall (0 : X) (R i), G y := by
          rw [lintegral_ofReal_eq_one (hρnn i) (hρi i) (hρ1 i), one_mul]
  rw [ENNReal.tendsto_nhds_zero] at hS ⊢
  intro ε hε
  filter_upwards [hS ε hε] with i hi
  exact le_trans (hbound i) hi

end Vec

theorem tendsto_integral_sq_moll_sub_compact_vec_measurable {n m : ℕ} {ι : Type*} {l : Filter ι}
    (ρ : ι → EuclideanSpace ℝ (Fin n) → ℝ) (R : ι → ℝ)
    (hρnn : ∀ i x, 0 ≤ ρ i x) (hρi : ∀ i, MeasureTheory.Integrable (ρ i) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hρ1 : ∀ i, ∫ x, ρ i x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hRpos : ∀ i, 0 ≤ R i) (hR : Filter.Tendsto R l (nhds 0))
    (hRs : ∀ i x, R i < ‖x‖ → ρ i x = 0)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (humeas : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hu : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖u x‖ ^ 2) K (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    Filter.Tendsto (fun i => ∫ x in K,
        ‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) - u x‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) l (nhds 0) := by
  classical
  set K' : Set (EuclideanSpace ℝ (Fin n)) :=
    K + Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hK'def
  have hK'c : IsCompact K' := by
    rw [hK'def]; exact hK.add (isCompact_closedBall _ _)
  have hK'meas : MeasurableSet K' := hK'c.isClosed.measurableSet
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKK' : K ⊆ K' := by
    intro x hx
    rw [hK'def]
    exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩
  set w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) := K'.indicator u with hwdef
  have hw_memLp : MemLp w 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hwdef, memLp_indicator_iff_restrict hK'meas]
    exact (memLp_two_iff_integrable_sq_norm humeas.restrict).2 (hu K' hK'c)
  have hD := tendsto_lintegral_convolution_sub_sq_vec ρ R hρnn hρi hρ1 hRpos hR hRs w hw_memLp
  set gu : ι → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => ‖(∫ y, ρ i y • u (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) - u x‖ ^ 2
    with hgudef
  set gw : ι → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => ‖(∫ y, ρ i y • w (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) - w x‖ ^ 2
    with hgwdef
  set D : ι → ℝ≥0∞ :=
    fun i => ∫⁻ x, ENNReal.ofReal (gw i x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
    with hDdef
  have hD' : Tendsto D l (nhds 0) := by
    refine hD.congr' (Eventually.of_forall fun i => ?_)
    simp only [hDdef, hgwdef]
  have hconv_eq : ∀ i, R i ≤ 1 → ∀ x ∈ K,
      (∫ y, ρ i y • u (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = (∫ y, ρ i y • w (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro i hi x hx
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change ρ i y • u (x - y) = ρ i y • w (x - y)
    by_cases hy : R i < ‖y‖
    · rw [hRs i y hy]; simp
    · have hmem : x - y ∈ K' := by
        rw [hK'def, sub_eq_add_neg]
        refine Set.mem_add.mpr ⟨x, hx, -y, ?_, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg]
        exact le_trans (le_of_not_gt hy) hi
      have : w (x - y) = u (x - y) := by
        rw [hwdef]; exact Set.indicator_of_mem hmem u
      rw [this]
  have hguw : ∀ i, R i ≤ 1 → ∀ x ∈ K, gu i x = gw i x := by
    intro i hi x hx
    simp only [hgudef, hgwdef]
    rw [hconv_eq i hi x hx]
    have : w x = u x := by
      rw [hwdef]; exact Set.indicator_of_mem (hKK' hx) u
    rw [this]
  have hkey : ∀ i, R i ≤ 1 → D i < ⊤ →
      ∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≤ (D i).toReal := by
    intro i hi hDfin
    by_cases hmeas : AEStronglyMeasurable (gu i) (volume.restrict K)
    · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => by positivity)) hmeas]
      apply ENNReal.toReal_mono hDfin.ne
      calc ∫⁻ x, ENNReal.ofReal (gu i x) ∂(volume.restrict K)
          = ∫⁻ x in K, ENNReal.ofReal (gu i x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl
        _ = ∫⁻ x in K, ENNReal.ofReal (gw i x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
              setLIntegral_congr_fun hKmeas (fun x hx => by rw [hguw i hi x hx])
        _ ≤ D i := by
              simpa [hDdef] using lintegral_mono_set (Set.subset_univ K)
    · have hz : ∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
        rw [show (∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            = ∫ x, gu i x ∂(volume.restrict K) from rfl]
        exact integral_undef (fun h => hmeas h.aestronglyMeasurable)
      rw [hz]
      exact ENNReal.toReal_nonneg
  have hDfin : ∀ᶠ i in l, D i < ⊤ :=
    hD'.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ≥0∞) < ⊤ by simp))
  have hR1 : ∀ᶠ i in l, R i ≤ 1 :=
    (hR.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono
      (fun i hi => le_of_lt hi)
  have hDreal : Tendsto (fun i => (D i).toReal) l (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) ≠ ∞ := by simp
    have := (ENNReal.tendsto_toReal h0).comp hD'
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  change Tendsto (fun i => ∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) l (nhds 0)
  refine squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg (fun x => by positivity))) ?_ hDreal
  filter_upwards [hR1, hDfin] with i hi hfin
  exact hkey i hi hfin

end Commons.Analysis.Convolution