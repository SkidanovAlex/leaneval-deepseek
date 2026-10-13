import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.traceAux

open MeasureTheory Set Filter
open scoped ENNReal

theorem integrableOn_Ioo_of_intervalIntegral_le {ε K : ℝ} (hε : 0 < ε) {f : ℝ → ℝ}
    (hfnn : ∀ x ∈ Set.Ioo 0 ε, 0 ≤ f x)
    (hfi : ∀ δ ∈ Set.Ioo 0 ε, IntervalIntegrable f volume δ ε)
    (hbd : ∀ δ ∈ Set.Ioo 0 ε, (∫ x in δ..ε, f x) ≤ K) :
    MeasureTheory.IntegrableOn f (Set.Ioo 0 ε) := by
  classical
  -- the approximating left endpoints `d n = ε / (n + 2) ↓ 0`
  set d : ℕ → ℝ := fun n => ε / ((n : ℝ) + 2) with hd
  have hdpos : ∀ n, 0 < d n := by
    intro n
    simp only [hd]
    positivity
  have hdlt : ∀ n, d n < ε := by
    intro n
    simp only [hd]
    refine div_lt_self hε ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdmem : ∀ n, d n ∈ Set.Ioo (0 : ℝ) ε := fun n => ⟨hdpos n, hdlt n⟩
  have hdle : ∀ n, d n ≤ ε := fun n => (hdlt n).le
  -- `f` is nonnegative almost everywhere on each `(d n, ε]`
  have hnn : ∀ n, ∀ᵐ x ∂(volume.restrict (Set.Ioc (d n) ε)), 0 ≤ f x := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
    refine measure_mono_null ?_ (measure_singleton ε)
    intro x hx
    push Not at hx
    obtain ⟨hxIoc, hxf⟩ := hx
    by_contra hxe
    exact absurd (hfnn x ⟨lt_trans (hdpos n) hxIoc.1, lt_of_le_of_ne hxIoc.2 hxe⟩)
      (not_le.mpr hxf)
  -- the lintegral of `f` over each `(d n, ε]` is bounded by `ofReal K`
  have hbnd : ∀ n, ∫⁻ x in Set.Ioc (d n) ε, ENNReal.ofReal (f x) ≤ ENNReal.ofReal K := by
    intro n
    have hInt : IntegrableOn f (Set.Ioc (d n) ε) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (hdle n)).mp (hfi (d n) (hdmem n))
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (hnn n)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← intervalIntegral.integral_of_le (hdle n)]
    exact hbd (d n) (hdmem n)
  -- the indicator functions of `(d n, ε]` are a.e. measurable
  have hAEM : ∀ n, AEMeasurable
      (fun x => (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x) volume := by
    intro n
    refine (aemeasurable_indicator_iff measurableSet_Ioc).mpr ?_
    have hInt : IntegrableOn f (Set.Ioc (d n) ε) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (hdle n)).mp (hfi (d n) (hdmem n))
    exact ENNReal.measurable_ofReal.comp_aemeasurable hInt.aemeasurable
  -- and they are pointwise monotone in `n`
  have hmono : ∀ᵐ x ∂volume,
      Monotone fun n => (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    intro n m hnm
    change (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x
      ≤ (Set.Ioc (d m) ε).indicator (fun y => ENNReal.ofReal (f y)) x
    have hsub : Set.Ioc (d n) ε ⊆ Set.Ioc (d m) ε := by
      refine Ioc_subset_Ioc_left ?_
      simp only [hd]
      refine div_le_div_of_nonneg_left hε.le (by positivity) ?_
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      linarith
    by_cases hx : x ∈ Set.Ioc (d n) ε
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  -- the union of the sets `(d n, ε]` is `(0, ε]`
  have hunion : (⋃ n, Set.Ioc (d n) ε) = Set.Ioc (0 : ℝ) ε := by
    ext y
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨n, hn⟩
      exact ⟨lt_trans (hdpos n) hn.1, hn.2⟩
    · rintro ⟨hy0, hyε⟩
      rw [Set.mem_iUnion]
      obtain ⟨N, hN⟩ := exists_nat_gt (ε / y)
      refine ⟨N, ⟨?_, hyε⟩⟩
      simp only [hd]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 2)]
      have hy : 0 < y := hy0
      have h1 : ε / y * y < (N : ℝ) * y := mul_lt_mul_of_pos_right hN hy
      rw [div_mul_cancel₀ ε hy.ne'] at h1
      nlinarith [h1, hy, (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  -- the sup of the indicators is the indicator of the union
  have hsup : ∀ x, (⨆ n, (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x)
      = (Set.Ioc (0 : ℝ) ε).indicator (fun y => ENNReal.ofReal (f y)) x := by
    intro x
    have h := indicator_iUnion_apply (M := ℝ≥0∞) (rfl : (⊥ : ℝ≥0∞) = 0)
      (fun n => Set.Ioc (d n) ε) (fun y => ENNReal.ofReal (f y)) x
    rw [hunion] at h
    exact h.symm
  -- monotone convergence: the lintegral over `(0, ε]` is the sup of the lintegrals
  have hfin : ∫⁻ x in Set.Ioc (0 : ℝ) ε, ENNReal.ofReal (f x) ≤ ENNReal.ofReal K := by
    have hmain := lintegral_iSup' (μ := volume)
      (f := fun n x => (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x)
      hAEM hmono
    calc ∫⁻ x in Set.Ioc (0 : ℝ) ε, ENNReal.ofReal (f x)
        = ∫⁻ x, (Set.Ioc (0 : ℝ) ε).indicator (fun y => ENNReal.ofReal (f y)) x :=
          (lintegral_indicator measurableSet_Ioc _).symm
      _ = ∫⁻ x, ⨆ n, (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x :=
          lintegral_congr_ae (Filter.Eventually.of_forall fun x => (hsup x).symm)
      _ = ⨆ n, ∫⁻ x, (Set.Ioc (d n) ε).indicator (fun y => ENNReal.ofReal (f y)) x := hmain
      _ = ⨆ n, ∫⁻ x in Set.Ioc (d n) ε, ENNReal.ofReal (f x) := by
          simp only [lintegral_indicator measurableSet_Ioc]
      _ ≤ ENNReal.ofReal K := iSup_le hbnd
  -- `ofReal ‖f‖` and `ofReal f` agree a.e. on `(0, ε]`
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) ε)),
      ENNReal.ofReal ‖f x‖ = ENNReal.ofReal (f x) := by
    rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
    refine measure_mono_null ?_ (measure_singleton ε)
    intro x hx
    push Not at hx
    obtain ⟨hxIoc, hxne⟩ := hx
    by_contra hxe
    exact hxne (by rw [Real.norm_of_nonneg (hfnn x ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxe⟩)])
  -- strong measurability on `(0, ε]`
  have hAESM : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) ε)) := by
    rw [← hunion]
    refine AEStronglyMeasurable.iUnion (fun n => ?_)
    exact (hfi (d n) (hdmem n)).1.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · exact hAESM.mono_measure (Measure.restrict_mono Set.Ioo_subset_Ioc_self le_rfl)
  · rw [hasFiniteIntegral_iff_norm]
    refine lt_of_le_of_lt (lintegral_mono_set Set.Ioo_subset_Ioc_self) ?_
    refine lt_of_le_of_lt (le_trans (le_of_eq (lintegral_congr_ae hae)) hfin) ENNReal.ofReal_lt_top

end Work.FTS.EllSol.VthAux.traceAux
