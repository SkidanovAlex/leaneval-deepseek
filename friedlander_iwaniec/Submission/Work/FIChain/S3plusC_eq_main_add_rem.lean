import Mathlib
import Submission.Work.FIChain.s3RemPlus_defs
import Submission.Work.FIChain.s3InnerInt_eq_split
import Submission.Work.FIChain.S3plusC_aux2
import Submission.Work.FIChain.s3SplitDefs
import Submission.Work.FIChain.s3Split_integrand_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Interval integrability of the two `(1.7)`-halves

Both integrands `u ↦ s3MainI … u / u` and `u ↦ s3RemI … u / u` are *step functions* of `u`
(`u ↦ ⌊u⌋₊` and `u ↦ ⌊max (ℓ z) (ℓ Cm u)⌋₊` are), and on `[a,b]` with `1 ≤ a ≤ b` the sum range
`Icc 1 ⌊u⌋₊` is contained in the fixed `Icc 1 ⌊b⌋₊`, while every `Ã`-evaluation stays inside the
fixed finite range up to `⌊max (ℓ z) (ℓ Cm b)⌋₊`.  So the integrand is bounded on `[a,b]` by an
explicit finite sum and — being a finite sum of `u`-measurable functions — interval integrable. -/

/-- A measurable function bounded by `M` on `[a,b]` (`1 ≤ a ≤ b`) gives an interval-integrable
`u ↦ h u / u`. -/
private theorem intervalIntegrable_div_of_bdd (h : ℝ → ℝ) (M a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hmeas : Measurable h) (hbdd : ∀ u ∈ Set.Icc a b, |h u| ≤ M) :
    IntervalIntegrable (fun u => h u / u) volume a b := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (h a)) (hbdd a (Set.mem_Icc.mpr ⟨le_refl a, hab⟩))
  constructor
  · refine Measure.integrableOn_of_bounded
      (s_finite := (measure_Ioc_lt_top (a := a) (b := b)).ne)
      (f_mble := (hmeas.div measurable_id).aestronglyMeasurable) (M := M) ?_
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u hu
    have hu1 : 1 ≤ u := le_trans ha (le_of_lt hu.1)
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |h u| ≤ M := hbdd u (Set.mem_Icc.mpr ⟨le_of_lt hu.1, hu.2⟩)
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * u := mul_le_mul_of_nonneg_left hu1 hM
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact integrableOn_empty

/-- The MAIN integrand `u ↦ s3MainI … u / u` is interval integrable on `[a,b]` (`1 ≤ a ≤ b`), with
no hypothesis on the parameters. -/
private theorem s3MainI_intervalIntegrable_aux (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => s3MainI x z sz Cm ℓ u / u) volume a b := by
  classical
  set Mc : ℝ := ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, |Submission.ASP.FIgtil (ℓ * d)| *
      (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊) with hMc
  have hMc0 : 0 ≤ Mc := by
    rw [hMc]
    exact Finset.sum_nonneg (fun d hd => mul_nonneg (abs_nonneg _)
      (add_nonneg (AcountAtilC_nonneg _) (AcountAtilC_nonneg _)))
  set G : ℝ → ℝ := fun u => ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, (if (d : ℝ) ≤ u then
      (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (ℓ * d) *
        (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊) else 0) with hG
  have hGmeas : Measurable G := by
    simp only [hG]
    refine Finset.measurable_sum _ (fun d hd => ?_)
    have hAB : Measurable (fun u : ℝ => AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊) :=
      Measurable.sub measurable_const
        ((by fun_prop : Measurable (AcountAtilC : ℕ → ℝ)).comp
          (Nat.measurable_floor.comp (Measurable.max measurable_const
            (measurable_const.mul measurable_id))))
    refine Measurable.ite (measurableSet_le measurable_const measurable_id)
      ((measurable_const.mul measurable_const).mul hAB) measurable_const
  have hGbdd : ∀ u ∈ Set.Icc a b, |G u| ≤ Mc := by
    intro u hu
    obtain ⟨hua, hub⟩ := Set.mem_Icc.mp hu
    have hu1 : (1 : ℝ) ≤ u := le_trans ha hua
    have hfloor : ⌊u⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hub
    have hAu : AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
        ≤ AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊ := by
      apply AcountAtilC_mono
      apply Nat.floor_mono
      exact max_le_max (le_refl _) (mul_le_mul_of_nonneg_left hub (by positivity))
    simp only [hG, hMc]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
    split_ifs with hdu
    · rw [abs_mul, abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 :=
        Submission.ASP.abs_moebius_cast_le_one d
      have hF0 : (0 : ℝ) ≤ |Submission.ASP.FIgtil (ℓ * d)| := abs_nonneg _
      have habs : |AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
          ≤ AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊ := by
        have h1 := AcountAtilC_nonneg ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        have h2 := AcountAtilC_nonneg ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
        have h3 := AcountAtilC_nonneg ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      calc |(ArithmeticFunction.moebius d : ℝ)| * |Submission.ASP.FIgtil (ℓ * d)|
            * |AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
          ≤ 1 * |Submission.ASP.FIgtil (ℓ * d)| *
              (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊) :=
            mul_le_mul (mul_le_mul hmu le_rfl hF0 (by norm_num)) habs (abs_nonneg _) (by positivity)
        _ = |Submission.ASP.FIgtil (ℓ * d)| *
              (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊) := by ring
    · rw [abs_zero]
      exact mul_nonneg (abs_nonneg _)
        (add_nonneg (AcountAtilC_nonneg _) (AcountAtilC_nonneg _))
  have hIntG : IntervalIntegrable (fun u => G u / u) volume a b :=
    intervalIntegrable_div_of_bdd G Mc a b ha hab hGmeas hGbdd
  refine IntervalIntegrable.congr ?_ hIntG
  intro u hu
  rw [Set.uIoc_of_le hab] at hu
  obtain ⟨hua, hub⟩ := Set.mem_Ioc.mp hu
  have hu0 : (0 : ℝ) ≤ u := le_trans (le_trans zero_le_one ha) hua.le
  have hGu : G u = s3MainI x z sz Cm ℓ u := by
    simp only [hG, s3MainI]
    have hsub : Finset.Icc 1 ⌊u⌋₊ ⊆ Finset.Icc 1 ⌊b⌋₊ := by
      intro d hd; rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (Nat.floor_mono hub)⟩
    have hzero : ∀ d ∈ Finset.Icc 1 ⌊b⌋₊, d ∉ Finset.Icc 1 ⌊u⌋₊ →
        (if (d : ℝ) ≤ u then
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (ℓ * d) *
            (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊) else 0) = 0 := by
      intro d hd hnd
      rw [if_neg]
      intro hdu
      exact hnd (by rw [Finset.mem_Icc] at hd ⊢
                    exact ⟨hd.1, (Nat.le_floor_iff hu0).mpr hdu⟩)
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Icc] at hd
    rw [if_pos ((Nat.le_floor_iff hu0).mp hd.2)]
  change G u / u = s3MainI x z sz Cm ℓ u / u
  rw [hGu]

/-- The REM integrand `u ↦ s3RemI … u / u` is interval integrable on `[a,b]` (`1 ≤ a ≤ b`), with
no hypothesis on the parameters.  The bound on the summands is `abs_rtildeFull_le_mul`. -/
private theorem s3RemI_intervalIntegrable_aux (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => s3RemI x z sz Cm ℓ u / u) volume a b := by
  classical
  set Mc : ℝ := ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, (1 + |Submission.ASP.FIgtil (ℓ * d)|) *
      (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊) with hMc
  have hMc0 : 0 ≤ Mc := by
    rw [hMc]
    exact Finset.sum_nonneg (fun d hd => mul_nonneg (by positivity)
      (add_nonneg (AcountAtilC_nonneg _) (AcountAtilC_nonneg _)))
  set G : ℝ → ℝ := fun u => ∑ d ∈ Finset.Icc 1 ⌊b⌋₊, (if (d : ℝ) ≤ u then
      (ArithmeticFunction.moebius d : ℝ) *
        (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
            Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
            ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
              ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊) else 0) with hG
  have hGmeas : Measurable G := by
    simp only [hG]
    refine Finset.measurable_sum _ (fun d hd => ?_)
    have hAB : Measurable (fun u : ℝ =>
        (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
            Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
            ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
              ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) :=
      Measurable.sub measurable_const
        ((by fun_prop : Measurable (fun n : ℕ =>
            Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) n)).comp
          (Nat.measurable_floor.comp (Measurable.max measurable_const
            (measurable_const.mul measurable_id))))
    exact Measurable.ite (measurableSet_le measurable_const measurable_id)
      (measurable_const.mul hAB) measurable_const
  have hGbdd : ∀ u ∈ Set.Icc a b, |G u| ≤ Mc := by
    intro u hu
    obtain ⟨hua, hub⟩ := Set.mem_Icc.mp hu
    have hu1 : (1 : ℝ) ≤ u := le_trans ha hua
    have hfloor : ⌊u⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hub
    have hAu : AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
        ≤ AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊ := by
      apply AcountAtilC_mono
      apply Nat.floor_mono
      exact max_le_max (le_refl _) (mul_le_mul_of_nonneg_left hub (by positivity))
    simp only [hG, hMc]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
    split_ifs with hdu
    · rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 :=
        Submission.ASP.abs_moebius_cast_le_one d
      have hF0 : (0 : ℝ) ≤ 1 + |Submission.ASP.FIgtil (ℓ * d)| := by positivity
      have hR1 := abs_rtildeFull_le_mul (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
      have hR2 := abs_rtildeFull_le_mul (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
      have hsub : |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
              ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
          ≤ (1 + |Submission.ASP.FIgtil (ℓ * d)|) *
              (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊) := by
        have h1 : Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            ≤ (1 + |Submission.ASP.FIgtil (ℓ * d)|)
              * AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊ := le_trans (le_abs_self _) hR1
        have h2 : -Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            ≤ (1 + |Submission.ASP.FIgtil (ℓ * d)|)
              * AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊ := le_trans (neg_le_abs _) hR1
        have h3 : Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
              ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
            ≤ (1 + |Submission.ASP.FIgtil (ℓ * d)|)
              * AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ :=
          le_trans (le_abs_self _) hR2
        have h4 : -Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
              ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
            ≤ (1 + |Submission.ASP.FIgtil (ℓ * d)|)
              * AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ :=
          le_trans (neg_le_abs _) hR2
        have h5 : (1 + |Submission.ASP.FIgtil (ℓ * d)|)
              * AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
            ≤ (1 + |Submission.ASP.FIgtil (ℓ * d)|)
              * AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊ :=
          mul_le_mul_of_nonneg_left hAu hF0
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      calc |(ArithmeticFunction.moebius d : ℝ)| *
            |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                  Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                  ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
          ≤ 1 * ((1 + |Submission.ASP.FIgtil (ℓ * d)|) *
              (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊)) :=
            mul_le_mul hmu hsub (abs_nonneg _) (by norm_num)
        _ = (1 + |Submission.ASP.FIgtil (ℓ * d)|) *
              (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                + AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * b)⌋₊) := by ring
    · rw [abs_zero]
      exact mul_nonneg (by positivity)
        (add_nonneg (AcountAtilC_nonneg _) (AcountAtilC_nonneg _))
  have hIntG : IntervalIntegrable (fun u => G u / u) volume a b :=
    intervalIntegrable_div_of_bdd G Mc a b ha hab hGmeas hGbdd
  refine IntervalIntegrable.congr ?_ hIntG
  intro u hu
  rw [Set.uIoc_of_le hab] at hu
  obtain ⟨hua, hub⟩ := Set.mem_Ioc.mp hu
  have hu0 : (0 : ℝ) ≤ u := le_trans (le_trans zero_le_one ha) hua.le
  have hGu : G u = s3RemI x z sz Cm ℓ u := by
    simp only [hG, s3RemI]
    have hsub : Finset.Icc 1 ⌊u⌋₊ ⊆ Finset.Icc 1 ⌊b⌋₊ := by
      intro d hd; rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (Nat.floor_mono hub)⟩
    have hzero : ∀ d ∈ Finset.Icc 1 ⌊b⌋₊, d ∉ Finset.Icc 1 ⌊u⌋₊ →
        (if (d : ℝ) ≤ u then
          (ArithmeticFunction.moebius d : ℝ) *
            (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                  Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                  ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊) else 0) = 0 := by
      intro d hd hnd
      rw [if_neg]
      intro hdu
      exact hnd (by rw [Finset.mem_Icc] at hd ⊢
                    exact ⟨hd.1, (Nat.le_floor_iff hu0).mpr hdu⟩)
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Icc] at hd
    rw [if_pos ((Nat.le_floor_iff hu0).mp hd.2)]
  change G u / u = s3RemI x z sz Cm ℓ u / u
  rw [hGu]

/-- **The per-`ℓ` split** of the `(1.7)`-identity inside the `λ⁺` level integral: the split form of
`s3InnerInt` (`s3InnerInt_eq_split`) is the sum of its MAIN half (the integrand `s3MainI`) and its
REM half (the integrand `s3RemI`).  The additivity of the interval integral is supplied by the two
interval-integrability facts above; the pointwise identity of the integrands is
`s3Split_integrand_eq`. -/
theorem s3InnerInt_split (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hCm : 1 ≤ Cm) (hsz : 1 ≤ sz) (hzsz : z ≤ sz)
    (hzN : (ℓ : ℝ) * z ≤ (x : ℝ)) (hCmz : (Cm : ℝ) ≤ z) (hT : 1 ≤ sz / (Cm : ℝ)) :
    s3InnerInt atilc x ℓ Cm z sz
      = (∫ u in (1 : ℝ)..(s3SplitU x z sz Cm ℓ), s3MainI x z sz Cm ℓ u / u)
        + (∫ u in (1 : ℝ)..(s3SplitU x z sz Cm ℓ), s3RemI x z sz Cm ℓ u / u) := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (by omega : 0 < Cm)
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hU1 : (1 : ℝ) ≤ s3SplitU x z sz Cm ℓ := by
    rw [s3SplitU]
    refine le_min hT ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hCmz hℓpos.le, hzN]
  have hIm := s3MainI_intervalIntegrable_aux (x := x) (z := z) (sz := sz) (Cm := Cm) (ℓ := ℓ)
    (a := 1) (b := s3SplitU x z sz Cm ℓ) le_rfl hU1
  have hIr := s3RemI_intervalIntegrable_aux (x := x) (z := z) (sz := sz) (Cm := Cm) (ℓ := ℓ)
    (a := 1) (b := s3SplitU x z sz Cm ℓ) le_rfl hU1
  rw [s3InnerInt_eq_split x ℓ Cm z sz hℓ hCm hsz hzsz hzN hCmz hT]
  simp only [s3SplitU]
  rw [intervalIntegral.integral_congr (fun u _ => s3Split_integrand_eq x z sz Cm ℓ u)]
  exact intervalIntegral.integral_add hIm hIr

/-- **The `(1.7)`-split of `S₃⁺`**: `S3plusC = s3MainPlus + s3RemPlus`, i.e. the companion's (8.2)
summed over the outer index `ℓ`.  The outer weight `Σ_{b | ℓ, sy < b} μ b · ρ(ℓ)` is common to the
two sides, so the proof is the per-`ℓ` split `s3InnerInt_split` plus the observation that for
`ℓ · z > x` the inner `c`-sum vanishes (`S3plusInnerC_eq_zero_of_mul_lt`), which is exactly the
indicator `ℓ · z ≤ x` carried by the two definitions. -/
theorem S3plusC_eq_main_add_rem (lam : ℕ → ℝ) (x : ℕ) (z sy sz : ℝ) (Cm : ℕ)
    (hCm : 1 ≤ Cm) (hz2 : 2 ≤ z) (hzCm : ((Cm : ℕ) : ℝ) < z)
    (hsz : 1 ≤ sz) (hzsz : z ≤ sz) (hT : 1 ≤ sz / (Cm : ℝ)) :
    Work.FIChain.S3plusC Work.FIChain.atilc lam x z sy sz (Cm : ℝ)
      = Work.FIChain.s3MainPlus lam x z sy sz Cm
        + Work.FIChain.s3RemPlus lam x z sy sz Cm := by
  let W : ℕ → ℝ := fun ℓ => (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
      (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ
  have hu : S3plusC atilc lam x z sy sz (Cm : ℝ)
      = ∑ ℓ ∈ Finset.Icc 1 x, W ℓ * S3plusInnerC atilc x ℓ z sz (Cm : ℝ) := rfl
  have hm : s3MainPlus lam x z sy sz Cm
      = ∑ ℓ ∈ Finset.Icc 1 x, (if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
          W ℓ * (∫ u in (1 : ℝ)..(s3SplitU x z sz Cm ℓ), s3MainI x z sz Cm ℓ u / u)
          else 0) := rfl
  have hr : s3RemPlus lam x z sy sz Cm
      = ∑ ℓ ∈ Finset.Icc 1 x, (if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
          W ℓ * (∫ u in (1 : ℝ)..(s3SplitU x z sz Cm ℓ), s3RemI x z sz Cm ℓ u / u)
          else 0) := rfl
  rw [hu, hm, hr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc] at hℓ
  obtain ⟨hℓ1, hℓx⟩ := hℓ
  by_cases hc : ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ)
  · rw [S3plusInnerC_eq_s3InnerInt atilc x ℓ Cm z sz atilc_eq_zero_of_not_squarefree hCm hz2 hzCm,
      s3InnerInt_split x z sz Cm ℓ hℓ1 hCm hsz hzsz hc (le_of_lt hzCm) hT]
    simp only [if_pos hc]
    ring
  · have hzero : S3plusInnerC atilc x ℓ z sz (Cm : ℝ) = 0 :=
      S3plusInnerC_eq_zero_of_mul_lt atilc x ℓ z sz (Cm : ℝ) (not_le.mp hc)
    rw [hzero, mul_zero]
    simp only [if_neg hc, add_zero]

end

end Work.FIChain
