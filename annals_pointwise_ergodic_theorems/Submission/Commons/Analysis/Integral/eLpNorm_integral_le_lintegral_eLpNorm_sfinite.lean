import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped ENNReal

/-- For `a ≠ ⊤` and `1 < p`, `a ^ p = a ^ (p - 1) * a`. -/
lemma rpow_pred_mul {a : ℝ≥0∞} {p : ℝ} (ha : a ≠ ⊤) (hp : 1 < p) :
    a ^ p = a ^ (p - 1) * a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p),
        ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p - 1), zero_mul]
  · have h := ENNReal.rpow_add (x := a) (p - 1) 1 ha0 ha
    rw [ENNReal.rpow_one] at h
    rw [← h, sub_add_cancel]

/-- `ℝ≥0∞`-valued `rpow` commutes with `iSup` for positive exponent. -/
lemma ENNReal.iSup_rpow {ι : Sort*} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 < r) :
    (⨆ i, f i) ^ r = ⨆ i, (f i) ^ r := by
  apply le_antisymm
  · have h1 : ⨆ i, f i ≤ (⨆ i, (f i) ^ r) ^ (1 / r) := by
      apply iSup_le; intro i
      have h2 : f i = ((f i) ^ r) ^ (1 / r) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
      rw [h2]
      exact ENNReal.rpow_le_rpow (le_iSup (fun i => (f i) ^ r) i) (by positivity)
    calc (⨆ i, f i) ^ r ≤ ((⨆ i, (f i) ^ r) ^ (1 / r)) ^ r :=
          ENNReal.rpow_le_rpow h1 hr.le
      _ = ⨆ i, (f i) ^ r := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  · exact iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hr.le

/-- Minkowski's integral inequality for `ℝ≥0∞`-valued functions, for a finite measure `μ` and
`1 < p` (real exponent). -/
theorem lintegral_rpow_lintegral_le_of_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {p : ℝ} (hp1 : 1 < p) {g : β → α → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ x, (∫⁻ y, g y x ∂ν) ^ p ∂μ) ^ (1 / p)
      ≤ ∫⁻ y, (∫⁻ x, g y x ^ p ∂μ) ^ (1 / p) ∂ν := by
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp1, ?_⟩
    rw [inv_div]
    field_simp
    ring
  set F : α × β → ℝ≥0∞ := fun z => g z.2 z.1 with hFdef
  have hF : Measurable F := by
    rw [hFdef]; exact hg.comp measurable_swap
  set h : α → ℝ≥0∞ := fun x => ∫⁻ y, g y x ∂ν with hhdef
  have hh_meas : Measurable h := by
    rw [hhdef]
    simpa [hFdef, Function.uncurry] using hF.lintegral_prod_right'
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, g y x ^ p ∂μ) ^ (1 / p) ∂ν with hRdef
  suffices hmain : (∫⁻ x, h x ^ p ∂μ) ^ (1 / p) ≤ R by
    simpa [hhdef, hRdef] using hmain
  have hB_lt : ∀ n : ℕ, (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) < ⊤ := by
    intro n
    have hle : ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ ≤ (n:ℝ≥0∞) ^ p * μ Set.univ := by
      calc ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ
          ≤ ∫⁻ _x, (n:ℝ≥0∞) ^ p ∂μ := by
            apply lintegral_mono; intro x
            exact ENNReal.rpow_le_rpow inf_le_right hp0.le
        _ = (n:ℝ≥0∞) ^ p * μ Set.univ := lintegral_const _
    refine lt_of_le_of_lt hle (ENNReal.mul_lt_top ?_ ?_)
    · exact ENNReal.rpow_lt_top_of_nonneg hp0.le (by simp)
    · exact measure_lt_top μ Set.univ
  have key : ∀ n : ℕ,
      (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ≤
        (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) * R := by
    intro n
    set c : α → ℝ≥0∞ := fun x => (h x ⊓ (n:ℝ≥0∞)) ^ (p - 1) with hcdef
    have hc_meas : Measurable c := by
      rw [hcdef]; exact (hh_meas.inf measurable_const).pow_const _
    have hc_ne : ∀ x, c x ≠ ⊤ := fun x =>
      ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
        (ENNReal.rpow_le_rpow inf_le_right (by linarith : (0:ℝ) ≤ p - 1))
    have hstep1 : ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ ≤ ∫⁻ x, c x * h x ∂μ := by
      apply lintegral_mono; intro x
      calc (h x ⊓ (n:ℝ≥0∞)) ^ p = (h x ⊓ (n:ℝ≥0∞)) ^ (p - 1) * (h x ⊓ (n:ℝ≥0∞)) :=
            rpow_pred_mul (ne_top_of_le_ne_top (by simp) inf_le_right) hp1
        _ ≤ (h x ⊓ (n:ℝ≥0∞)) ^ (p - 1) * h x := by
            gcongr; exact inf_le_left
        _ = c x * h x := by rw [hcdef]
    have hstep2 : ∫⁻ x, c x * h x ∂μ = ∫⁻ x, ∫⁻ y, c x * g y x ∂ν ∂μ := by
      apply lintegral_congr; intro x
      rw [hhdef]
      exact (lintegral_const_mul' (c x) (fun y => g y x) (hc_ne x)).symm
    have hstep3 : ∫⁻ x, ∫⁻ y, c x * g y x ∂ν ∂μ
        = ∫⁻ y, ∫⁻ x, c x * g y x ∂μ ∂ν := by
      apply lintegral_lintegral_swap
      exact ((hc_meas.comp measurable_fst).mul hF).aemeasurable
    have hstep4 : ∫⁻ y, ∫⁻ x, c x * g y x ∂μ ∂ν ≤
        ∫⁻ y, (∫⁻ x, c x ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1)))
          * (∫⁻ x, g y x ^ p ∂μ) ^ (1 / p) ∂ν := by
      apply lintegral_mono; intro y
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm
        hc_meas.aemeasurable
        (hg.comp (measurable_prodMk_left (x := y))).aemeasurable
    have hc_pow : ∀ x, c x ^ (p / (p - 1)) = (h x ⊓ (n:ℝ≥0∞)) ^ p := by
      intro x
      rw [hcdef, ← ENNReal.rpow_mul]
      congr 1
      rw [mul_comm, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (by linarith : p - 1 ≠ 0), mul_one]
    have hstep5 : ∫⁻ y, (∫⁻ x, c x ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1)))
          * (∫⁻ x, g y x ^ p ∂μ) ^ (1 / p) ∂ν
        = (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) * R := by
      have hBeq : ∫⁻ x, c x ^ (p / (p - 1)) ∂μ = ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ :=
        lintegral_congr hc_pow
      rw [hBeq, hRdef]
      rw [lintegral_const_mul']
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (hB_lt n).ne
    calc ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ
        ≤ ∫⁻ x, c x * h x ∂μ := hstep1
      _ = ∫⁻ x, ∫⁻ y, c x * g y x ∂ν ∂μ := hstep2
      _ = ∫⁻ y, ∫⁻ x, c x * g y x ∂μ ∂ν := hstep3
      _ ≤ _ := hstep4
      _ = (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) * R := hstep5
  have hbound : ∀ n : ℕ, (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / p) ≤ R := by
    intro n
    rcases eq_or_ne (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) 0 with hzero | hpos
    · rw [hzero, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / p)]
      exact zero_le
    · have hBpos : 0 < ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ := lt_of_le_of_ne zero_le hpos.symm
      have hBne_top : (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ≠ ⊤ := (hB_lt n).ne
      have hBq_ne_top : (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) hBne_top
      have hBq_ne_zero : (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) ≠ 0 :=
        (ENNReal.rpow_pos hBpos hBne_top).ne'
      have hBs : (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ)
          = (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / p)
            * (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) := by
        rw [← ENNReal.rpow_add (1 / p) (1 / (p / (p - 1))) hpos hBne_top,
          show 1 / p + 1 / (p / (p - 1)) = 1 by field_simp; ring, ENNReal.rpow_one]
      have key' : (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / p)
            * (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1)))
          ≤ R * (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) := by
        rw [hBs.symm]
        calc ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ
            ≤ (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) * R := key n
          _ = R * (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / (p / (p - 1))) := mul_comm _ _
      exact (ENNReal.mul_le_mul_iff_left hBq_ne_zero hBq_ne_top).mp key'
  have hsup : (⨆ n : ℕ, ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) = ∫⁻ x, h x ^ p ∂μ := by
    rw [← lintegral_iSup']
    · apply lintegral_congr; intro x
      rw [← ENNReal.iSup_rpow (f := fun n : ℕ => h x ⊓ (n:ℝ≥0∞)) hp0]
      congr 1
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    · intro n
      exact ((hh_meas.inf measurable_const).pow_const _).aemeasurable
    · filter_upwards with x
      intro m n hmn
      exact ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast hmn)) hp0.le
  calc (∫⁻ x, h x ^ p ∂μ) ^ (1 / p)
      = (⨆ n : ℕ, ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / p) := by rw [hsup]
    _ = ⨆ n : ℕ, (∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) ^ (1 / p) :=
        ENNReal.iSup_rpow (f := fun n : ℕ => ∫⁻ x, (h x ⊓ (n:ℝ≥0∞)) ^ p ∂μ) (by positivity)
    _ ≤ R := iSup_le hbound

/-- `essSup` and `lintegral` commute in the direction of Minkowski's inequality. -/
theorem essSup_lintegral_le_lintegral_essSup_of_measurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [SFinite μ]
    {g : β → α → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    essSup (fun x => ∫⁻ y, g y x ∂ν) μ ≤ ∫⁻ y, essSup (fun x => g y x) μ ∂ν := by
  classical
  set c : β → ℝ≥0∞ := fun y => essSup (fun x => g y x) μ with hcdef
  have hc_meas : Measurable c := by
    apply measurable_of_Iic
    intro t
    have hset : {y : β | c y ≤ t} = {y : β | μ {x : α | t < g y x} = 0} := by
      ext y
      simp only [Set.mem_ofPred_eq, hcdef]
      constructor
      · intro h
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [ae_le_essSup (μ := μ) (f := fun x => g y x)] with x hx
        exact not_lt.mpr (hx.trans h)
      · intro h
        apply essSup_le_of_ae_le t
        rw [measure_eq_zero_iff_ae_notMem] at h
        filter_upwards [h] with x hx
        exact not_lt.mp hx
    change MeasurableSet {y : β | c y ≤ t}
    rw [hset]
    have hmeas : Measurable (fun y => μ {x : α | t < g y x}) := by
      have hst : MeasurableSet {z : β × α | t < g z.1 z.2} := measurableSet_lt measurable_const hg
      have heq : (fun y => μ {x : α | t < g y x})
          = fun y => ∫⁻ x, ({z : β × α | t < g z.1 z.2}.indicator (fun _ => (1:ℝ≥0∞))) (y, x) ∂μ := by
        funext y
        have hcongr : (fun x => ({z : β × α | t < g z.1 z.2}.indicator (fun _ => (1:ℝ≥0∞))) (y, x))
            = (Prod.mk y ⁻¹' {z : β × α | t < g z.1 z.2}).indicator (fun _ => (1:ℝ≥0∞)) := by
          funext x
          rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage]
          by_cases h : (y, x) ∈ {z : β × α | t < g z.1 z.2} <;> simp [h]
        rw [hcongr, show lintegral μ ((Prod.mk y ⁻¹' {z : β × α | t < g z.1 z.2}).indicator
                (fun _ => (1:ℝ≥0∞)))
              = μ (Prod.mk y ⁻¹' {z : β × α | t < g z.1 z.2}) from
            lintegral_indicator_one
              (hst.preimage (measurable_prodMk_left (x := y)))]
        rfl
      rw [heq]
      exact (Measurable.indicator measurable_const hst).lintegral_prod_right'
    exact hmeas (measurableSet_singleton 0)
  have hS_meas : MeasurableSet {z : β × α | c z.1 < g z.1 z.2} :=
    measurableSet_lt (hc_meas.comp measurable_fst) hg
  have hS_null : (ν.prod μ) {z : β × α | c z.1 < g z.1 z.2} = 0 := by
    rw [Measure.prod_apply hS_meas]
    have hone : (fun y => μ (Prod.mk y ⁻¹' {z : β × α | c z.1 < g z.1 z.2})) = fun _ => 0 := by
      funext y
      have h1 : μ {x : α | c y < g y x} = 0 := by
        simpa [hcdef] using
          (meas_essSup_lt (μ := μ) (f := fun x => g y x)
            ⟨⊤, Filter.Eventually.of_forall fun x => le_top⟩)
      simpa using h1
    rw [hone]
    simp
  have hS'_null : (μ.prod ν) (Prod.swap ⁻¹' {z : β × α | c z.1 < g z.1 z.2}) = 0 := by
    rw [← Measure.map_apply measurable_swap hS_meas, Measure.prod_swap]
    exact hS_null
  have hae_null : (fun x => ν (Prod.mk x ⁻¹' (Prod.swap ⁻¹' {z : β × α | c z.1 < g z.1 z.2})))
      =ᵐ[μ] 0 :=
    Measure.measure_ae_null_of_prod_null hS'_null
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, g y x ≤ c y := by
    filter_upwards [hae_null] with x hx
    rw [ae_iff]
    have hset : Prod.mk x ⁻¹' (Prod.swap ⁻¹' {z : β × α | c z.1 < g z.1 z.2})
        = {y : β | ¬ (g y x ≤ c y)} := by
      ext y
      simp [not_le, Prod.swap]
    rw [← hset]
    exact hx
  have hmain : ∀ᵐ x ∂μ, (fun x => ∫⁻ y, g y x ∂ν) x ≤ ∫⁻ y, c y ∂ν := by
    filter_upwards [hae] with x hx
    exact lintegral_mono_ae hx
  have hfin := essSup_le_of_ae_le (∫⁻ y, c y ∂ν) hmain
  simpa [hcdef] using hfin

/-- Monotone convergence of `lintegral` along the partial sums of an s-finite measure. -/
lemma lintegral_eq_iSup_partialSum {α : Type*} [MeasurableSpace α]
    (μseq : ℕ → Measure α) (G : α → ℝ≥0∞) :
    ∫⁻ x, G x ∂(Measure.sum μseq) = ⨆ k, ∫⁻ x, G x ∂(∑ n ∈ Finset.range k, μseq n) := by
  rw [lintegral_sum_measure, ENNReal.tsum_eq_iSup_nat]
  apply iSup_congr
  intro k
  exact (lintegral_finsetSum_measure (Finset.range k) G μseq).symm

/-- Minkowski's integral inequality for `ℝ≥0∞`-valued functions, `1 < p`, s-finite `μ`. -/
theorem lintegral_rpow_lintegral_le_of_sfinite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [SFinite μ]
    {p : ℝ} (hp1 : 1 < p) {g : β → α → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ x, (∫⁻ y, g y x ∂ν) ^ p ∂μ) ^ (1 / p)
      ≤ ∫⁻ y, (∫⁻ x, g y x ^ p ∂μ) ^ (1 / p) ∂ν := by
  set h : α → ℝ≥0∞ := fun x => ∫⁻ y, g y x ∂ν with hhdef
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, g y x ^ p ∂μ) ^ (1 / p) ∂ν with hRdef
  suffices hmain : (∫⁻ x, h x ^ p ∂μ) ^ (1 / p) ≤ R by
    simpa [hhdef, hRdef] using hmain
  have hpartial : ∀ G : α → ℝ≥0∞, (∫⁻ x, G x ∂μ)
      = ⨆ k, ∫⁻ x, G x ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n) := by
    intro G
    have h1 : (∫⁻ x, G x ∂μ) = ∫⁻ x, G x ∂(Measure.sum (sfiniteSeq μ)) := by
      rw [sum_sfiniteSeq μ]
    rw [h1, lintegral_eq_iSup_partialSum (sfiniteSeq μ) G]
  have key : ∀ k : ℕ, (∫⁻ x, h x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p)
      ≤ ∫⁻ y, (∫⁻ x, g y x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) ∂ν := by
    intro k
    have hfin : IsFiniteMeasure (∑ n ∈ Finset.range k, sfiniteSeq μ n) := inferInstance
    have hk := lintegral_rpow_lintegral_le_of_finite (α := α) (β := β)
      (ν := ν) (μ := (∑ n ∈ Finset.range k, sfiniteSeq μ n : Measure α)) hp1 hg
    simpa [hhdef] using hk
  calc (∫⁻ x, h x ^ p ∂μ) ^ (1 / p)
      = (⨆ k, ∫⁻ x, h x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) := by
        rw [hpartial (fun x => h x ^ p)]
    _ = ⨆ k, (∫⁻ x, h x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) :=
        ENNReal.iSup_rpow (by positivity)
    _ ≤ ⨆ k, ∫⁻ y, (∫⁻ x, g y x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) ∂ν :=
        iSup_le fun k => (key k).trans (le_iSup (fun k =>
          ∫⁻ y, (∫⁻ x, g y x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) ∂ν) k)
    _ ≤ ∫⁻ y, ⨆ k, (∫⁻ x, g y x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) ∂ν :=
        iSup_le fun k => lintegral_mono fun y => le_iSup (fun k =>
          (∫⁻ x, g y x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p)) k
    _ = ∫⁻ y, (⨆ k, ∫⁻ x, g y x ^ p ∂(∑ n ∈ Finset.range k, sfiniteSeq μ n)) ^ (1 / p) ∂ν := by
        apply lintegral_congr; intro y
        rw [ENNReal.iSup_rpow (by positivity)]
    _ = R := by
        rw [hRdef]
        apply lintegral_congr; intro y
        rw [hpartial (fun x => g y x ^ p)]

/-- Minkowski's integral inequality for `ℝ≥0∞`-valued functions. -/
theorem lintegral_lintegral_le_lintegral_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [SFinite μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : β → α → ℝ≥0∞}
    (hg : AEMeasurable (Function.uncurry g) (ν.prod μ)) :
    eLpNorm (fun x => ∫⁻ y, g y x ∂ν) p μ ≤ ∫⁻ y, eLpNorm (fun x => g y x) p μ ∂ν := by
  have key : ∀ {g : β → α → ℝ≥0∞}, Measurable (Function.uncurry g) →
      eLpNorm (fun x => ∫⁻ y, g y x ∂ν) p μ ≤ ∫⁻ y, eLpNorm (fun x => g y x) p μ ∂ν := by
    intro g hg
    have hLm : AEStronglyMeasurable (fun x => ∫⁻ y, g y x ∂ν) μ :=
      (Measurable.lintegral_prod_right' (ν := ν) (hg.comp measurable_swap)).aestronglyMeasurable
    have hsl : ∀ y, AEStronglyMeasurable (fun x => g y x) μ := fun y =>
      (hg.comp measurable_prodMk_left).aestronglyMeasurable
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · subst hp1
      have hR : ∫⁻ y, eLpNorm (fun x => g y x) 1 μ ∂ν = ∫⁻ y, ∫⁻ x, g y x ∂μ ∂ν := by
        apply lintegral_congr; intro y
        rw [eLpNorm_one_eq_lintegral_enorm (hsl y)]
        exact lintegral_congr (fun x => enorm_eq_self _)
      have hL : eLpNorm (fun x => ∫⁻ y, g y x ∂ν) 1 μ
          = ∫⁻ x, ∫⁻ y, g y x ∂ν ∂μ := by
        rw [eLpNorm_one_eq_lintegral_enorm hLm]
        exact lintegral_congr (fun x => enorm_eq_self _)
      rw [hL, hR]
      exact le_of_eq (lintegral_lintegral_swap (hg.comp measurable_swap).aemeasurable)
    · rcases eq_or_ne p ∞ with htop | htop
      · subst htop
        have h1 : eLpNorm (fun x => ∫⁻ y, g y x ∂ν) ∞ μ
            = essSup (fun x => ∫⁻ y, g y x ∂ν) μ := by
          rw [eLpNorm_exponent_top hLm, eLpNormEssSup_eq_essSup_enorm]
          apply essSup_congr_ae; filter_upwards with x; rw [enorm_eq_self]
        have h2 : ∫⁻ y, eLpNorm (fun x => g y x) ∞ μ ∂ν
            = ∫⁻ y, essSup (fun x => g y x) μ ∂ν := by
          apply lintegral_congr; intro y
          rw [eLpNorm_exponent_top (hsl y), eLpNormEssSup_eq_essSup_enorm]
          apply essSup_congr_ae; filter_upwards with x; rw [enorm_eq_self]
        rw [h1, h2]
        exact essSup_lintegral_le_lintegral_essSup_of_measurable hg
      · have hpne0 : p ≠ 0 := by
          intro h; rw [h] at hp; exact absurd hp (by norm_num)
        have hpr : 1 < p.toReal := by
          rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop]
          exact hp1
        have hL : eLpNorm (fun x => ∫⁻ y, g y x ∂ν) p μ
            = (∫⁻ x, (∫⁻ y, g y x ∂ν) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 htop hLm]
          simp only [enorm_eq_self]
        have hR : ∫⁻ y, eLpNorm (fun x => g y x) p μ ∂ν
            = ∫⁻ y, (∫⁻ x, g y x ^ p.toReal ∂μ) ^ (1 / p.toReal) ∂ν := by
          apply lintegral_congr; intro y
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 htop (hsl y)]
          simp only [enorm_eq_self]
        rw [hL, hR]
        exact lintegral_rpow_lintegral_le_of_sfinite hpr hg
  obtain ⟨G, hG, hGae⟩ := hg
  set g' : β → α → ℝ≥0∞ := fun y x => G (y, x) with hg'def
  have huncurry : Function.uncurry g' = G := by
    rw [hg'def]; funext z; rfl
  have hG' : Measurable (Function.uncurry g') := huncurry ▸ hG
  have hgoal := key hG'
  have hGae'' : Function.uncurry g =ᵐ[ν.prod μ] Function.uncurry g' := huncurry ▸ hGae
  have hswap : Function.uncurry (fun x y => g y x) =ᵐ[μ.prod ν] Function.uncurry (fun x y => g' y x) := by
    have hGae' : Function.uncurry g =ᵐ[(μ.prod ν).map Prod.swap] Function.uncurry g' := by
      rw [Measure.prod_swap]; exact hGae''
    have hthis := ae_eq_comp (f := (Prod.swap : α × β → β × α)) measurable_swap.aemeasurable hGae'
    have h1 : (Function.uncurry g) ∘ (Prod.swap : α × β → β × α)
        = Function.uncurry (fun x y => g y x) := by funext z; rfl
    have h2 : (Function.uncurry g') ∘ (Prod.swap : α × β → β × α)
        = Function.uncurry (fun x y => g' y x) := by funext z; rfl
    rw [h1, h2] at hthis
    exact hthis
  have heq1 : (fun x => ∫⁻ y, g y x ∂ν) =ᵐ[μ] (fun x => ∫⁻ y, g' y x ∂ν) := by
    filter_upwards [Measure.ae_ae_eq_of_ae_eq_uncurry hswap] with x hx
    exact lintegral_congr_ae hx
  have heq2 : (fun y => eLpNorm (fun x => g y x) p μ)
      =ᵐ[ν] (fun y => eLpNorm (fun x => g' y x) p μ) := by
    filter_upwards [Measure.ae_ae_eq_of_ae_eq_uncurry hGae''] with y hy
    exact eLpNorm_congr_ae hy
  rw [eLpNorm_congr_ae heq1, lintegral_congr_ae heq2]
  exact hgoal

open MeasureTheory in
theorem eLpNorm_integral_le_lintegral_eLpNorm_sfinite {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [SFinite μ] {p : ENNReal} (hp : 1 ≤ p)
    {f : β → α → ℂ} (hf : AEStronglyMeasurable (Function.uncurry f) (ν.prod μ)) :
    eLpNorm (fun x => ∫ y, f y x ∂ν) p μ ≤ lintegral ν (fun y => eLpNorm (fun x => f y x) p μ) := by
  set g : β → α → ℝ≥0∞ := fun y x => ‖f y x‖ₑ with hgdef
  have hg : AEMeasurable (Function.uncurry g) (ν.prod μ) := hf.enorm
  have hm := lintegral_lintegral_le_lintegral_lintegral (μ := μ) (ν := ν) (g := g) hp hg
  have h1 : eLpNorm (fun x => ∫ y, f y x ∂ν) p μ
      ≤ eLpNorm (fun x => ∫⁻ y, g y x ∂ν) p μ := by
    have hfi : AEStronglyMeasurable (fun x : α => ∫ y, f y x ∂ν) μ :=
      hf.prod_swap.integral_prod_right'
    have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (μ := μ) (f := fun x : α => ∫ y, f y x ∂ν)
      (g := fun x : α => ∫⁻ y, g y x ∂ν) (c := 1) hfi ?_ p
    · simpa using hh
    · filter_upwards with x
      simp only [ENNReal.coe_one, one_mul]
      rw [hgdef]
      simpa using enorm_integral_le_lintegral_enorm (fun y => f y x)
  have h2 : ∀ᵐ y ∂ν, eLpNorm (fun x => g y x) p μ = eLpNorm (fun x => f y x) p μ := by
    filter_upwards [hf.prodMk_left] with y hy
    apply le_antisymm
    · have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (μ := μ) (f := fun x : α => g y x)
        (g := fun x : α => f y x) (c := 1) hy.enorm.aestronglyMeasurable ?_ p
      · simpa using hh
      · filter_upwards with x
        simp only [ENNReal.coe_one, one_mul, hgdef, enorm_eq_self]
        exact le_refl _
    · have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (μ := μ) (f := fun x : α => f y x)
        (g := fun x : α => g y x) (c := 1) hy ?_ p
      · simpa using hh
      · filter_upwards with x
        simp only [ENNReal.coe_one, one_mul, hgdef, enorm_eq_self]
        exact le_refl _
  calc eLpNorm (fun x => ∫ y, f y x ∂ν) p μ
      ≤ eLpNorm (fun x => ∫⁻ y, g y x ∂ν) p μ := h1
    _ ≤ lintegral ν (fun y => eLpNorm (fun x => g y x) p μ) := hm
    _ = lintegral ν (fun y => eLpNorm (fun x => f y x) p μ) := by
        exact lintegral_congr_ae h2

end Commons.Analysis.Integral