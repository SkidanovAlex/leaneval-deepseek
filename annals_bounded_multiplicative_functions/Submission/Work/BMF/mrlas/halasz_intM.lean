import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_abel
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_plancherel
import Submission.Work.BMF.IntM.abel_id

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

namespace Work.BMF.mrlas

/-!
# Ramaré's inequality `(ineqMg1)`

`∫_1^x ‖Mf f t‖ log t / t² dt ≤ 2 ∫_1^x ‖Kf f t‖ / t² dt + O(1)` for `‖f n‖ ≤ 1`.

Writing `A(t) = ∫_1^t Mf f u / u du`, the Abel identity gives `Mf f t log t = Kf f t + A(t)`, so
`‖Mf f t‖ log t ≤ ‖Kf f t‖ + ‖A(t)‖`, and `‖A(t)‖ ≤ ∫_1^t ‖Mf f u‖/u du`.  Integrating the
`1/t²` weight against that primitive against the bound `log t ≥ 2` (valid for `t ≥ e²`) produces
the factor `2`.  The calculus core is `intM_primitive_div_sq_le`.
-/

/-! ## Measurability of the step functions -/

lemma intM_measurable_Mf (f : ℕ → ℂ) : Measurable (fun t : ℝ => Work.BMF.Mf f t) := by
  have h1 : Measurable (fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, f n) := measurable_of_countable _
  have h3 : Measurable (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) :=
    h1.comp Nat.measurable_floor
  simpa only [Work.BMF.Mf] using h3

lemma intM_measurable_Kf (f : ℕ → ℂ) : Measurable (fun t : ℝ => Work.BMF.Kf f t) := by
  have h1 : Measurable (fun m : ℕ => ∑ n ∈ Finset.Icc 1 m, f n * (Real.log n : ℂ)) :=
    measurable_of_countable _
  have h3 : Measurable (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n * (Real.log n : ℂ)) :=
    h1.comp Nat.measurable_floor
  simpa only [Work.BMF.Kf] using h3

/-! ## Integrability helpers -/

/-- A measurable function that is bounded on `(a,b]` is interval integrable on `[a,b]`. -/
lemma intM_intervalIntegrable_of_bound {g : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    (hb : ∀ t ∈ Set.Ioc a b, ‖g t‖ ≤ C) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine IntegrableOn.of_bound ?_ hg C (ae_restrict_of_forall_mem measurableSet_Ioc hb)
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top

/-- Real version of `intM_intervalIntegrable_of_bound`. -/
lemma intM_intervalIntegrable_of_bound_real {g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    (hb : ∀ t ∈ Set.Ioc a b, |g t| ≤ C) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine IntegrableOn.of_bound ?_ hg C (ae_restrict_of_forall_mem measurableSet_Ioc hb)
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top

/-- Multiplying an interval-integrable function by a continuous function preserves interval
integrability (product form). -/
lemma intM_intervalIntegrable_mul_continuousOn {g u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hu : ContinuousOn u (Set.Icc a b)) :
    IntervalIntegrable (fun t => g t * u t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hg ⊢
  exact hg.mul_continuousOn hu isCompact_Icc

/-- Dividing an interval-integrable function by a continuous nonvanishing function preserves
interval integrability. -/
lemma intM_intervalIntegrable_div_continuousOn {g u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hu : ContinuousOn u (Set.Icc a b))
    (hne : ∀ t ∈ Set.Icc a b, u t ≠ 0) :
    IntervalIntegrable (fun t => g t / u t) volume a b := by
  have h := intM_intervalIntegrable_mul_continuousOn hab hg (hu.inv₀ hne)
  simpa only [div_eq_mul_inv, Pi.inv_apply] using h

/-- `t ↦ Mf f t / t` is interval integrable on `[1,x]` when `‖f n‖ ≤ 1`. -/
lemma intM_intervalIntegrable_Mf_div (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Work.BMF.Mf f t / t) volume 1 x := by
  have hmeas : Measurable (fun t : ℝ => Work.BMF.Mf f t / ((t : ℝ) : ℂ)) :=
    (intM_measurable_Mf f).div Complex.continuous_ofReal.measurable
  refine intM_intervalIntegrable_of_bound hx hmeas.aestronglyMeasurable.restrict (C := 1) ?_
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht.1
  have hnorm : ‖((t : ℝ) : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  rw [norm_div, hnorm, div_le_one ht0]
  exact Work.BMF.Mf_norm_le_x f hf t (le_of_lt ht0)

/-- `t ↦ ‖Mf f t‖ / t` is interval integrable on `[1,x]` when `‖f n‖ ≤ 1`. -/
lemma intM_intervalIntegrable_norm_Mf_div (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ}
    (hx : 1 ≤ x) : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t) volume 1 x := by
  have hmeas : Measurable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t) :=
    ((intM_measurable_Mf f).norm).div measurable_id
  refine intM_intervalIntegrable_of_bound_real hx hmeas.aestronglyMeasurable.restrict (C := 1) ?_
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht.1
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) ht0.le), div_le_one ht0]
  exact Work.BMF.Mf_norm_le_x f hf t (le_of_lt ht0)

/-- `t ↦ ‖Mf f t‖ / t^2` is interval integrable on `[1,x]` when `‖f n‖ ≤ 1`. -/
lemma intM_intervalIntegrable_norm_Mf_div_sq (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ}
    (hx : 1 ≤ x) : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t ^ 2) volume 1 x := by
  have hmeas : Measurable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t ^ 2) :=
    ((intM_measurable_Mf f).norm).div (by fun_prop : Measurable fun t : ℝ => t ^ 2)
  refine intM_intervalIntegrable_of_bound_real hx hmeas.aestronglyMeasurable.restrict (C := 1) ?_
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht.1
  have h1 : ‖Work.BMF.Mf f t‖ ≤ t := Work.BMF.Mf_norm_le_x f hf t (le_of_lt ht0)
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (by positivity))]
  rw [div_le_one (by positivity : (0 : ℝ) < t ^ 2)]
  nlinarith [ht.1]

/-- `u ↦ ‖Mf f u‖ / u` is right continuous at every `y ≥ 1`. -/
lemma intM_continuousWithinAt_norm_Mf_div (f : ℕ → ℂ) {y : ℝ} (hy : 1 ≤ y) :
    ContinuousWithinAt (fun u : ℝ => ‖Work.BMF.Mf f u‖ / u) (Set.Ioi y) y := by
  have hy0 : y ≠ 0 := by linarith
  have heq : ∀ᶠ u in 𝓝[Set.Ioi y] y, Work.BMF.Mf f u = Work.BMF.Mf f y := by
    have hIio : Set.Iio ((⌊y⌋₊ : ℝ) + 1) ∈ 𝓝 y :=
      IsOpen.mem_nhds isOpen_Iio (Nat.lt_floor_add_one y)
    have h1 : Set.Iio ((⌊y⌋₊ : ℝ) + 1) ∈ 𝓝[Set.Ioi y] y :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _ hIio
    filter_upwards [h1, self_mem_nhdsWithin] with u hu huy
    rw [Set.mem_Ioi] at huy
    have hyle : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hfloor : ⌊u⌋₊ = ⌊y⌋₊ := by
      apply le_antisymm
      · rw [← Nat.lt_succ_iff]
        refine (Nat.floor_lt (a := u) (n := ⌊y⌋₊ + 1) (by linarith : (0 : ℝ) ≤ u)).mpr ?_
        simpa using hu
      · exact Nat.le_floor (le_trans hyle (le_of_lt huy))
    rw [Work.BMF.Mf_floor f u, Work.BMF.Mf_floor f y, hfloor]
  have hcont : ContinuousWithinAt (fun u : ℝ => ‖Work.BMF.Mf f y‖ / u) (Set.Ioi y) y :=
    continuousWithinAt_const.div continuousWithinAt_id hy0
  exact hcont.congr_of_eventuallyEq (by filter_upwards [heq] with u hu; rw [hu]) rfl

/-- `‖Kf f t‖ ≤ t log t` for `t ≥ 1` when `‖f n‖ ≤ 1`. -/
lemma intM_norm_Kf_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (le_of_lt ht0)
  calc ‖Work.BMF.Kf f t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖f n * (Real.log n : ℂ)‖ := by
        rw [Work.BMF.Kf]; exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖f n‖ * Real.log n := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1))]
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊t⌋₊, Real.log t := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
        have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have h2 : (n : ℝ) ≤ t := le_trans (by exact_mod_cast hn2) hfloor
        calc ‖f n‖ * Real.log n ≤ 1 * Real.log t :=
              mul_le_mul (hf n) (Real.log_le_log (by linarith) h2) (Real.log_nonneg h1)
                (by norm_num)
          _ = Real.log t := by ring
    _ = (⌊t⌋₊ : ℝ) * Real.log t := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
        simp
    _ ≤ t * Real.log t := mul_le_mul_of_nonneg_right hfloor hlogt

/-- `t ↦ ‖Kf f t‖ / t^2` is interval integrable on `[1,x]` when `‖f n‖ ≤ 1`. -/
lemma intM_intervalIntegrable_norm_Kf_div_sq (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ}
    (hx : 1 ≤ x) : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Kf f t‖ / t ^ 2) volume 1 x := by
  have hmeas : Measurable (fun t : ℝ => ‖Work.BMF.Kf f t‖ / t ^ 2) :=
    ((intM_measurable_Kf f).norm).div (by fun_prop : Measurable fun t : ℝ => t ^ 2)
  refine intM_intervalIntegrable_of_bound_real hx hmeas.aestronglyMeasurable.restrict
    (C := Real.log x) ?_
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogle : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) ht.2
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (by positivity))]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
  calc ‖Work.BMF.Kf f t‖ ≤ t * Real.log t := intM_norm_Kf_le f hf ht1
    _ ≤ t * Real.log x := mul_le_mul_of_nonneg_left hlogle (by linarith)
    _ ≤ Real.log x * t ^ 2 := by
        calc t * Real.log x ≤ t ^ 2 * Real.log x :=
              mul_le_mul_of_nonneg_right (by nlinarith [ht1]) hlogx
          _ = Real.log x * t ^ 2 := by ring

/-- `t ↦ ‖Mf f t‖ log t / t^2` is interval integrable on `[1,x]` when `‖f n‖ ≤ 1`. -/
lemma intM_intervalIntegrable_norm_Mf_log_div_sq (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) volume 1 x := by
  have hmeas : Measurable (fun t : ℝ => ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) :=
    (((intM_measurable_Mf f).norm).mul Real.measurable_log).div
      (by fun_prop : Measurable fun t : ℝ => t ^ 2)
  refine intM_intervalIntegrable_of_bound_real hx hmeas.aestronglyMeasurable.restrict
    (C := Real.log x) ?_
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogle : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) ht.2
  have h1 : ‖Work.BMF.Mf f t‖ ≤ t := Work.BMF.Mf_norm_le_x f hf t (by linarith)
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (norm_nonneg _) hlogt) (by positivity))]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
  calc ‖Work.BMF.Mf f t‖ * Real.log t ≤ t * Real.log t :=
        mul_le_mul_of_nonneg_right h1 hlogt
    _ ≤ t * Real.log x := mul_le_mul_of_nonneg_left hlogle (by linarith)
    _ ≤ Real.log x * t ^ 2 := by
        calc t * Real.log x ≤ t ^ 2 * Real.log x :=
              mul_le_mul_of_nonneg_right (by nlinarith [ht1]) (Real.log_nonneg hx)
          _ = Real.log x * t ^ 2 := by ring

/-! ## The calculus core -/

/-- **Calculus core.**  Let `0 ≤ h ≤ 1` on `[1,x]`, let `h` be interval integrable there and
right continuous at every point of `(c,x)`.  Then for `1 ≤ c ≤ x`,
`∫_c^x (∫_1^t h) / t² dt ≤ (c-1)/c + ∫_c^x h(t)/t dt`.

The proof differentiates `t ↦ -(\∫_1^t h)/t`, whose right derivative exists because `h` is right
continuous, and applies the fundamental theorem of calculus for right derivatives. -/
lemma intM_primitive_div_sq_le (h : ℝ → ℝ) {c x : ℝ} (hc : 1 ≤ c) (hcx : c ≤ x)
    (hh0 : ∀ t ∈ Set.Icc (1 : ℝ) x, 0 ≤ h t) (hh1 : ∀ t ∈ Set.Icc (1 : ℝ) x, h t ≤ 1)
    (hh_int : IntervalIntegrable h volume 1 x)
    (hh_rc : ∀ y ∈ Set.Ioo c x, ContinuousWithinAt h (Set.Ioi y) y) :
    (∫ t in c..x, (∫ u in (1 : ℝ)..t, h u) / t ^ 2) ≤ (c - 1) / c + ∫ t in c..x, h t / t := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hc0 hcx
  have hIcc : IntegrableOn h (Set.Icc (1 : ℝ) x) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (le_trans hc hcx)).mp hh_int
  have hHcont1 : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, h u) (Set.Icc (1 : ℝ) x) := by
    have h1 := intervalIntegral.continuousOn_primitive (a := (1 : ℝ)) (b := x) hIcc
    exact h1.congr (fun y hy => intervalIntegral.integral_of_le hy.1)
  have hHcont : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, h u) (Set.Icc c x) :=
    hHcont1.mono (Set.Icc_subset_Icc_left hc)
  have hderiv : ∀ y ∈ Set.Ioo c x,
      HasDerivWithinAt (fun t : ℝ => -((∫ u in (1 : ℝ)..t, h u) / t))
        ((∫ u in (1 : ℝ)..y, h u) / y ^ 2 - h y / y) (Set.Ioi y) y := by
    intro y hy
    have hy1 : (1 : ℝ) ≤ y := le_trans hc (le_of_lt hy.1)
    have hyx : y ≤ x := le_of_lt hy.2
    have hy0 : y ≠ 0 := by
      have : (0 : ℝ) < y := lt_of_lt_of_le hc0 (le_of_lt hy.1)
      linarith
    have hInt_y : IntervalIntegrable h volume 1 y :=
      hh_int.mono_set (by
        rw [Set.uIcc_of_le hy1, Set.uIcc_of_le (le_trans hy1 hyx)]
        exact Set.Icc_subset_Icc_right hyx)
    have hmem : Set.Ioc (1 : ℝ) x ∈ 𝓝[Set.Ioi y] y := by
      have hIoo : Set.Ioo (1 : ℝ) x ∈ 𝓝 y :=
        IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [hc, hy.1], hy.2⟩
      have h1 : Set.Ioo (1 : ℝ) x ∈ 𝓝[Set.Ioi y] y :=
        (Filter.le_def.mp nhdsWithin_le_nhds) _ hIoo
      exact Filter.mem_of_superset h1 (fun z hz => ⟨hz.1, le_of_lt hz.2⟩)
    have hAE : AEStronglyMeasurable h (volume.restrict (Set.Ioc (1 : ℝ) x)) :=
      hh_int.1.aestronglyMeasurable
    have hprim := intervalIntegral.integral_hasDerivWithinAt_right (a := (1 : ℝ)) (b := y)
      (s := Set.Ici y) (t := Set.Ioi y) hInt_y ⟨Set.Ioc (1 : ℝ) x, hmem, hAE⟩ (hh_rc y hy)
    have hprim' : HasDerivWithinAt (fun t : ℝ => ∫ u in (1 : ℝ)..t, h u) (h y) (Set.Ioi y) y :=
      hprim.mono Set.Ioi_subset_Ici_self
    have hdiv := hprim'.div ((hasDerivAt_id y).hasDerivWithinAt) hy0
    have hneg := hdiv.neg
    convert hneg using 1
    · ext t; simp
    · simp only [id_eq]
      field_simp
      ring
  have hprim_int_x : IntervalIntegrable (fun t : ℝ => ∫ u in (1 : ℝ)..t, h u) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (le_trans hc hcx)]
  have hprim_int : IntervalIntegrable (fun t : ℝ => ∫ u in (1 : ℝ)..t, h u) volume c x :=
    hprim_int_x.mono_set (by
      rw [Set.uIcc_of_le hcx, Set.uIcc_of_le (le_trans hc hcx)]
      exact Set.Icc_subset_Icc_left hc)
  have hih : IntervalIntegrable (fun t : ℝ => (∫ u in (1 : ℝ)..t, h u) / t ^ 2) volume c x :=
    intM_intervalIntegrable_div_continuousOn hcx hprim_int (by fun_prop)
      (fun t ht => by have : (0 : ℝ) < t := lt_of_lt_of_le hc0 ht.1; positivity)
  have hh_int_c : IntervalIntegrable h volume c x :=
    hh_int.mono_set (by
      rw [Set.uIcc_of_le hcx, Set.uIcc_of_le (le_trans hc hcx)]
      exact Set.Icc_subset_Icc_left hc)
  have hiht : IntervalIntegrable (fun t : ℝ => h t / t) volume c x :=
    intM_intervalIntegrable_div_continuousOn hcx hh_int_c continuousOn_id
      (fun t ht => by have : (0 : ℝ) < t := lt_of_lt_of_le hc0 ht.1; positivity)
  have hIderiv : IntervalIntegrable
      (fun t : ℝ => (∫ u in (1 : ℝ)..t, h u) / t ^ 2 - h t / t) volume c x :=
    hih.sub hiht
  have hFcont : ContinuousOn (fun t : ℝ => -((∫ u in (1 : ℝ)..t, h u) / t)) (Set.Icc c x) :=
    (hHcont.div continuousOn_id (fun t ht => by
      have : (0 : ℝ) < t := lt_of_lt_of_le hc0 ht.1; positivity)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := c) (b := x) hcx
    hFcont hderiv hIderiv
  have hsub := intervalIntegral.integral_sub hih hiht
  have hval : (∫ t in c..x, ((∫ u in (1 : ℝ)..t, h u) / t ^ 2 - h t / t))
      = -((∫ u in (1 : ℝ)..x, h u) / x) + (∫ u in (1 : ℝ)..c, h u) / c := by
    simpa using hFTC
  rw [hsub] at hval
  have hHx : 0 ≤ (∫ u in (1 : ℝ)..x, h u) :=
    intervalIntegral.integral_nonneg (le_trans hc hcx) (fun u hu => hh0 u hu)
  have hHx_div : 0 ≤ (∫ u in (1 : ℝ)..x, h u) / x := div_nonneg hHx hx0.le
  have hHc_le : (∫ u in (1 : ℝ)..c, h u) / c ≤ (c - 1) / c := by
    have hInt_c : IntervalIntegrable h volume 1 c :=
      hh_int.mono_set (by
        rw [Set.uIcc_of_le hc, Set.uIcc_of_le (le_trans hc hcx)]
        exact Set.Icc_subset_Icc_right hcx)
    have hmono : (∫ u in (1 : ℝ)..c, h u) ≤ ∫ u in (1 : ℝ)..c, (1 : ℝ) :=
      intervalIntegral.integral_mono_on hc hInt_c intervalIntegrable_const
        (fun u hu => hh1 u ⟨hu.1, le_trans hu.2 hcx⟩)
    have h1 : (∫ u in (1 : ℝ)..c, (1 : ℝ)) = c - 1 := by simp
    rw [h1] at hmono
    exact div_le_div_of_nonneg_right hmono hc0.le
  calc (∫ t in c..x, (∫ u in (1 : ℝ)..t, h u) / t ^ 2)
      = (∫ t in c..x, h t / t) - (∫ u in (1 : ℝ)..x, h u) / x
        + (∫ u in (1 : ℝ)..c, h u) / c := by linarith
    _ ≤ (∫ t in c..x, h t / t) + (∫ u in (1 : ℝ)..c, h u) / c := by linarith
    _ ≤ (∫ t in c..x, h t / t) + (c - 1) / c := by linarith
    _ = (c - 1) / c + ∫ t in c..x, h t / t := by ring

/-! ## The main inequality -/

theorem halasz_intM :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x : ℝ, 1 ≤ x →
      (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) ≤
        2 * (∫ t in (1 : ℝ)..x, ‖Work.BMF.Kf f t‖ / t ^ 2) + C := by
  refine ⟨6, by norm_num, ?_⟩
  intro f hf x hx
  have hLint : IntervalIntegrable
      (fun t : ℝ => ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) volume 1 x :=
    intM_intervalIntegrable_norm_Mf_log_div_sq f hf hx
  have hKint : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Kf f t‖ / t ^ 2) volume 1 x :=
    intM_intervalIntegrable_norm_Kf_div_sq f hf hx
  have hKnn : 0 ≤ ∫ t in (1 : ℝ)..x, ‖Work.BMF.Kf f t‖ / t ^ 2 :=
    intervalIntegral.integral_nonneg hx (fun t _ => by positivity)
  rcases le_total x (Real.exp 2) with hxc | hxc
  · -- small case: the whole integral is bounded by `4`
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) x,
        ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2 ≤ 2 * ((1 : ℝ) / t) := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hlog2 : Real.log t ≤ 2 := by
        calc Real.log t ≤ Real.log (Real.exp 2) :=
              Real.log_le_log ht0 (le_trans ht.2 hxc)
          _ = 2 := Real.log_exp 2
      have h1 : ‖Work.BMF.Mf f t‖ ≤ t := Work.BMF.Mf_norm_le_x f hf t (le_of_lt ht0)
      have h2 : ‖Work.BMF.Mf f t‖ * Real.log t ≤ t * Real.log t :=
        mul_le_mul_of_nonneg_right h1 hlog0
      have h3 : ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2 ≤ t * Real.log t / t ^ 2 :=
        div_le_div_of_nonneg_right h2 (by positivity)
      have h4 : t * Real.log t / t ^ 2 = Real.log t / t := by
        field_simp
      rw [h4] at h3
      have h5 : Real.log t / t ≤ 2 * ((1 : ℝ) / t) := by
        have h7 : (2 : ℝ) * ((1 : ℝ) / t) = 2 / t := by ring
        rw [h7]
        exact div_le_div_of_nonneg_right hlog2 ht0.le
      linarith
    have h2int : IntervalIntegrable (fun t : ℝ => 2 * ((1 : ℝ) / t)) volume 1 x :=
      ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hx]
        exact ContinuousOn.mul continuousOn_const
          (ContinuousOn.div continuousOn_const continuousOn_id
            (fun t ht => by linarith [ht.1])))
    have hmono : (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
        ≤ ∫ t in (1 : ℝ)..x, 2 * ((1 : ℝ) / t) :=
      intervalIntegral.integral_mono_on hx hLint h2int hpt
    have hval : (∫ t in (1 : ℝ)..x, 2 * ((1 : ℝ) / t)) = 2 * Real.log x := by
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos one_pos (lt_of_lt_of_le one_pos hx)]
      simp
    have hlogx : Real.log x ≤ 2 := by
      calc Real.log x ≤ Real.log (Real.exp 2) :=
            Real.log_le_log (lt_of_lt_of_le one_pos hx) hxc
        _ = 2 := Real.log_exp 2
    have hfin : (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) ≤ 4 := by
      have := hmono
      rw [hval] at this
      linarith
    linarith
  · -- main case: `Real.exp 2 ≤ x`
    have hce : Real.exp 2 ≤ x := hxc
    have hc1 : (1 : ℝ) ≤ Real.exp 2 := by
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have hLint1 : IntervalIntegrable
        (fun t : ℝ => ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) volume 1 (Real.exp 2) :=
      hLint.mono_set (by
        rw [Set.uIcc_of_le hc1, Set.uIcc_of_le hx]
        exact Set.Icc_subset_Icc_right hce)
    have hLint2 : IntervalIntegrable
        (fun t : ℝ => ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) volume (Real.exp 2) x :=
      hLint.mono_set (by
        rw [Set.uIcc_of_le hce, Set.uIcc_of_le hx]
        exact Set.Icc_subset_Icc_left hc1)
    have hsplit : (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
        = (∫ t in (1 : ℝ)..Real.exp 2, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
          + ∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2 :=
      (intervalIntegral.integral_add_adjacent_intervals hLint1 hLint2).symm
    -- the piece over `[1, e²]`
    have hsmall : (∫ t in (1 : ℝ)..Real.exp 2, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) ≤ 4 := by
      have hpt : ∀ t ∈ Set.Icc (1 : ℝ) (Real.exp 2),
          ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2 ≤ 2 * ((1 : ℝ) / t) := by
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := ht.1
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
        have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
        have hlog2 : Real.log t ≤ 2 := by
          calc Real.log t ≤ Real.log (Real.exp 2) := Real.log_le_log ht0 ht.2
            _ = 2 := Real.log_exp 2
        have h1 : ‖Work.BMF.Mf f t‖ ≤ t := Work.BMF.Mf_norm_le_x f hf t (le_of_lt ht0)
        have h2 : ‖Work.BMF.Mf f t‖ * Real.log t ≤ t * Real.log t :=
          mul_le_mul_of_nonneg_right h1 hlog0
        have h3 : ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2 ≤ t * Real.log t / t ^ 2 :=
          div_le_div_of_nonneg_right h2 (by positivity)
        have h4 : t * Real.log t / t ^ 2 = Real.log t / t := by
          field_simp
        rw [h4] at h3
        have h5 : Real.log t / t ≤ 2 * ((1 : ℝ) / t) := by
          have h7 : (2 : ℝ) * ((1 : ℝ) / t) = 2 / t := by ring
          rw [h7]
          exact div_le_div_of_nonneg_right hlog2 ht0.le
        linarith
      have h2int : IntervalIntegrable (fun t : ℝ => 2 * ((1 : ℝ) / t)) volume 1 (Real.exp 2) :=
        ContinuousOn.intervalIntegrable (by
          rw [Set.uIcc_of_le hc1]
          exact ContinuousOn.mul continuousOn_const
            (ContinuousOn.div continuousOn_const continuousOn_id
              (fun t ht => by linarith [ht.1])))
      have hmono := intervalIntegral.integral_mono_on hc1 hLint1 h2int hpt
      have hval : (∫ t in (1 : ℝ)..Real.exp 2, 2 * ((1 : ℝ) / t)) = 4 := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos one_pos (Real.exp_pos 2), div_one, Real.log_exp]
        norm_num
      linarith
    -- Abel's identity gives the pointwise bound
    have hAbel : ∀ t ∈ Set.Icc (Real.exp 2) x,
        ‖Work.BMF.Mf f t‖ * Real.log t
          ≤ ‖Work.BMF.Kf f t‖ + ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := le_trans hc1 ht.1
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
      have h := Work.BMF.halasz_abel f t ht1
      have h' : Work.BMF.Mf f t * (Real.log t : ℂ)
          = Work.BMF.Kf f t + ∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u := by
        rw [sub_eq_iff_eq_add, add_comm] at h
        exact h
      calc ‖Work.BMF.Mf f t‖ * Real.log t
          = ‖Work.BMF.Mf f t * (Real.log t : ℂ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
        _ = ‖Work.BMF.Kf f t + ∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ := by rw [h']
        _ ≤ ‖Work.BMF.Kf f t‖ + ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ := norm_add_le _ _
    have hApipe : ∀ t ∈ Set.Icc (Real.exp 2) x,
        ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖
          ≤ ∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := le_trans hc1 ht.1
      calc ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖
          ≤ ∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u / u‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht1
        _ = ∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u := by
            refine intervalIntegral.integral_congr (fun u hu => ?_)
            rw [Set.uIcc_of_le ht1] at hu
            have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    -- continuity facts
    have hAcont : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u)
        (Set.Icc (Real.exp 2) x) := by
      have hIcc : IntegrableOn (fun u : ℝ => Work.BMF.Mf f u / u) (Set.Icc (1 : ℝ) x) volume :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp (intM_intervalIntegrable_Mf_div f hf hx)
      have h1 := intervalIntegral.continuousOn_primitive (a := (1 : ℝ)) (b := x) hIcc
      have h2 : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u)
          (Set.Icc (1 : ℝ) x) :=
        h1.congr (fun y hy => intervalIntegral.integral_of_le hy.1)
      exact h2.mono (Set.Icc_subset_Icc_left hc1)
    have hHcont2 : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u)
        (Set.Icc (Real.exp 2) x) := by
      have hIcc : IntegrableOn (fun u : ℝ => ‖Work.BMF.Mf f u‖ / u) (Set.Icc (1 : ℝ) x) volume :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp
          (intM_intervalIntegrable_norm_Mf_div f hf hx)
      have h1 := intervalIntegral.continuousOn_primitive (a := (1 : ℝ)) (b := x) hIcc
      have h2 : ContinuousOn (fun t : ℝ => ∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u)
          (Set.Icc (1 : ℝ) x) :=
        h1.congr (fun y hy => intervalIntegral.integral_of_le hy.1)
      exact h2.mono (Set.Icc_subset_Icc_left hc1)
    have hKtail : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Kf f t‖ / t ^ 2)
        volume (Real.exp 2) x :=
      hKint.mono_set (by
        rw [Set.uIcc_of_le hce, Set.uIcc_of_le hx]
        exact Set.Icc_subset_Icc_left hc1)
    have hAtail : IntervalIntegrable
        (fun t : ℝ => ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2)
        volume (Real.exp 2) x := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hce]
      exact ContinuousOn.div hAcont.norm (by fun_prop)
        (fun t ht => by have : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht.1; positivity)
    have hHtail : IntervalIntegrable
        (fun t : ℝ => (∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u) / t ^ 2)
        volume (Real.exp 2) x := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hce]
      exact ContinuousOn.div hHcont2 (by fun_prop)
        (fun t ht => by have : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht.1; positivity)
    have hMtail : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t ^ 2)
        volume (Real.exp 2) x :=
      (intM_intervalIntegrable_norm_Mf_div_sq f hf hx).mono_set (by
        rw [Set.uIcc_of_le hce, Set.uIcc_of_le hx]
        exact Set.Icc_subset_Icc_left hc1)
    -- step 1: `L' ≤ K' + ∫ ‖A‖/t²`
    have hstep1 : (∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
        ≤ (∫ t in (Real.exp 2)..x, ‖Work.BMF.Kf f t‖ / t ^ 2)
          + ∫ t in (Real.exp 2)..x, ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2 := by
      have hpt : ∀ t ∈ Set.Icc (Real.exp 2) x,
          ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2
            ≤ ‖Work.BMF.Kf f t‖ / t ^ 2
              + ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2 := by
        intro t ht
        have ht0 : (0 : ℝ) ≤ t ^ 2 := by
          have : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht.1; positivity
        calc ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2
            ≤ (‖Work.BMF.Kf f t‖ + ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖) / t ^ 2 :=
              div_le_div_of_nonneg_right (hAbel t ht) ht0
          _ = ‖Work.BMF.Kf f t‖ / t ^ 2
              + ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2 := by ring
      calc (∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
          ≤ ∫ t in (Real.exp 2)..x, (‖Work.BMF.Kf f t‖ / t ^ 2
              + ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2) :=
            intervalIntegral.integral_mono_on hce hLint2 (hKtail.add hAtail) hpt
        _ = (∫ t in (Real.exp 2)..x, ‖Work.BMF.Kf f t‖ / t ^ 2)
              + ∫ t in (Real.exp 2)..x, ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2 :=
            intervalIntegral.integral_add hKtail hAtail
    -- step 2: `∫ ‖A‖/t² ≤ ∫ H/t²`
    have hstep2 : (∫ t in (Real.exp 2)..x,
          ‖∫ u in (1 : ℝ)..t, Work.BMF.Mf f u / u‖ / t ^ 2)
        ≤ ∫ t in (Real.exp 2)..x, (∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u) / t ^ 2 := by
      refine intervalIntegral.integral_mono_on hce hAtail hHtail (fun t ht => ?_)
      refine div_le_div_of_nonneg_right (hApipe t ht) ?_
      have : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht.1; positivity
    -- step 3: the calculus core
    have hstep3 : (∫ t in (Real.exp 2)..x, (∫ u in (1 : ℝ)..t, ‖Work.BMF.Mf f u‖ / u) / t ^ 2)
        ≤ (Real.exp 2 - 1) / Real.exp 2 + ∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ / t ^ 2 := by
      have hh0 : ∀ t ∈ Set.Icc (1 : ℝ) x, 0 ≤ ‖Work.BMF.Mf f t‖ / t := by
        intro t ht
        have : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1; positivity
      have hh1 : ∀ t ∈ Set.Icc (1 : ℝ) x, ‖Work.BMF.Mf f t‖ / t ≤ 1 := by
        intro t ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
        rw [div_le_one ht0]
        exact Work.BMF.Mf_norm_le_x f hf t (le_of_lt ht0)
      have hrc : ∀ y ∈ Set.Ioo (Real.exp 2) x,
          ContinuousWithinAt (fun u : ℝ => ‖Work.BMF.Mf f u‖ / u) (Set.Ioi y) y :=
        fun y hy => intM_continuousWithinAt_norm_Mf_div f (le_trans hc1 (le_of_lt hy.1))
      have hcore := intM_primitive_div_sq_le (fun u : ℝ => ‖Work.BMF.Mf f u‖ / u) hc1 hce
        hh0 hh1 (intM_intervalIntegrable_norm_Mf_div f hf hx) hrc
      convert hcore using 2
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [div_div, pow_two]
    -- step 4: the factor `1/2`
    have hstep4 : (∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ / t ^ 2)
        ≤ (1 / 2) * ∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hce hMtail (hLint2.const_mul (1 / 2))
        (fun t ht => ?_)
      have ht1 : (Real.exp 2) ≤ t := ht.1
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 2) ht1
      have hlog2 : 2 ≤ Real.log t := by
        calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
          _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 2) ht1
      rw [show (1 / 2) * (‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
          = ((1 / 2) * (‖Work.BMF.Mf f t‖ * Real.log t)) / t ^ 2 by ring]
      rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < t ^ 2)]
      nlinarith [norm_nonneg (Work.BMF.Mf f t)]
    -- assemble the tail bound
    have htail : (∫ t in (Real.exp 2)..x, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
        ≤ 2 * (∫ t in (Real.exp 2)..x, ‖Work.BMF.Kf f t‖ / t ^ 2) + 2 := by
      have hb : (Real.exp 2 - 1) / Real.exp 2 ≤ 1 := by
        rw [div_le_one (Real.exp_pos 2)]; linarith
      linarith [hstep1, hstep2, hstep3, hstep4, hb]
    have hK'tail : (∫ t in (Real.exp 2)..x, ‖Work.BMF.Kf f t‖ / t ^ 2)
        ≤ ∫ t in (1 : ℝ)..x, ‖Work.BMF.Kf f t‖ / t ^ 2 :=
      intervalIntegral.integral_mono_interval hc1 hce le_rfl
        (Eventually.of_forall (fun t => by positivity)) hKint
    rw [hsplit]
    linarith [hsmall, htail, hK'tail]

end Work.BMF.mrlas
