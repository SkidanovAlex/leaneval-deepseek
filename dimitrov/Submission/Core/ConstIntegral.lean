import Mathlib

noncomputable section

open scoped Real
open MeasureTheory
open Interval

namespace Submission.Core

/-- The D2 kernel denominator `1 - 2 s cos t + s²`. -/
private def kden (s t : ℝ) : ℝ := 1 - 2 * s * Real.cos t + s ^ 2

/-- `w_s(t) := (s - cos t)/(1 - 2 s cos t + s²)`, the `s`-derivative of
`(1/2) log(1 - 2 q cos t + q²)` at `q = s`. -/
private def ws (s t : ℝ) : ℝ := (s - Real.cos t) / kden s t

/-- `G(t,q) := (1/2)·log(1 - 2 q cos t + q²)` as a function of `q` for fixed `t`. -/
private def G (t q : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (kden q t)

/-- `kden q t = (q - cos t)^2 + sin^2 t`. -/
private lemma kden_sq_add_sq (q t : ℝ) : kden q t = (q - Real.cos t) ^ 2 + Real.sin t ^ 2 := by
  unfold kden
  rw [Real.sin_sq]
  ring

/-- `kden q t` is strictly positive when `sin t ≠ 0`. -/
private lemma kden_pos_of_sin_ne_zero {q t : ℝ} (h : Real.sin t ≠ 0) : 0 < kden q t := by
  rw [kden_sq_add_sq]
  positivity

private lemma kden_ne_zero_of_sin_ne_zero {q t : ℝ} (h : Real.sin t ≠ 0) : kden q t ≠ 0 :=
  (kden_pos_of_sin_ne_zero h).ne'

/-- Derivative in `q` of `G(t,q)` is `w_q(t)`. -/
private lemma hasDerivAt_G (t q : ℝ) (h : kden q t ≠ 0) :
    HasDerivAt (fun qq : ℝ => G t qq) (ws q t) q := by
  have hid2 : HasDerivAt (fun x : ℝ => 2 * x) (2 : ℝ) q := by
    simpa using (hasDerivAt_id' q).const_mul (2 : ℝ)
  have hlin : HasDerivAt (fun x : ℝ => (2 * x) * Real.cos t) (2 * Real.cos t) q := by
    simpa using hid2.mul_const (Real.cos t)
  have hin : HasDerivAt (fun x : ℝ => kden x t) (0 - 2 * Real.cos t + 2 * q) q := by
    have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ)) (0 : ℝ) q := hasDerivAt_const q _
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * q) q := by
      simpa using hasDerivAt_pow (n := 2) q
    have hs : HasDerivAt (fun x : ℝ => (1 : ℝ) - (2 * x) * Real.cos t + x ^ 2)
        (0 - 2 * Real.cos t + 2 * q) q := (h1.sub hlin).add hp
    simpa [kden] using hs
  have hlog : HasDerivAt Real.log ((kden q t)⁻¹) (kden q t) := Real.hasDerivAt_log h
  have hc : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (kden x t))
      ((1 / 2 : ℝ) * ((kden q t)⁻¹ * (0 - 2 * Real.cos t + 2 * q))) q := by
    simpa [Function.comp_def] using (hlog.comp q hin).const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((kden q t)⁻¹ * (0 - 2 * Real.cos t + 2 * q)) = ws q t := by
    unfold ws kden
    field_simp [h]
    ring
  rw [hval] at hc
  exact hc

/-- `deriv (fun q => G(t,q)) q = w_q(t)`. -/
private lemma deriv_G (t q : ℝ) (h : kden q t ≠ 0) :
    deriv (fun qq : ℝ => G t qq) q = ws q t :=
  (hasDerivAt_G t q h).deriv

/-- `G(t,cos t) - G(t,0) = (1/2)·log(sin² t)`. -/
private lemma G_sub_self (t : ℝ) : G t (Real.cos t) - G t 0 = (1 / 2 : ℝ) * Real.log (Real.sin t ^ 2) := by
  have h1 : kden (Real.cos t) t = Real.sin t ^ 2 := by
    unfold kden
    rw [Real.sin_sq]
    ring
  have h2 : kden 0 t = 1 := by unfold kden; ring
  unfold G
  rw [h1, h2]
  rw [Real.log_one]
  ring

/-- Continuity of `q ↦ w_q(t)` on a set where the denominator is nonzero. -/
private lemma continuousOn_ws (t : ℝ) {a b : ℝ}
    (h : ∀ q : ℝ, q ∈ Set.uIcc a b → kden q t ≠ 0) :
    ContinuousOn (fun q : ℝ => ws q t) (Set.uIcc a b) := by
  have hnum : ContinuousOn (fun q : ℝ => q - Real.cos t) (Set.uIcc a b) := by
    fun_prop
  have hden : ContinuousOn (fun q : ℝ => kden q t) (Set.uIcc a b) := by
    unfold kden
    fun_prop
  unfold ws
  refine ContinuousOn.div hnum hden ?_
  intro x hx
  exact h x hx

/-- Continuity of `q ↦ w_q(t)` on `[0,cos t]` when `sin t ≠ 0` and `0 ≤ cos t`. -/
private lemma continuousOn_ws_interval (t : ℝ) (hsin : Real.sin t ≠ 0) (hc : 0 ≤ Real.cos t) :
    ContinuousOn (fun q : ℝ => ws q t) (Set.Icc 0 (Real.cos t)) := by
  have hu : ContinuousOn (fun q : ℝ => ws q t) (Set.uIcc 0 (Real.cos t)) := by
    refine continuousOn_ws t ?_
    intro q hq
    exact kden_ne_zero_of_sin_ne_zero hsin
  simpa [Set.uIcc_of_le hc] using hu

/-- `q ↦ w_q(t)` is interval integrable on `[0,cos t]` when `sin t ≠ 0` and `0 ≤ cos t`. -/
private lemma intervalIntegrable_ws (t : ℝ) (hsin : Real.sin t ≠ 0) (hc : 0 ≤ Real.cos t) :
    IntervalIntegrable (fun q : ℝ => ws q t) volume 0 (Real.cos t) := by
  exact (continuousOn_ws_interval t hsin hc).intervalIntegrable_of_Icc hc

/-- The `s`-integral of `w_s(t)` over `[0, cos t]` equals `(1/2)·log(sin² t)` when
  `0 < cos t` and `sin t ≠ 0`. -/
private lemma s_integral_value (t : ℝ) (hc : 0 < Real.cos t) (hsin : Real.sin t ≠ 0) :
    (∫ s in 0..Real.cos t, ws s t) = (1 / 2 : ℝ) * Real.log (Real.sin t ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun q : ℝ => G t q)]
  · exact G_sub_self t
  · intro q hq
    exact hasDerivAt_G t q (kden_ne_zero_of_sin_ne_zero hsin)
  · exact intervalIntegrable_ws t hsin hc.le


/-- A singleton has volume zero (volume on ℝ). -/
private lemma volume_singleton_zero : (volume : Measure ℝ) {0} = 0 :=
  MeasureTheory.NullSingletonClass.measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ)

/-- Almost every real is nonzero. -/
private lemma ae_ne_zero_real : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {t : ℝ | ¬t ≠ 0} = {0} := by ext t; simp
  rw [hset]
  exact volume_singleton_zero

/-- A pointwise implication which fails only at `0` holds almost everywhere. -/
private lemma ae_of_off_zero (f g : ℝ → ℝ) (a b : ℝ)
    (hpt : ∀ t : ℝ, t ∈ Set.uIoc a b → t ≠ 0 → f t = g t) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → f t = g t := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ volume_singleton_zero
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · exfalso
    apply ht
    intro htI
    exact hpt t htI ht0

/-- `log(sin² t) / 2 = log (sin t)` pointwise (log 0 = 0 convention). -/
private lemma log_sin_sq_half (t : ℝ) : (1 / 2 : ℝ) * Real.log (Real.sin t ^ 2) = Real.log (Real.sin t) := by
  rw [Real.log_pow]
  norm_num
  ring

/-- If `t ≠ 0` and `|t| < π/2` then `sin t ≠ 0`. -/
private lemma sin_ne_zero_of_ne_zero_of_abs_lt {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| < π / 2) :
    Real.sin t ≠ 0 := by
  have ht_lt : t < π / 2 := (abs_lt.mp ht1).2
  have hneg_lt : -(π / 2) < t := (abs_lt.mp ht1).1
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · intro hs
    have hsp : 0 < Real.sin (-t) := by
      refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
      · linarith
      · nlinarith [Real.pi_pos]
    rw [Real.sin_neg] at hsp
    linarith
  · intro hs
    have hsp : 0 < Real.sin t := by
      refine Real.sin_pos_of_pos_of_lt_pi htpos ?_
      nlinarith [Real.pi_pos]
    linarith

/-- Evenness splitting of an integral over `[-π/2,π/2]`. -/
private lemma integral_even_pi (f : ℝ → ℝ) (hf : ∀ t : ℝ, f (-t) = f t)
    (hI1 : IntervalIntegrable f volume (-(π / 2)) 0)
    (hI2 : IntervalIntegrable f volume 0 (π / 2)) :
    (∫ t in -(π / 2)..(π / 2), f t) = 2 * (∫ t in 0..(π / 2), f t) := by
  have hsplit : (∫ t in -(π / 2)..(π / 2), f t)
      = (∫ t in -(π / 2)..0, f t) + (∫ t in 0..(π / 2), f t) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  rw [hsplit]
  have hc' : (∫ x in -(π / 2)..0, f (-x)) = ∫ x in 0..(π / 2), f x := by
    simpa using (intervalIntegral.integral_comp_neg (f := fun t : ℝ => f (-t)) (a := 0) (b := π / 2))
  have hneg : (∫ t in -(π / 2)..0, f t) = ∫ t in 0..(π / 2), f t := by
    rw [← hc']
    apply intervalIntegral.integral_congr
    intro x hx
    simp [hf]
  rw [hneg]
  ring

/-- Value at `t = π/2`: the degenerate inner integral. -/
private lemma inner_at_pi_div_two :
    (∫ s in 0..Real.cos (π / 2), ws s (π / 2)) =
      (1 / 2 : ℝ) * Real.log (Real.sin (π / 2) ^ 2) := by
  simp [ws]

/-- For almost every `t` in `(-π/2,π/2]` the inner integral equals `log(sin t)`. -/
private lemma ae_inner_eq_log :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.uIoc (-(π / 2)) (π / 2) →
        (∫ s in 0..Real.cos t, ws s t) = Real.log (Real.sin t) := by
  refine ae_of_off_zero (fun t => ∫ s in 0..Real.cos t, ws s t)
      (fun t => Real.log (Real.sin t)) (-(π / 2)) (π / 2) ?_
  intro t ht ht0
  have hu : Set.uIoc (-(π / 2)) (π / 2) = Set.Ioc (-(π / 2)) (π / 2) :=
    Set.uIoc_of_le (by nlinarith [Real.pi_pos])
  have htI : t ∈ Set.Ioc (-(π / 2)) (π / 2) := by simpa [hu] using ht
  have htm : -(π / 2) < t := htI.1
  have htl : t ≤ π / 2 := htI.2
  by_cases hpi : t = π / 2
  · subst t
    simpa using inner_at_pi_div_two
  · have hlt : t < π / 2 := lt_of_le_of_ne htl hpi
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨htm, hlt⟩
    have hs : Real.sin t ≠ 0 := by
      refine sin_ne_zero_of_ne_zero_of_abs_lt ht0 ?_
      exact abs_lt.mpr ⟨htm, hlt⟩
    exact (s_integral_value t hc hs).trans (log_sin_sq_half t)

/-- The integral of `t ↦ log(sin t)` over `[0,π/2]` is `-π log 2 / 2` (Mathlib). -/
private lemma integral_log_sin_half : (∫ t in 0..(π / 2), Real.log (Real.sin t)) = -Real.log 2 * (π / 2) := by
  rw [integral_log_sin_zero_pi_div_two]
  ring

/-- The outer (t-outer) integral: `∫_{t=-π/2}^{π/2} ∫_{s=0}^{cos t} w_s(t) = -π log 2`. -/
private lemma t_outer_value :
    (∫ t in -(π / 2)..(π / 2), ∫ s in 0..Real.cos t, ws s t) = -Real.pi * Real.log 2 := by
  have heq : (∫ t in -(π / 2)..(π / 2), ∫ s in 0..Real.cos t, ws s t)
      = ∫ t in -(π / 2)..(π / 2), Real.log (Real.sin t) := by
    exact intervalIntegral.integral_congr_ae ae_inner_eq_log
  rw [heq]
  have hI1 : IntervalIntegrable (fun t : ℝ => Real.log (Real.sin t)) volume (-(π / 2)) 0 := by
    exact intervalIntegrable_log_sin (a := -(π / 2)) (b := 0)
  have hI2 : IntervalIntegrable (fun t : ℝ => Real.log (Real.sin t)) volume 0 (π / 2) := by
    exact intervalIntegrable_log_sin (a := 0) (b := π / 2)
  have heven : (∫ t in -(π / 2)..(π / 2), Real.log (Real.sin t))
      = 2 * (∫ t in 0..(π / 2), Real.log (Real.sin t)) := by
    apply integral_even_pi
    · intro t
      rw [Real.sin_neg]
      simp [Real.log_abs]
    · exact hI1
    · exact hI2
  rw [heven, integral_log_sin_half]
  ring


/-- Almost every real differs from `c`. -/
private lemma ae_ne_c (c : ℝ) : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ c := by
  rw [MeasureTheory.ae_iff]
  have hset : {t : ℝ | ¬t ≠ c} = {c} := by ext t; simp
  rw [hset]
  exact NullSingletonClass.measure_singleton (μ := (volume : Measure ℝ)) c

/-- If functions agree off a single point, they agree almost everywhere. -/
private lemma ae_eq_of_off_single (f g : ℝ → ℝ) (c : ℝ)
    (h : ∀ t : ℝ, t ≠ c → f t = g t) : f =ᵐ[(volume : Measure ℝ)] g := by
  filter_upwards [ae_ne_c c] with t ht
  exact h t ht

/-- A pointwise implication which fails only at `c` holds almost everywhere. -/
private lemma ae_imp_of_off_single (f g : ℝ → ℝ) (a b c : ℝ)
    (hpt : ∀ t : ℝ, t ∈ Set.uIoc a b → t ≠ c → f t = g t) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → f t = g t := by
  filter_upwards [ae_ne_c c] with t ht
  intro htI
  exact hpt t htI ht

/-- The closed interval integral `[-a,a]` (a ≥ 0) equals the integral over ℝ of the
  function cut by `|t| ≤ a`. -/
private lemma integral_closed_cut (h : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∫ t in -a..a, h t) = ∫ t : ℝ, h t * (if |t| ≤ a then 1 else 0) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  rw [← MeasureTheory.integral_indicator (measurableSet_Ioc)]
  apply MeasureTheory.integral_congr_ae
  refine ae_eq_of_off_single (fun t : ℝ => (Set.Ioc (-a) a).indicator h t)
      (fun t : ℝ => h t * (if |t| ≤ a then 1 else 0)) (-a) ?_
  intro t ht
  by_cases hta : |t| ≤ a
  · have hmem : t ∈ Set.Ioc (-a) a := by
      constructor
      · have hge : -a ≤ t := (abs_le.mp hta).1
        exact lt_of_le_of_ne hge (Ne.symm ht)
      · exact (abs_le.mp hta).2
    simp [hmem, hta]
  · have hnot : t ∉ Set.Ioc (-a) a := by
      intro hmem
      apply hta
      exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    simp [hnot, hta]

/-- The integral over `[0,b]` (`0 ≤ b`) equals the integral over ℝ of the function cut
  by `0 ≤ s ≤ b`. -/
private lemma integral_nonneg_cut (h : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b) :
    (∫ s in 0..b, h s) = ∫ s : ℝ, h s * (if 0 ≤ s ∧ s ≤ b then 1 else 0) := by
  rw [intervalIntegral.integral_of_le hb]
  rw [← MeasureTheory.integral_indicator (measurableSet_Ioc)]
  apply MeasureTheory.integral_congr_ae
  refine ae_eq_of_off_single (fun s : ℝ => (Set.Ioc 0 b).indicator h s)
      (fun s : ℝ => h s * (if 0 ≤ s ∧ s ≤ b then 1 else 0)) 0 ?_
  intro s hs0
  by_cases hs : 0 ≤ s ∧ s ≤ b
  · have hmem : s ∈ Set.Ioc 0 b := ⟨lt_of_le_of_ne hs.1 hs0.symm, hs.2⟩
    simp [hmem, hs]
  · have hnot : s ∉ Set.Ioc 0 b := by
      intro hmem
      apply hs
      exact ⟨le_of_lt hmem.1, hmem.2⟩
    simp [hnot, hs]



/-- The double-integral region in `(s,t)`-coordinates (s outer): `0 < s ≤ 1`, `|t| ≤ arccos s`. -/
private def RSt (z : ℝ × ℝ) : Prop := 0 < z.1 ∧ z.1 ≤ 1 ∧ |z.2| ≤ Real.arccos z.1

/-- The double-integral region in `(s,t)`-coordinates (t outer): `|t| ≤ π/2`, `0 < s ≤ cos t`. -/
private def RTs (z : ℝ × ℝ) : Prop := |z.2| ≤ π / 2 ∧ 0 < z.1 ∧ z.1 ≤ Real.cos z.2

/-- Characteristic function (real-valued) of `RSt`. -/
private noncomputable def cutSt (z : ℝ × ℝ) : ℝ := by
  classical
  exact if RSt z then 1 else 0

/-- The full 2D integrand restricted to `RSt`. -/
private def Phi2 (z : ℝ × ℝ) : ℝ := ws z.1 z.2 * cutSt z

/-- Region equivalence: both descriptions of the integration region agree. -/
private lemma region_iff (z : ℝ × ℝ) : RSt z ↔ RTs z := by
  constructor
  · intro hz
    rcases hz with ⟨hs0, hs1, ht⟩
    constructor
    · have hpi : Real.arccos z.1 ≤ π / 2 := (Real.arccos_le_pi_div_two).mpr (le_of_lt hs0)
      linarith
    · constructor
      · exact hs0
      · -- z.1 ≤ cos z.2
        have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z.2)
          (Real.arccos_le_pi z.1) ht
        -- cos |t| ≤ cos (arccos s)  → cos |t| ≤ cos (arccos s)
        have hcos : Real.cos (Real.arccos z.1) = z.1 :=
          Real.cos_arccos (by linarith) (by linarith)
        -- hc: cos (arccos s) ≤ cos |t|, hmm check
        have hc' : Real.cos |z.2| ≥ Real.cos (Real.arccos z.1) := by
          -- cos_le_cos_of_nonneg_of_le_pi hx₁ hy₂ hxy gives cos y ≤ cos x for x = |t|, y = arccos s
          -- with x ≤ y: cos(y) ≤ cos(x)
          exact hc
        rw [Real.cos_abs] at hc'
        rwa [hcos] at hc'
  · intro hz
    rcases hz with ⟨hpi, hs0, hs1⟩
    constructor
    · exact hs0
    · constructor
      · have hc : z.1 ≤ Real.cos z.2 := hs1
        have hcl : Real.cos z.2 ≤ 1 := Real.cos_le_one z.2
        linarith
      · -- |t| ≤ arccos s
        have hcar : Real.arccos (Real.cos z.2) = |z.2| := by
          rw [← Real.cos_abs]
          have hle_pi : |z.2| ≤ π := by
            rcases abs_le.mp hpi with ⟨hm, hp⟩
            exact abs_le.mpr ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
          exact Real.arccos_cos (abs_nonneg z.2) hle_pi
        have hmono := Real.arccos_le_arccos hs1
        -- arccos s ≥ arccos(cos t) (since s ≤ cos t, arccos decreasing)
        rwa [hcar] at hmono

/-- Measurability of the region `RSt`. -/
private lemma measurableSet_RSt : MeasurableSet {z : ℝ × ℝ | RSt z} := by
  unfold RSt
  measurability

/-- The product cut function is measurable. -/
private lemma measurable_cutSt : Measurable cutSt := by
  have h : cutSt = ({z : ℝ × ℝ | RSt z}).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) := by
    funext z
    unfold cutSt Set.indicator
    rfl
  rw [h]
  exact measurable_const.indicator measurableSet_RSt

/-- `ws` is measurable on ℝ × ℝ. -/
private lemma measurable_ws_prod : Measurable (fun z : ℝ × ℝ => ws z.1 z.2) := by
  unfold ws kden
  fun_prop

/-- `Phi2` is measurable on ℝ × ℝ. -/
private lemma measurable_Phi2 : Measurable Phi2 := by
  unfold Phi2
  exact measurable_ws_prod.mul measurable_cutSt


/-- The cut `cutSt (s, ·)` on the range `0 < s ≤ 1` is the `t`-window cut. -/
private lemma cutSt_eq (s t : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    cutSt (s, t) = if |t| ≤ Real.arccos s then 1 else 0 := by
  classical
  unfold cutSt RSt
  by_cases ht : |t| ≤ Real.arccos s <;> simp [ht, hs0, hs1]

/-- The cut `cutSt (s, t)` vanishes unless `0 < s ≤ 1`. -/
private lemma cutSt_zero (s t : ℝ) (h : ¬(0 < s ∧ s ≤ 1)) : cutSt (s, t) = 0 := by
  classical
  unfold cutSt RSt
  have hneg : ¬(0 < s ∧ s ≤ 1 ∧ |t| ≤ Real.arccos s) := by
    intro hc
    exact h ⟨hc.1, hc.2.1⟩
  simp [hneg]

/-- For `s ∈ (0,1]` the inner interval integral equals the full-space integral of the
  region-cut integrand (in `t`). -/
private lemma inner_eq_section (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∫ t in (-Real.arccos s)..Real.arccos s, ws s t) = ∫ t : ℝ, Phi2 (s, t) := by
  classical
  rw [integral_closed_cut (fun t : ℝ => ws s t) (Real.arccos s) (Real.arccos_nonneg s)]
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all volume
  intro t
  change ws s t * (if |t| ≤ Real.arccos s then 1 else 0) = Phi2 (s, t)
  rw [Phi2, cutSt_eq s t hs0 hs1]

/-- The s-outer (original) iterated integral equals the iterated full-space integral. -/
private lemma prod_eq_lhs :
    (∫ s in 0..1, ∫ t in (-Real.arccos s)..Real.arccos s, ws s t)
      = ∫ s : ℝ, ∫ t : ℝ, Phi2 (s, t) := by
  classical
  have h1 : (∫ s in 0..1, ∫ t in (-Real.arccos s)..Real.arccos s, ws s t)
      = (∫ s in Set.Ioc 0 1, ∫ t in (-Real.arccos s)..Real.arccos s, ws s t) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [h1]
  have h2 : (∫ s in Set.Ioc 0 1, ∫ t in (-Real.arccos s)..Real.arccos s, ws s t)
      = ∫ s in Set.Ioc 0 1, (∫ t : ℝ, Phi2 (s, t)) := by
    apply setIntegral_congr_ae measurableSet_Ioc
    apply MeasureTheory.ae_of_all volume
    intro s hs
    exact inner_eq_section s hs.1 hs.2
  rw [h2]
  -- now ∫ over (0,1] of ψ equals ∫_ℝ of ψ since ψ vanishes outside (0,1]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc 0 1)
  intro s hs
  have hs' : ¬(0 < s ∧ s ≤ 1) := by simpa using hs
  -- ψ(s) = ∫_t Phi2 (s, t); show = 0
  apply MeasureTheory.integral_eq_zero_of_ae
  apply MeasureTheory.ae_of_all volume
  intro t
  change Phi2 (s, t) = 0
  rw [Phi2, cutSt_zero s t hs']
  ring

/-- `cos t ≥ 0` when `|t| ≤ π/2`. -/
private lemma cos_nonneg_of_abs_le {t : ℝ} (ht : |t| ≤ π / 2) : 0 ≤ Real.cos t := by
  rw [← Real.cos_abs]
  exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos, abs_nonneg t], ht⟩

/-- For `s ≠ 0` the cut along `s` at fixed `t` with `|t| ≤ π/2` is the interval cut
  `0 ≤ s ≤ cos t`. -/
private lemma cut_eq_s (s t : ℝ) (hs0 : s ≠ 0) (ht : |t| ≤ π / 2) :
    cutSt (s, t) = (if 0 ≤ s ∧ s ≤ Real.cos t then 1 else 0) := by
  classical
  unfold cutSt
  by_cases hR : RSt (s, t)
  · have hRT := (region_iff (s, t)).mp hR
    have hscond : 0 ≤ s ∧ s ≤ Real.cos t := by
      rcases hRT with ⟨htle, hspos, hsle⟩
      exact ⟨le_of_lt hspos, hsle⟩
    simp [hR, hscond]
  · have hcond : ¬(0 ≤ s ∧ s ≤ Real.cos t) := by
      intro hscond
      apply hR
      apply (region_iff (s, t)).mpr
      exact ⟨ht, lt_of_le_of_ne hscond.1 (Ne.symm hs0), hscond.2⟩
    simp [hR, hcond]

/-- The inner `s`-integral over `[0,cos t]` equals the full-space section integral
  when `|t| ≤ π/2`. -/
private lemma inner_t_eq_section (t : ℝ) (ht : |t| ≤ π / 2) :
    (∫ s in 0..Real.cos t, ws s t) = ∫ s : ℝ, Phi2 (s, t) := by
  classical
  rw [integral_nonneg_cut (fun s : ℝ => ws s t) (Real.cos t) (cos_nonneg_of_abs_le ht)]
  apply MeasureTheory.integral_congr_ae
  apply ae_eq_of_off_single _ _ 0
  intro s hs0
  change ws s t * (if 0 ≤ s ∧ s ≤ Real.cos t then 1 else 0) = Phi2 (s, t)
  rw [Phi2, cut_eq_s s t hs0 ht]

/-- The t-outer iterated integral equals the iterated full-space integral. -/
private lemma prod_eq_t :
    (∫ t in -(π / 2)..(π / 2), ∫ s in 0..Real.cos t, ws s t)
      = ∫ t : ℝ, ∫ s : ℝ, Phi2 (s, t) := by
  classical
  have h1 : (∫ t in -(π / 2)..(π / 2), ∫ s in 0..Real.cos t, ws s t)
      = (∫ t in Set.Ioc (-(π / 2)) (π / 2), ∫ s in 0..Real.cos t, ws s t) := by
    rw [intervalIntegral.integral_of_le (by nlinarith [Real.pi_pos])]
  rw [h1]
  have h2 : (∫ t in Set.Ioc (-(π / 2)) (π / 2), ∫ s in 0..Real.cos t, ws s t)
      = ∫ t in Set.Ioc (-(π / 2)) (π / 2), (∫ s : ℝ, Phi2 (s, t)) := by
    apply setIntegral_congr_ae measurableSet_Ioc
    apply MeasureTheory.ae_of_all volume
    intro t ht
    -- |t| ≤ π/2 from membership in (-π/2, π/2]
    have htle : |t| ≤ π / 2 := by
      rcases ht with ⟨htm, htp⟩
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_pos]
    exact inner_t_eq_section t htle
  rw [h2]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-(π / 2)) (π / 2))
  intro t ht
  apply MeasureTheory.integral_eq_zero_of_ae
  apply MeasureTheory.ae_of_all volume
  intro s
  change Phi2 (s, t) = 0
  unfold Phi2
  have hcut : cutSt (s, t) = 0 := by
    unfold cutSt
    have hnotR : ¬RSt (s, t) := by
      intro hR
      apply ht
      have hRT := (region_iff (s, t)).mp hR
      have htle : |t| ≤ π / 2 := by simpa using hRT.1
      have hspos : 0 < s := by simpa using hRT.2.1
      have hsle : s ≤ Real.cos t := by simpa using hRT.2.2
      constructor
      · rcases abs_le.mp htle with ⟨h1, h2⟩
        by_cases hpi : t = -(π / 2)
        · subst t
          have : s ≤ 0 := by
            simpa [Real.cos_neg, Real.cos_pi_div_two] using hsle
          linarith
        · exact lt_of_le_of_ne h1 (Ne.symm hpi)
      · exact (abs_le.mp htle).2
    simp [hnotR]
  simp [hcut]


/-- If `cos t > 0` and `|t| ≤ π/2` then in fact `|t| < π/2`. -/
private lemma abs_lt_pi_div_two_of_pos_cos {t : ℝ} (htc : 0 < Real.cos t) (ht : |t| ≤ π / 2) :
    |t| < π / 2 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact hlt
  · exfalso
    have habs : t = π / 2 ∨ t = -(π / 2) :=
      (abs_eq (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)).mp heq
    rcases habs with rfl | rfl
    · rw [Real.cos_pi_div_two] at htc
      linarith
    · rw [Real.cos_neg, Real.cos_pi_div_two] at htc
      linarith

/-- Points of `RTs` automatically have `|t| < π/2`. -/
private lemma abs_lt_of_RTs {s t : ℝ} (h : RTs (s, t)) : |t| < π / 2 := by
  rcases h with ⟨htle, hs0, hsle⟩
  exact abs_lt_pi_div_two_of_pos_cos (lt_of_lt_of_le hs0 hsle) htle

/-- `cutSt` is the characteristic function of the set `{z | RTs z}`. -/
private lemma cutSt_eq_set (z : ℝ × ℝ) :
    cutSt z = ({z : ℝ × ℝ | RTs z}).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) z := by
  classical
  unfold cutSt
  by_cases h : z ∈ {z : ℝ × ℝ | RTs z}
  · have hR : RSt z := (region_iff z).mpr h
    simp [h, hR]
  · have hR : ¬ RSt z := by
      intro hR
      exact h ((region_iff z).mp hR)
    simp [h, hR]

/-- For `|t| ≤ π/2`, `RTs (s,t)` is equivalent to `s ∈ (0, cos t]`. -/
private lemma RTs_iff_mem_Ioc (s t : ℝ) (ht : |t| ≤ π / 2) :
    RTs (s, t) ↔ s ∈ Set.Ioc 0 (Real.cos t) := by
  simp [RTs, ht, Set.mem_Ioc]

/-- For `|t| ≤ π/2`, `Phi2 (s,t)` is the restriction of `ws(·,t)` to `(0,cos t]`. -/
private lemma Phi2_eq_indicator (s t : ℝ) (ht : |t| ≤ π / 2) :
    Phi2 (s, t) = (Set.Ioc 0 (Real.cos t)).indicator (fun q : ℝ => ws q t) s := by
  classical
  unfold Phi2
  rw [cutSt_eq_set]
  by_cases hmem : s ∈ Set.Ioc 0 (Real.cos t)
  · have hset : (s, t) ∈ {z : ℝ × ℝ | RTs z} := (RTs_iff_mem_Ioc s t ht).mpr hmem
    simp [hmem, hset]
  · have hset : (s, t) ∉ {z : ℝ × ℝ | RTs z} := by
      intro hs
      exact hmem ((RTs_iff_mem_Ioc s t ht).mp hs)
    simp [hmem, hset]

/-- `Phi2` vanishes for `|t| ≥ π/2` (the region is empty there). -/
private lemma Phi2_zero_of_abs_ge {s t : ℝ} (ht : π / 2 ≤ |t|) : Phi2 (s, t) = 0 := by
  unfold Phi2
  have hc : cutSt (s, t) = 0 := by
    classical
    rw [cutSt_eq_set]
    have hnot : (s, t) ∉ {z : ℝ × ℝ | RTs z} := by
      intro hR
      exact (not_lt_of_ge ht) (abs_lt_of_RTs hR)
    simp [hnot]
  simp [hc]

/-- For every `t ≠ 0` the section `s ↦ Phi2(s,t)` is integrable. -/
private lemma section_integrable_of_ne_zero (t : ℝ) (ht0 : t ≠ 0) :
    Integrable (fun s : ℝ => Phi2 (s, t)) volume := by
  by_cases htlt : |t| < π / 2
  · have hsin : Real.sin t ≠ 0 := sin_ne_zero_of_ne_zero_of_abs_lt ht0 htlt
    have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo (abs_lt.mp htlt)
    have hteq : (fun s : ℝ => Phi2 (s, t)) =
        (Set.Ioc 0 (Real.cos t)).indicator (fun q : ℝ => ws q t) := by
      funext s
      exact Phi2_eq_indicator s t (le_of_lt htlt)
    rw [hteq]
    refine (MeasureTheory.integrable_indicator_iff (s := Set.Ioc 0 (Real.cos t))
      (f := fun q : ℝ => ws q t) ?_).mpr ?_
    · exact measurableSet_Ioc
    · have hcont : ContinuousOn (fun q : ℝ => ws q t) (Set.Icc 0 (Real.cos t)) :=
        continuousOn_ws_interval t hsin hcos.le
      have hIcc : IntegrableOn (fun q : ℝ => ws q t) (Set.Icc 0 (Real.cos t)) volume :=
        ContinuousOn.integrableOn_Icc hcont
      exact hIcc.mono_set Set.Ioc_subset_Icc_self
  · have htge : π / 2 ≤ |t| := le_of_not_gt htlt
    have hz : (fun s : ℝ => Phi2 (s, t)) = 0 := by
      funext s
      exact Phi2_zero_of_abs_ge htge
    rw [hz]
    exact integrable_zero ℝ ℝ volume

/-- Sections are integrable for almost every `t`. -/
private lemma ae_section_integrable :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun s : ℝ => Phi2 (s, t)) volume := by
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null _ (NullSingletonClass.measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))
  intro t ht
  by_contra ht0
  exact ht (section_integrable_of_ne_zero t ht0)

/-- `Phi2` vanishes when `|t| > π/2`, hence so does its section norm integral. -/
private lemma section_norm_integral_zero_of_abs_gt (t : ℝ) (ht : π / 2 < |t|) :
    (∫ s : ℝ, ‖Phi2 (s, t)‖) = 0 := by
  calc
    (∫ s : ℝ, ‖Phi2 (s, t)‖) = ∫ s : ℝ, (0 : ℝ) := by
      apply MeasureTheory.integral_congr_ae
      apply MeasureTheory.ae_of_all volume
      intro s
      have hphi : Phi2 (s, t) = 0 := Phi2_zero_of_abs_ge (le_of_lt ht)
      simp [hphi]
    _ = 0 := by simp

/-- Pointwise: the norm of the section equals the indicator-cut norm. -/
private lemma norm_Phi2_eq_indicator (s t : ℝ) (ht : |t| ≤ π / 2) :
    ‖Phi2 (s, t)‖ = (Set.Ioc 0 (Real.cos t)).indicator (fun q : ℝ => ‖ws q t‖) s := by
  classical
  rw [Phi2_eq_indicator s t ht]
  by_cases hmem : s ∈ Set.Ioc 0 (Real.cos t)
  · simp [hmem]
  · simp [hmem]

/-- For `|t| ≤ π/2` the section norm integral is the interval integral of `‖ws‖`. -/
private lemma section_norm_integral (t : ℝ) (ht : |t| ≤ π / 2) :
    (∫ s : ℝ, ‖Phi2 (s, t)‖) = ∫ s in 0..Real.cos t, ‖ws s t‖ := by
  have hc : 0 ≤ Real.cos t := cos_nonneg_of_abs_le ht
  calc
    (∫ s : ℝ, ‖Phi2 (s, t)‖)
        = ∫ s : ℝ, (Set.Ioc 0 (Real.cos t)).indicator (fun q : ℝ => ‖ws q t‖) s := by
          apply MeasureTheory.integral_congr_ae
          apply MeasureTheory.ae_of_all volume
          intro s
          exact norm_Phi2_eq_indicator s t ht
    _ = ∫ s in Set.Ioc 0 (Real.cos t), ‖ws s t‖ := by
          exact MeasureTheory.integral_indicator
            (measurableSet_Ioc : MeasurableSet (Set.Ioc 0 (Real.cos t)))
    _ = ∫ s in 0..Real.cos t, ‖ws s t‖ := by
          exact (intervalIntegral.integral_of_le hc).symm

/-- On `(0,cos t]` the function `ws(·,t)` is nonpositive, so `‖ws‖ = -ws`. -/
private lemma abs_ws_integral (t : ℝ) (hc : 0 < Real.cos t) (hs : Real.sin t ≠ 0) :
    (∫ s in 0..Real.cos t, ‖ws s t‖) = -(1 / 2 : ℝ) * Real.log (Real.sin t ^ 2) := by
  have hcongr : (∫ s in 0..Real.cos t, ‖ws s t‖) = ∫ s in 0..Real.cos t, -ws s t := by
    apply intervalIntegral.integral_congr
    intro s hsI
    change ‖ws s t‖ = -ws s t
    rw [Real.norm_eq_abs]
    have hs' : s ∈ Set.Icc 0 (Real.cos t) := by
      simpa [Set.uIcc_of_le hc.le] using hsI
    have hsle : s ≤ Real.cos t := hs'.2
    have hD : 0 < kden s t := kden_pos_of_sin_ne_zero (q := s) hs
    have hw : ws s t ≤ 0 := by
      unfold ws
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsle) (le_of_lt hD)
    rw [abs_of_nonpos hw]
  rw [hcongr]
  rw [intervalIntegral.integral_neg]
  rw [s_integral_value t hc hs]
  ring

/-- Candidate for the t-outer norm integral: `-log(sin t)` on `(-π/2, π/2]`, zero off it. -/
private noncomputable def hcut (t : ℝ) : ℝ :=
  (Set.Ioc (-(π / 2)) (π / 2)).indicator (fun u : ℝ => -Real.log (Real.sin u)) t

/-- `hcut` is integrable over the real line. -/
private lemma integrable_hcut : Integrable hcut volume := by
  have hOnIoc : IntegrableOn (fun u : ℝ => -Real.log (Real.sin u))
      (Set.Ioc (-(π / 2)) (π / 2)) volume := by
    have hLog : IntegrableOn (fun u : ℝ => Real.log (Real.sin u))
        (Set.Ioc (-(π / 2)) (π / 2)) volume :=
      (intervalIntegrable_log_sin (a := -(π / 2)) (b := π / 2)).1
    exact hLog.neg
  unfold hcut
  exact (MeasureTheory.integrable_indicator_iff (s := Set.Ioc (-(π / 2)) (π / 2))
    (f := fun u : ℝ => -Real.log (Real.sin u)) (measurableSet_Ioc)).mpr hOnIoc

/-- For `t ≠ 0` with `|t| ≠ π/2` the section norm integral equals `hcut t`. -/
private lemma section_norm_value (t : ℝ) (ht0 : t ≠ 0) (htpi : |t| ≠ π / 2) :
    (∫ s : ℝ, ‖Phi2 (s, t)‖) = hcut t := by
  rcases lt_or_gt_of_ne htpi with hlt | hgt
  · have htle : |t| ≤ π / 2 := le_of_lt hlt
    have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo (abs_lt.mp hlt)
    have hsin : Real.sin t ≠ 0 := sin_ne_zero_of_ne_zero_of_abs_lt ht0 hlt
    calc
      (∫ s : ℝ, ‖Phi2 (s, t)‖) = ∫ s in 0..Real.cos t, ‖ws s t‖ := section_norm_integral t htle
      _ = -(1 / 2 : ℝ) * Real.log (Real.sin t ^ 2) := abs_ws_integral t hcos hsin
      _ = -Real.log (Real.sin t) := by
          rw [Real.log_pow]
          ring
      _ = hcut t := by
          have hmem : t ∈ Set.Ioc (-(π / 2)) (π / 2) :=
            ⟨(abs_lt.mp hlt).1, le_of_lt (abs_lt.mp hlt).2⟩
          simp [hcut, hmem]
  · have hzero : (∫ s : ℝ, ‖Phi2 (s, t)‖) = 0 := section_norm_integral_zero_of_abs_gt t hgt
    have hcut0 : hcut t = 0 := by
      have hmem : ¬ t ∈ Set.Ioc (-(π / 2)) (π / 2) := by
        intro hmem
        rcases hmem with ⟨htl, htr⟩
        have hle : |t| ≤ π / 2 := abs_le.mpr ⟨le_of_lt htl, htr⟩
        linarith
      simp [hcut, hmem]
    rw [hzero, hcut0]

/-- The t-outer norm integral is a.e. equal to `hcut`. -/
private lemma H_eq_hcut_ae :
    (fun t : ℝ => ∫ s : ℝ, ‖Phi2 (s, t)‖) =ᵐ[volume] hcut := by
  filter_upwards [ae_ne_c 0, ae_ne_c (π / 2), ae_ne_c (-(π / 2))] with t ht0 htp htn
  have htpi : |t| ≠ π / 2 := by
    intro h
    have habs : t = π / 2 ∨ t = -(π / 2) :=
      (abs_eq (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)).mp h
    rcases habs with h1 | h2
    · exact htp h1
    · exact htn h2
  exact section_norm_value t ht0 htpi

/-- The t-outer norm integral is integrable. -/
private lemma outer_integrable :
    Integrable (fun t : ℝ => ∫ s : ℝ, ‖Phi2 (s, t)‖) volume := by
  exact MeasureTheory.Integrable.congr (hf := integrable_hcut) (H_eq_hcut_ae.symm)

/-- **Integrability of `Phi2` on `ℝ × ℝ` (w.r.t. product volume).** -/
private lemma integrable_Phi2 : Integrable Phi2 (volume.prod volume) := by
  exact (MeasureTheory.integrable_prod_iff'
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := Phi2) (h1f := measurable_Phi2.aestronglyMeasurable)).mpr
    ⟨ae_section_integrable, outer_integrable⟩


/-- The double integral equals both iterated full-space integrals (swap). -/
private lemma swap_region :
    (∫ s in 0..1, ∫ t in (-Real.arccos s)..Real.arccos s, ws s t)
      = (∫ t in -(π / 2)..(π / 2), ∫ s in 0..Real.cos t, ws s t) := by
  rw [prod_eq_lhs, prod_eq_t]
  rw [show (∫ s : ℝ, ∫ t : ℝ, Phi2 (s, t)) = ∫ z : ℝ × ℝ, Phi2 z by
      exact (MeasureTheory.integral_prod Phi2 integrable_Phi2).symm]
  rw [show (∫ t : ℝ, ∫ s : ℝ, Phi2 (s, t)) = ∫ z : ℝ × ℝ, Phi2 z by
      exact (MeasureTheory.integral_prod_symm Phi2 integrable_Phi2).symm]

/-- **Constant computation.**  `∫_0^1 ∫_{-arccos s}^{arccos s} w_s = -π log 2`
where `w_s(t) := (s - cos t)/(1 - 2s cos t + s²)`. -/
theorem const_integral :
    (∫ s in 0..1,
      ∫ t in (-Real.arccos s)..Real.arccos s,
        (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2))
      = -Real.pi * Real.log 2 := by
  change (∫ s in 0..1, ∫ t in (-Real.arccos s)..Real.arccos s, ws s t)
      = -Real.pi * Real.log 2
  rw [swap_region]
  exact t_outer_value

