import Mathlib

/-!
# D2-L1: layer-cake identity for the single-arc integral

With `G(t,q) := (1/2)·log(1 - 2q·cos t + q²)` (so `G(t,q) = log‖1-qe^{it}‖`
and `G(t,0) = 0`) and `w_s(t) := ∂G/∂q (t,s) = (s - cos t)/(1 - 2s cos t+s²)`,
the fundamental theorem in `s` gives `G(t,q(t)) = ∫_0^{q(t)} w_s(t) ds`, and
Fubini/Tonelli over `s ∈ [0,1]`, `t ∈ [a,b]` yields

    ∫_a^b G(t,q(t)) dt = ∫_0^1 ( ∫_a^b (if s < q t then w_s(t) else 0) dt ) ds.
-/

noncomputable section

open scoped Real
open MeasureTheory
open Interval

namespace Submission.Core

/-- The squared modulus denominator `D(s,t) = 1 - 2s cos t + s² = |s - e^{it}|²`. -/
private def D (s t : ℝ) : ℝ := 1 - 2 * s * Real.cos t + s ^ 2

/-- `w(s,t) = ∂_s (1/2) log D(s,t)`. -/
private def w (s t : ℝ) : ℝ := (s - Real.cos t) / D s t

/-- `G(t,q) := (1/2)·log(1 - 2q cos t + q²)`. -/
private def G (t q : ℝ) : ℝ := (1 / 2) * Real.log (1 - 2 * q * Real.cos t + q ^ 2)

/-- The truncated integrand of the right-hand side: `F(t,s) = 1_{s<q t}·w(s,t)`. -/
private def F (q : ℝ → ℝ) (t s : ℝ) : ℝ := if s < q t then w s t else 0

private lemma D_eq_sq_sin (s t : ℝ) : D s t = (s - Real.cos t) ^ 2 + Real.sin t ^ 2 := by
  unfold D
  rw [show (s - Real.cos t) ^ 2 + Real.sin t ^ 2 =
      s ^ 2 - 2 * s * Real.cos t + (Real.cos t ^ 2 + Real.sin t ^ 2) by ring]
  rw [Real.cos_sq_add_sin_sq]
  ring

private lemma D_nonneg (s t : ℝ) : 0 ≤ D s t := by
  rw [D_eq_sq_sin]
  positivity

/-- `D(s,t) ≥ (1-s)²` for `0 ≤ s`. -/
private lemma D_ge_one_sub_sq (s t : ℝ) (hs : 0 ≤ s) : (1 - s) ^ 2 ≤ D s t := by
  unfold D
  have hc : 0 ≤ 1 - Real.cos t := by
    exact sub_nonneg.mpr (Real.cos_le_one t)
  have h : 0 ≤ 2 * s * (1 - Real.cos t) := by positivity
  nlinarith

/-- `D(s,t) > 0` on `0 ≤ s ≤ 1` when `cos t ≠ 1`. -/
private lemma D_pos_of_cos_ne_one (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : Real.cos t ≠ 1) : 0 < D s t := by
  by_cases hseq : s = 1
  · subst s
    have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hpos : 0 < 2 - 2 * Real.cos t := by
      have hc2 : ¬ (2 - 2 * Real.cos t ≤ 0) := by
        intro h
        have hcge : 1 ≤ Real.cos t := by nlinarith
        have hceq : Real.cos t = 1 := le_antisymm hc1 hcge
        exact ht hceq
      linarith
    unfold D
    linarith
  · have hslt : s < 1 := lt_of_le_of_ne hs1 hseq
    have hpos : 0 < (1 - s) ^ 2 := by positivity
    have hle : (1 - s) ^ 2 ≤ D s t := D_ge_one_sub_sq s t hs0
    exact lt_of_lt_of_le hpos hle

/-- `G(t,0) = 0`. -/
private lemma G_zero (t : ℝ) : G t 0 = 0 := by
  unfold G
  simp

/-- `w(s,t)` is the partial derivative in `s` of `G(t,s) = (1/2) log D(s,t)` wherever `D ≠ 0`. -/
private lemma hasDerivAt_G_w (t s : ℝ) (hs : D s t ≠ 0) :
    HasDerivAt (fun x => G t x) (w s t) s := by
  have hDdiff : HasDerivAt (fun x : ℝ => D x t) (2 * s - 2 * Real.cos t) s := by
    unfold D
    have hid : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
    have hB : HasDerivAt (fun x : ℝ => (2 * Real.cos t) * x) (2 * Real.cos t) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * Real.cos t))
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
      have h : HasDerivAt (fun x : ℝ => x * x) (1 * s + s * 1) s := hid.mul hid
      convert h using 1
      · ext x; ring
      · ring
    have hAll : HasDerivAt (fun x : ℝ => 1 - (2 * Real.cos t) * x + x ^ 2)
        (0 - 2 * Real.cos t + 2 * s) s := by
      exact ((hasDerivAt_const s (1 : ℝ)).sub hB).add hsq
    convert hAll using 1
    · ext x; ring
    · ring
  have hLog : HasDerivAt (fun x : ℝ => Real.log (D x t)) ((2 * s - 2 * Real.cos t) / D s t) s :=
    hDdiff.log hs
  have hhalf : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (D x t))
      ((1 / 2 : ℝ) * ((2 * s - 2 * Real.cos t) / D s t)) s := hLog.const_mul (1 / 2 : ℝ)
  exact hhalf.congr_deriv (by
    unfold w
    field_simp [hs])

/-- continuity of `s ↦ w s t` on `0 ≤ s ≤ 1` when `cos t ≠ 1`. -/
private lemma continuousOn_w (t : ℝ) (ht : Real.cos t ≠ 1) :
    ContinuousOn (fun s : ℝ => w s t) (Set.Icc (0 : ℝ) 1) := by
  unfold w
  have hnum : ContinuousOn (fun s : ℝ => s - Real.cos t) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hden : ContinuousOn (fun s : ℝ => D s t) (Set.Icc (0 : ℝ) 1) := by
    unfold D
    fun_prop
  have hden0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, D s t ≠ 0 := by
    intro s hs
    exact ne_of_gt (D_pos_of_cos_ne_one s t hs.1 hs.2 ht)
  exact hnum.div hden hden0

/-- Fundamental theorem of calculus for `s ↦ G(t, s)`:
    `∫_0^q w(s,t) ds = G(t,q)` for `0 ≤ q ≤ 1`, `cos t ≠ 1`. -/
private lemma ftc_inner (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : Real.cos t ≠ 1) :
    (∫ s in 0..q, w s t) = G t q := by
  have hderiv : ∀ s ∈ [[0, q]], HasDerivAt (fun x => G t x) (w s t) s := by
    intro s hs
    apply hasDerivAt_G_w
    apply ne_of_gt
    have hs0 : 0 ≤ s := by
      rcases Set.mem_uIcc.mp hs with ⟨h01, h02⟩ | ⟨h11, h12⟩
      · exact h01
      · linarith
    have hs1 : s ≤ 1 := by
      rcases Set.mem_uIcc.mp hs with ⟨h01, h02⟩ | ⟨h11, h12⟩
      · exact le_trans h02 hq1
      · linarith
    exact D_pos_of_cos_ne_one s t hs0 hs1 ht
  have hint : IntervalIntegrable (fun s => w s t) volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    have hsub : [[0, q]] ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h01, h02⟩ | ⟨h11, h12⟩
      · exact ⟨h01, le_trans h02 hq1⟩
      · have hx0 : 0 ≤ x := by linarith
        exact ⟨hx0, by linarith⟩
    exact (continuousOn_w t ht).mono hsub
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => G t x)
    (f' := fun s => w s t) hderiv hint
  rw [hmain]
  simp [G_zero]

/-- `s ↦ w s t` is interval-integrable on `[0,1]` when `cos t ≠ 1`. -/
private lemma ii_w01 (t : ℝ) (ht : Real.cos t ≠ 1) :
    IntervalIntegrable (fun s => w s t) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  convert continuousOn_w t ht using 1
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- `s ↦ w s t` is measurable. -/
private lemma measurable_w_s (t : ℝ) : Measurable (fun s : ℝ => w s t) := by
  unfold w
  apply Measurable.div
  · fun_prop
  · unfold D
    fun_prop

/-- `s ↦ 1_{s<q}·w(s,t)` is interval-integrable on `[0,1]` when `cos t ≠ 1`. -/
private lemma ii_phi01 (t q : ℝ) (ht : Real.cos t ≠ 1) :
    IntervalIntegrable (fun s => if s < q then w s t else 0) volume 0 1 := by
  apply IntervalIntegrable.mono_fun (f := fun s => w s t) (a := 0) (b := 1)
  · exact ii_w01 t ht
  · have hmeas : Measurable (fun s => if s < q then w s t else 0) := by
      exact Measurable.ite measurableSet_Iio (measurable_w_s t) measurable_const
    exact hmeas.aestronglyMeasurable
  · refine ae_of_all _ (fun x => ?_)
    by_cases hx : x < q
    · simp [hx]
    · simp [hx]

/-- `t ↦ ∫_0^1 1_{s<q}·w(s,t) ds` equals `G(t,q)` for `0≤q≤1`, `cos t≠1`. -/
private lemma G_eq_int_cut (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : Real.cos t ≠ 1) :
    (∫ s in 0..1, (if s < q then w s t else 0)) = G t q := by
  let φ : ℝ → ℝ := fun s => if s < q then w s t else 0
  have hφ01 : IntervalIntegrable φ volume 0 1 := by
    simpa [φ] using ii_phi01 t q ht
  have hφ0q : IntervalIntegrable φ volume 0 q := by
    apply hφ01.mono_set'
    intro x hx
    rw [Set.uIoc_of_le hq0] at hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, le_trans hx.2 hq1⟩
  have hφq1 : IntervalIntegrable φ volume q 1 := by
    apply hφ01.mono_set'
    intro x hx
    rw [Set.uIoc_of_le hq1] at hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨lt_of_le_of_lt hq0 hx.1, hx.2⟩
  have hsplit : (∫ s in 0..q, φ s) + (∫ s in q..1, φ s) = ∫ s in 0..1, φ s :=
    intervalIntegral.integral_add_adjacent_intervals hφ0q hφq1
  have h1 : (∫ s in 0..q, φ s) = ∫ s in 0..q, w s t := by
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    have hsubset : {x : ℝ | ¬(x ∈ Ι 0 q → φ x = w x t)} ⊆ {q} := by
      intro x hx
      have hx' : x ∈ Ι 0 q ∧ ¬(φ x = w x t) := by
        classical
        by_cases h1 : x ∈ Ι 0 q
        · have h2 : ¬(φ x = w x t) := by simpa [h1] using hx
          exact ⟨h1, h2⟩
        · exfalso
          apply hx
          intro h
          exact False.elim (h1 h)
      rw [Set.uIoc_of_le hq0] at hx'
      have hxq : x = q := by
        by_contra hne
        have hxlt : x < q := lt_of_le_of_ne hx'.1.2 hne
        have : φ x = w x t := by
          simp [φ, hxlt]
        exact hx'.2 this
      simp [hxq]
    refine MeasureTheory.measure_mono_null hsubset ?_
    simp
  have h2 : (∫ s in q..1, φ s) = 0 := by
    calc
      (∫ s in q..1, φ s) = ∫ s in q..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        refine ae_of_all _ (fun x hx => ?_)
        rw [Set.uIoc_of_le hq1] at hx
        simp [φ, not_lt_of_ge (le_of_lt hx.1)]
      _ = 0 := by simp
  calc
    (∫ s in 0..1, (if s < q then w s t else 0)) = ∫ s in 0..1, φ s := by
      simp [φ]
    _ = (∫ s in 0..q, φ s) + ∫ s in q..1, φ s := hsplit.symm
    _ = (∫ s in 0..q, w s t) + 0 := by rw [h1, h2]
    _ = G t q := by
      rw [ftc_inner t q hq0 hq1 ht]
      ring

/-- The set `{t : cos t = 1}` is countable (hence null). -/
private lemma countable_cos_eq_one : Set.Countable {t : ℝ | Real.cos t = 1} := by
  have h : {t : ℝ | Real.cos t = 1} = (fun n : ℤ => (n : ℝ) * (2 * Real.pi)) '' Set.univ := by
    ext t
    constructor
    · intro ht
      rcases (Real.cos_eq_one_iff t).mp ht with ⟨n, hn⟩
      refine ⟨n, trivial, ?_⟩
      exact hn
    · rintro ⟨n, -, hn⟩
      rw [← hn]
      exact (Real.cos_eq_one_iff (↑n * (2 * Real.pi))).mpr ⟨n, rfl⟩
  rw [h]
  exact Set.Countable.image Set.countable_univ _

/-- `cos t ≠ 1` for almost every `t`. -/
private lemma ae_cos_ne_one : ∀ᵐ t : ℝ ∂volume, Real.cos t ≠ 1 := by
  rw [MeasureTheory.ae_iff]
  have h : {t : ℝ | ¬Real.cos t ≠ 1} = {t : ℝ | Real.cos t = 1} := by
    ext t
    simp
  rw [h]
  exact countable_cos_eq_one.measure_zero volume

/-- Almost everywhere in `t` (restricted to the integration interval), the
identity `G(t,q t) = ∫_0^1 1_{s<q t} w(s,t) ds` holds. -/
private lemma ae_G_eq_cut (a b : ℝ) (hab : a ≤ b) (q : ℝ → ℝ)
    (hq0 : ∀ t : ℝ, a ≤ t → t ≤ b → 0 ≤ q t)
    (hq1 : ∀ t : ℝ, a ≤ t → t ≤ b → q t ≤ 1) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Ι a b →
      G t (q t) = ∫ s in 0..1, (if s < q t then w s t else 0) := by
  filter_upwards [ae_cos_ne_one] with t ht
  intro htI
  have htIoc : t ∈ Set.Ioc a b := by
    simpa [Set.uIoc_of_le hab] using htI
  exact (G_eq_int_cut t (q t) (hq0 t (le_of_lt htIoc.1) htIoc.2)
    (hq1 t (le_of_lt htIoc.1) htIoc.2) ht).symm

/-- If `c,d ∈ [0,1]` then `uIoc c d ⊆ uIoc 0 1`. -/
private lemma uIoc_sub_uIoc_unit {c d : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) : Set.uIoc c d ⊆ Set.uIoc (0 : ℝ) 1 := by
  intro x hx
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rcases (Set.mem_uIoc.mp hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_le_of_lt hc0 h1, le_trans h2 hd1⟩
  · exact ⟨lt_of_le_of_lt hd0 h1, le_trans h2 hc1⟩

/-- `w(·,t)` interval-integrable on any `[c,d] ⊆ [0,1]` (good `t`). -/
private lemma ii_w_sub (t c d : ℝ) (ht : Real.cos t ≠ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    IntervalIntegrable (fun s => w s t) volume c d :=
  (ii_w01 t ht).mono_set' (uIoc_sub_uIoc_unit hc0 hc1 hd0 hd1)

/-- `|w(·,t)|` interval-integrable on any `[c,d] ⊆ [0,1]` (good `t`). -/
private lemma ii_abs_sub (t c d : ℝ) (ht : Real.cos t ≠ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    IntervalIntegrable (fun s => |w s t|) volume c d :=
  ((ii_w01 t ht).abs).mono_set' (uIoc_sub_uIoc_unit hc0 hc1 hd0 hd1)

/-- `∫_u^v w(s,t) ds = G(t,v) − G(t,u)` for `0 ≤ u,v ≤ 1` and `cos t ≠ 1`. -/
private lemma ftc_sub (t u v : ℝ) (ht : Real.cos t ≠ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ s in u..v, w s t) = G t v - G t u := by
  have hfv := ftc_inner t v hv0 hv1 ht
  have hfu := ftc_inner t u hu0 hu1 ht
  have huv : IntervalIntegrable (fun s => w s t) volume 0 v :=
    ii_w_sub t 0 v ht (by norm_num) (by norm_num) hv0 hv1
  have huu : IntervalIntegrable (fun s => w s t) volume 0 u :=
    ii_w_sub t 0 u ht (by norm_num) (by norm_num) hu0 hu1
  have hs := intervalIntegral.integral_interval_sub_left (f := fun s => w s t)
    (a := 0) (b := v) (c := u) huv huu
  rw [← hs, hfv, hfu]

/-- `G(t,1) = (1/2)·log(2 − 2 cos t)`. -/
private lemma G_one (t : ℝ) : G t 1 = (1 / 2) * Real.log (2 - 2 * Real.cos t) := by
  unfold G
  have harg : 1 - 2 * 1 * Real.cos t + 1 ^ 2 = 2 - 2 * Real.cos t := by ring
  rw [harg]

/-- `G(t,cos t) = (1/2)·log(sin² t)`. -/
private lemma G_cos (t : ℝ) : G t (Real.cos t) = (1 / 2) * Real.log ((Real.sin t) ^ 2) := by
  unfold G
  have harg : 1 - 2 * Real.cos t * Real.cos t + (Real.cos t) ^ 2 = (Real.sin t) ^ 2 := by
    have h := Real.cos_sq_add_sin_sq t
    nlinarith
  rw [harg]

/-- For real `x`, `|x| = x` when `0 ≤ x`. -/
private lemma abs_eq_self_of_nonneg {x : ℝ} (h : 0 ≤ x) : |x| = x := abs_of_nonneg h

/-- `w(s,t) ≥ 0` when `cos t ≤ s ≤ 1` and `cos t ≠ 1`. -/
private lemma w_nonneg_of_ge_cos (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsc : Real.cos t ≤ s) (ht : Real.cos t ≠ 1) : 0 ≤ w s t := by
  unfold w
  have hnum : 0 ≤ s - Real.cos t := sub_nonneg.mpr hsc
  have hD : 0 < D s t := D_pos_of_cos_ne_one s t hs0 hs1 ht
  exact (div_nonneg_iff.mpr (Or.inl ⟨hnum, le_of_lt hD⟩))

/-- `w(s,t) ≤ 0` when `0 ≤ s ≤ cos t` and `cos t ≠ 1`. -/
private lemma w_nonpos_of_le_cos (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsc : s ≤ Real.cos t) (ht : Real.cos t ≠ 1) : w s t ≤ 0 := by
  unfold w
  have hnum : s - Real.cos t ≤ 0 := sub_nonpos.mpr hsc
  have hD : 0 < D s t := D_pos_of_cos_ne_one s t hs0 hs1 ht
  exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hD)

/-- `|G(t,1)| = (1/2)·|log(2−2cos t)|`. -/
private lemma abs_G_one (t : ℝ) : |G t 1| = (1 / 2) * |Real.log (2 - 2 * Real.cos t)| := by
  rw [G_one, abs_mul]
  have hh : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [hh]

/-- `2·|G(t,cos t)| = |log(sin² t)|`. -/
private lemma two_abs_G_cos (t : ℝ) : 2 * |G t (Real.cos t)| = |Real.log ((Real.sin t) ^ 2)| := by
  rw [G_cos]
  rw [abs_mul]
  have hh : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [hh]
  ring

/-- Pointwise bound: `∫_0^1 |w(s,t)| ds ≤ |log(sin²t)| + (1/2)|log(2−2cos t)|`. -/
private lemma abs_w_int_le (t : ℝ) (ht : Real.cos t ≠ 1) :
    (∫ s in 0..1, |w s t|) ≤
      |Real.log ((Real.sin t) ^ 2)| + (1 / 2) * |Real.log (2 - 2 * Real.cos t)| := by
  by_cases hc0 : Real.cos t ≤ 0
  · have hcong : (∫ s in 0..1, |w s t|) = ∫ s in 0..1, w s t := by
      apply intervalIntegral.integral_congr_ae
      refine ae_of_all _ (fun s hs => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hw : 0 ≤ w s t := by
        apply w_nonneg_of_ge_cos s t (le_of_lt hs.1) hs.2 ?_ ht
        exact le_trans hc0 (le_of_lt hs.1)
      exact abs_eq_self_of_nonneg hw
    calc
      (∫ s in 0..1, |w s t|) = ∫ s in 0..1, w s t := hcong
      _ = G t 1 - G t 0 := ftc_sub t 0 1 ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      _ = G t 1 := by simp [G_zero]
      _ = |G t 1| := by
        rw [G_one]
        have hge : (1 : ℝ) ≤ 2 - 2 * Real.cos t := by linarith
        have hnn : 0 ≤ Real.log (2 - 2 * Real.cos t) := Real.log_nonneg hge
        rw [abs_of_nonneg (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hnn)]
      _ ≤ |Real.log ((Real.sin t) ^ 2)| + (1 / 2) * |Real.log (2 - 2 * Real.cos t)| := by
        rw [abs_G_one]
        exact le_add_of_nonneg_left (abs_nonneg _)
  · have hcpos : 0 < Real.cos t := lt_of_not_ge hc0
    have hc1 : Real.cos t < 1 := lt_of_le_of_ne (Real.cos_le_one t) ht
    let c := Real.cos t
    have hc0b : 0 ≤ c := le_of_lt hcpos
    have hc1b : c ≤ 1 := le_of_lt hc1
    have hii0c : IntervalIntegrable (fun s => |w s t|) volume 0 c :=
      ii_abs_sub t 0 c ht (by norm_num) (by norm_num) hc0b hc1b
    have hiic1 : IntervalIntegrable (fun s => |w s t|) volume c 1 :=
      ii_abs_sub t c 1 ht hc0b hc1b (by norm_num) (by norm_num)
    have hsplit : (∫ s in 0..c, |w s t|) + (∫ s in c..1, |w s t|) =
        ∫ s in 0..1, |w s t| :=
      intervalIntegral.integral_add_adjacent_intervals hii0c hiic1
    have hcong0 : (∫ s in 0..c, |w s t|) = ∫ s in 0..c, (-(w s t)) := by
      apply intervalIntegral.integral_congr_ae
      refine ae_of_all _ (fun s hs => ?_)
      rw [Set.uIoc_of_le hc0b] at hs
      have hw : w s t ≤ 0 := by
        apply w_nonpos_of_le_cos s t (le_of_lt hs.1) (le_trans hs.2 hc1b) hs.2 ht
      exact abs_of_nonpos hw
    have hval0 : (∫ s in 0..c, |w s t|) = -G t c := by
      rw [hcong0]
      rw [intervalIntegral.integral_neg]
      rw [ftc_sub t 0 c ht (by norm_num) (by norm_num) hc0b hc1b]
      simp [G_zero]
    have hcong1 : (∫ s in c..1, |w s t|) = ∫ s in c..1, w s t := by
      apply intervalIntegral.integral_congr_ae
      refine ae_of_all _ (fun s hs => ?_)
      rw [Set.uIoc_of_le hc1b] at hs
      have hw : 0 ≤ w s t := by
        apply w_nonneg_of_ge_cos s t (le_of_lt (lt_of_le_of_lt hc0b hs.1)) hs.2 (le_of_lt hs.1) ht
      exact abs_eq_self_of_nonneg hw
    calc
      (∫ s in 0..1, |w s t|) = (∫ s in 0..c, |w s t|) + ∫ s in c..1, |w s t| := hsplit.symm
      _ = -G t c + (G t 1 - G t c) := by
        rw [hval0, hcong1]
        rw [ftc_sub t c 1 ht hc0b hc1b (by norm_num) (by norm_num)]
      _ = G t 1 - 2 * G t c := by ring
      _ ≤ |G t 1| + 2 * |G t c| := by
        have h1 : G t 1 ≤ |G t 1| := le_abs_self _
        have h2 : -2 * G t c ≤ 2 * |G t c| := by
          have hng : -G t c ≤ |G t c| := neg_le_abs (G t c)
          nlinarith
        nlinarith
      _ = |Real.log ((Real.sin t) ^ 2)| + (1 / 2) * |Real.log (2 - 2 * Real.cos t)| := by
        rw [abs_G_one, two_abs_G_cos]
        ring

/-- `2 − 2cos t = 4·sin²(t/2)`. -/
private lemma two_sub_two_cos (t : ℝ) : 2 - 2 * Real.cos t = 4 * (Real.sin (t / 2)) ^ 2 := by
  have hc := Real.cos_two_mul (t / 2)
  have hcarg : 2 * (t / 2) = t := by ring
  rw [hcarg] at hc
  have hs := Real.sin_sq (t / 2)
  nlinarith [hc, hs]

/-- `log(2−2cos t) = log 4 + 2·log(sin(t/2))` when `sin(t/2) ≠ 0`. -/
private lemma log_two_sub_two_cos (t : ℝ) (hz : Real.sin (t / 2) ≠ 0) :
    Real.log (2 - 2 * Real.cos t) = Real.log 4 + 2 * Real.log (Real.sin (t / 2)) := by
  rw [two_sub_two_cos]
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 hz)]
  rw [Real.log_pow]
  ring

/-- `(1/2)·|log(2−2cos t)| ≤ log 2 + |log(sin(t/2))|`. -/
private lemma log_two_sub_two_cos_abs_le (t : ℝ) :
    (1 / 2) * |Real.log (2 - 2 * Real.cos t)| ≤
      Real.log 2 + |Real.log (Real.sin (t / 2))| := by
  by_cases hz : Real.sin (t / 2) = 0
  · have h : 2 - 2 * Real.cos t = 0 := by
      rw [two_sub_two_cos, hz]
      ring
    rw [h]
    simp [hz]
    have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  · have hmain := log_two_sub_two_cos t hz
    calc
      (1 / 2) * |Real.log (2 - 2 * Real.cos t)|
          = (1 / 2) * |Real.log 4 + 2 * Real.log (Real.sin (t / 2))| := by rw [hmain]
      _ ≤ (1 / 2) * (|Real.log 4| + |2 * Real.log (Real.sin (t / 2))|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ = (1 / 2) * (|Real.log 4| + 2 * |Real.log (Real.sin (t / 2))|) := by
        congr 2
        rw [abs_mul]
        norm_num
      _ = Real.log 2 + |Real.log (Real.sin (t / 2))| := by
        have h4a : Real.log 4 = 2 * Real.log 2 := by
          have h := Real.log_pow (2 : ℝ) 2
          norm_num at h
          simpa using h
        have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        rw [h4a]
        have hnn : 0 ≤ 2 * Real.log 2 := by positivity
        rw [abs_of_nonneg hnn]
        ring

/-- `|log(sin²t)| ≤ 2·|log(sin t)|`. -/
private lemma abs_log_sin_sq_le (t : ℝ) :
    |Real.log ((Real.sin t) ^ 2)| ≤ 2 * |Real.log (Real.sin t)| := by
  rw [Real.log_pow, abs_mul]
  norm_num

/-- The (log-type) integrable bound for `t ↦ ∫_s |w(s,t)|`. -/
private noncomputable def Bnd (t : ℝ) : ℝ :=
  2 * |Real.log (Real.sin t)| + |Real.log (Real.sin (t / 2))| + Real.log 2

private lemma Bnd_nonneg (t : ℝ) : 0 ≤ Bnd t := by
  unfold Bnd
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

/-- `volume (Ioc a b) < ⊤` on `ℝ`. -/
private lemma measure_Ioc_ne_top (a b : ℝ) : volume (Set.Ioc a b) ≠ ⊤ := by
  have hcc : volume (Set.Icc a b) < ⊤ := (isCompact_Icc : IsCompact (Set.Icc a b)).measure_lt_top
  have hmono : volume (Set.Ioc a b) ≤ volume (Set.Icc a b) :=
    measure_mono Set.Ioc_subset_Icc_self
  exact ne_of_lt (lt_of_le_of_lt hmono hcc)

/-- `Bnd` is interval-integrable over any interval. -/
private lemma intervalIntegrable_Bnd (a b : ℝ) : IntervalIntegrable Bnd volume a b := by
  have h1 : IntervalIntegrable (fun t => Real.log (Real.sin t)) volume a b :=
    intervalIntegrable_log_sin
  have h2 : IntervalIntegrable (fun t => Real.log (Real.sin t)) volume (a / 2) (b / 2) :=
    intervalIntegrable_log_sin
  have hcomp : IntervalIntegrable (fun t => Real.log (Real.sin (t / 2))) volume a b := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      h2.comp_mul_left (c := (1 / 2 : ℝ))
  have h1a : IntervalIntegrable (fun t => 2 * |Real.log (Real.sin t)|) volume a b := by
    simpa using (h1.abs.const_mul (2 : ℝ))
  have h2a : IntervalIntegrable (fun t => |Real.log (Real.sin (t / 2))|) volume a b :=
    hcomp.abs
  have hc : IntervalIntegrable (fun _ : ℝ => Real.log 2) volume a b := by
    change IntegrableOn (fun _ : ℝ => Real.log 2) (Set.Ioc a b) volume ∧
           IntegrableOn (fun _ : ℝ => Real.log 2) (Set.Ioc b a) volume
    constructor
    · exact MeasureTheory.integrableOn_const (s := Set.Ioc a b) (μ := volume)
        (hs := measure_Ioc_ne_top a b)
    · exact MeasureTheory.integrableOn_const (s := Set.Ioc b a) (μ := volume)
        (hs := measure_Ioc_ne_top b a)
  unfold Bnd
  simpa [add_assoc, add_comm, add_left_comm] using h1a.add h2a |>.add hc

/-- `∫_0^1 |w(s,t)| ds ≤ Bnd t` for `cos t ≠ 1`. -/
private lemma abs_w_int_le_Bnd (t : ℝ) (ht : Real.cos t ≠ 1) :
    (∫ s in 0..1, |w s t|) ≤ Bnd t := by
  unfold Bnd
  calc
    (∫ s in 0..1, |w s t|) ≤
        |Real.log ((Real.sin t) ^ 2)| + (1 / 2) * |Real.log (2 - 2 * Real.cos t)| :=
      abs_w_int_le t ht
    _ ≤ 2 * |Real.log (Real.sin t)| + (Real.log 2 + |Real.log (Real.sin (t / 2))|) := by
      have h1 := abs_log_sin_sq_le t
      have h2 := log_two_sub_two_cos_abs_le t
      linarith
    _ = 2 * |Real.log (Real.sin t)| + |Real.log (Real.sin (t / 2))| + Real.log 2 := by ring

/-- `w` is jointly measurable in `(s,t)`. -/
private lemma measurable_w2 : Measurable (fun z : ℝ × ℝ => w z.1 z.2) := by
  unfold w
  apply Measurable.div
  · fun_prop
  · unfold D
    fun_prop

/-- Absolute-value version: `|w|` integrable on the full rectangle
`(a,b] × (0,1]`, for `a ≤ b`. -/
private lemma w_abs_integrable_rect (a b : ℝ) (_hab : a ≤ b) :
    Integrable (fun z : ℝ × ℝ => |w z.2 z.1|)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1))) := by
  let f : ℝ × ℝ → ℝ := fun z => |w z.2 z.1|
  have hmf : Measurable f := by
    exact (measurable_w2.comp measurable_swap).abs
  have hfae : AEStronglyMeasurable f
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1))) := hmf.aestronglyMeasurable
  have h1 : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      Integrable (fun s : ℝ => |w s t|) (volume.restrict (Set.Ioc 0 1)) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae ae_cos_ne_one] with t ht
    change IntegrableOn (fun s : ℝ => |w s t|) (Set.Ioc 0 1) volume
    exact (ii_abs_sub t 0 1 ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      (∫ s in Set.Ioc 0 1, |w s t|) ≤ Bnd t := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae ae_cos_ne_one] with t ht
    calc
      (∫ s in Set.Ioc 0 1, |w s t|) = ∫ s in 0..1, |w s t| := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      _ ≤ Bnd t := abs_w_int_le_Bnd t ht
  have hBI : Integrable (fun t : ℝ => Bnd t) (volume.restrict (Set.Ioc a b)) := by
    exact (intervalIntegrable_Bnd a b).1
  have hIm : AEStronglyMeasurable
      (fun t : ℝ => ∫ s : ℝ, |w s t| ∂(volume.restrict (Set.Ioc 0 1)))
      (volume.restrict (Set.Ioc a b)) := by
    simpa [f] using hfae.integral_prod_right'
  have hI : Integrable (fun t : ℝ => ∫ s : ℝ, |w s t| ∂(volume.restrict (Set.Ioc 0 1)))
      (volume.restrict (Set.Ioc a b)) := by
    apply Integrable.mono (g := fun t : ℝ => Bnd t)
    · exact hBI
    · exact hIm
    · filter_upwards [hbd] with t htle
      have hpos : 0 ≤ (∫ s : ℝ in Set.Ioc 0 1, |w s t|) :=
        integral_nonneg (fun _ => abs_nonneg _)
      have hn1 : ‖(∫ s : ℝ in Set.Ioc 0 1, |w s t|)‖ =
          (∫ s : ℝ in Set.Ioc 0 1, |w s t|) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      have hn2 : ‖Bnd t‖ = Bnd t := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Bnd_nonneg t)]
      rw [hn1, hn2]
      exact htle
  refine (MeasureTheory.integrable_prod_iff hfae).2 ⟨?_, ?_⟩
  · simpa [f] using h1
  · simpa [f, Real.norm_eq_abs] using hI

/-- A continuous (on `[a,b]`) function extends to a continuous function on all of `ℝ`
by clamping its argument. -/
private lemma continuous_clamp_q (a b : ℝ) (hab : a ≤ b) (q : ℝ → ℝ)
    (hqc : ContinuousOn q (Set.Icc a b)) :
    Continuous (fun t : ℝ => q (min (max t a) b)) := by
  have hminmax : Continuous (fun t : ℝ => min (max t a) b) := by
    fun_prop
  apply ContinuousOn.comp_continuous hqc hminmax
  intro t
  constructor
  · apply le_min
    · exact le_trans (le_max_left a t) (le_of_eq (max_comm a t))
    · exact hab
  · exact min_le_right _ _

/-- `w` is jointly measurable in swapped order `(t,s) ↦ w(s,t)`. -/
private lemma measurable_w2_swap : Measurable (fun z : ℝ × ℝ => w z.2 z.1) := by
  exact (measurable_w2.comp measurable_swap)

/-- The truncated integrand `F` is integrable on the rectangle, `a ≤ b`. -/
private lemma F_integrable_rect (a b : ℝ) (hab : a ≤ b) (q : ℝ → ℝ)
    (hqc : ContinuousOn q (Set.Icc a b)) :
    Integrable (fun z : ℝ × ℝ => F q z.1 z.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1))) := by
  let qe : ℝ → ℝ := fun t => q (min (max t a) b)
  have hqe_c : Continuous qe := by
    have h := continuous_clamp_q a b hab q hqc
    simpa [qe] using h
  let G : ℝ × ℝ → ℝ := fun z => if z.2 < qe z.1 then w z.2 z.1 else 0
  have hqe_m : Measurable (fun z : ℝ × ℝ => qe z.1) :=
    (hqe_c.measurable.comp measurable_fst)
  have hrel : Measurable (fun z : ℝ × ℝ => z.2 - qe z.1) := measurable_snd.sub hqe_m
  have hset : MeasurableSet {z : ℝ × ℝ | z.2 < qe z.1} := by
    have hpre : MeasurableSet {z : ℝ × ℝ | z.2 - qe z.1 < 0} := by
      exact (measurableSet_Iio.preimage hrel)
    convert hpre using 1
    ext z
    exact (sub_lt_zero.symm : z.2 < qe z.1 ↔ z.2 - qe z.1 < 0)
  have hGmeas : Measurable G := by
    unfold G
    exact Measurable.ite hset measurable_w2_swap measurable_const
  have hnull : ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1)))
      (((Set.Ioc a b)ᶜ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have hmu : (volume.restrict (Set.Ioc a b)) ((Set.Ioc a b)ᶜ) = 0 := by simp
    simp [hmu]
  have hGF : G =ᵐ[(volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1))]
      (fun z : ℝ × ℝ => F q z.1 z.2) := by
    change ∀ᵐ (z : ℝ × ℝ) ∂((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1))),
      G z = F q z.1 z.2
    rw [MeasureTheory.ae_iff]
    have hsubset : {z : ℝ × ℝ | G z ≠ F q z.1 z.2}
        ⊆ (Set.Ioc a b)ᶜ ×ˢ (Set.univ : Set ℝ) := by
      intro z hz
      by_contra h
      have htnot : ¬ z.1 ∈ (Set.Ioc a b)ᶜ := by
        intro hc
        apply h
        exact ⟨hc, trivial⟩
      have ht : z.1 ∈ Set.Ioc a b := by simpa using htnot
      have hclamp : min (max z.1 a) b = z.1 := by
        have hmax : max z.1 a = z.1 := max_eq_left (le_of_lt ht.1)
        rw [hmax, min_eq_left ht.2]
      have hqeq : qe z.1 = q z.1 := by
        simp [qe, hclamp]
      have heq : G z = F q z.1 z.2 := by
        unfold G F
        rw [hqeq]
      exact hz heq
    exact MeasureTheory.measure_mono_null hsubset hnull
  have hAes : AEStronglyMeasurable (fun z : ℝ × ℝ => F q z.1 z.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1))) := by
    exact hGmeas.aestronglyMeasurable.congr hGF
  apply Integrable.mono (g := fun z : ℝ × ℝ => |w z.2 z.1|)
  · exact w_abs_integrable_rect a b hab
  · exact hAes
  · refine ae_of_all _ (fun z => ?_)
    unfold F
    by_cases hz : z.2 < q z.1
    · simp [hz]
    · simp [hz]

/-- Fubini: interval integrals over `t ∈ [a,b]` and `s ∈ [0,1]` can be
swapped for an integrable (on the rectangle) `F`. -/
private lemma swap_rect (a b : ℝ) (hab : a ≤ b) (Ff : ℝ → ℝ → ℝ)
    (hFf : Integrable (fun z : ℝ × ℝ => Ff z.1 z.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 1)))) :
    (∫ t in a..b, ∫ s in 0..1, Ff t s) = ∫ s in 0..1, ∫ t in a..b, Ff t s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  have hinner_s : (fun s : ℝ => ∫ t in Set.Ioc a b, Ff t s)
      = fun s => ∫ t in a..b, Ff t s := by
    funext s
    rw [intervalIntegral.integral_of_le hab]
  have hinner_t : (fun t : ℝ => ∫ s in 0..1, Ff t s)
      = fun t => ∫ s in Set.Ioc 0 1, Ff t s := by
    funext t
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hswap := MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) (f := Ff) hFf
  calc
    (∫ t in a..b, ∫ s in 0..1, Ff t s)
        = ∫ t in Set.Ioc a b, ∫ s in 0..1, Ff t s := by
          rw [intervalIntegral.integral_of_le hab]
    _ = ∫ t in Set.Ioc a b, ∫ s in Set.Ioc 0 1, Ff t s := by
          rw [hinner_t]
    _ = (∫ t, ∫ s, Ff t s ∂ν ∂μ) := by
          simp [μ, ν]
    _ = ∫ s, ∫ t, Ff t s ∂μ ∂ν := hswap
    _ = ∫ s in Set.Ioc 0 1, ∫ t in Set.Ioc a b, Ff t s := by
          simp [μ, ν]
    _ = ∫ s in 0..1, ∫ t in a..b, Ff t s := by
          rw [hinner_s]
          rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
/-- The theorem in the case `a ≤ b`. -/
private theorem layer_cake_le (a b : ℝ) (hab : a ≤ b) (q : ℝ → ℝ)
    (hqc : ContinuousOn q (Set.Icc (min a b) (max a b)))
    (hq0 : ∀ t : ℝ, a ≤ t → t ≤ b → 0 ≤ q t)
    (hq1 : ∀ t : ℝ, a ≤ t → t ≤ b → q t ≤ 1) :
    (∫ t in a..b, (1 / 2 : ℝ) * Real.log (1 - 2 * q t * Real.cos t + (q t) ^ 2)) =
      (∫ s in 0..1,
        ∫ t in a..b,
          if s < q t then (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2) else 0) := by
  have hqc' : ContinuousOn q (Set.Icc a b) := by
    simpa [min_eq_left hab, max_eq_right hab] using hqc
  calc
    (∫ t in a..b, (1 / 2 : ℝ) * Real.log (1 - 2 * q t * Real.cos t + (q t) ^ 2))
        = ∫ t in a..b, G t (q t) := by
          congr 1
    _ = ∫ t in a..b, (∫ s in 0..1, (if s < q t then w s t else 0)) := by
          apply intervalIntegral.integral_congr_ae
          exact ae_G_eq_cut a b hab q hq0 hq1
    _ = (∫ s in 0..1, ∫ t in a..b, (if s < q t then w s t else 0)) := by
          apply swap_rect a b hab
          exact F_integrable_rect a b hab q hqc'
    _ = ∫ s in 0..1, ∫ t in a..b,
          if s < q t then (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2) else 0 := by
          congr 1

/-- **Layer-cake identity for the D2 integrand.**  For `a ≤ b` and a
continuous `q : [a,b] → [0,1]`:
`∫_a^b G(t,q(t))dt = ∫_0^1 (∫_a^b 1_{q(t)>s}·w_s(t) dt) ds`. -/
theorem layer_cake (a b : ℝ) (hab : a ≤ b) (q : ℝ → ℝ)
    (hqc : ContinuousOn q (Set.Icc (min a b) (max a b)))
    (hq0 : ∀ t : ℝ, a ≤ t → t ≤ b → 0 ≤ q t)
    (hq1 : ∀ t : ℝ, a ≤ t → t ≤ b → q t ≤ 1) :
    (∫ t in a..b, (1 / 2 : ℝ) * Real.log (1 - 2 * q t * Real.cos t + (q t) ^ 2)) =
      (∫ s in 0..1,
        ∫ t in a..b,
          if s < q t then (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2) else 0) := by
  exact layer_cake_le a b hab q hqc hq0 hq1


/-- **Public: the `s`-slice of the layer cake is integrable over `[0,1]`.**
For continuous `q` on `[a,b]` (`a ≤ b`), the function
`s ↦ ∫_a^b (if s < q t then w_s(t) else 0) dt` is interval-integrable over
`s ∈ [0,1]` (used by the D2 assembly to compare the layer-cake `s`-integral
against the per-level window integrals via `intervalIntegral.integral_mono_on`). -/
theorem s_side_intervalIntegrable (a b : ℝ) (hab : a ≤ b) (q : ℝ → ℝ)
    (hqc : ContinuousOn q (Set.Icc a b)) :
    IntervalIntegrable
      (fun s : ℝ => ∫ t in a..b,
        if s < q t then (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2) else 0)
      volume 0 1 := by
  classical
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  have hF : Integrable (fun z : ℝ × ℝ => F q z.1 z.2) (μ.prod ν) := by
    simpa [μ, ν] using F_integrable_rect a b hab q hqc
  have hslice : Integrable (fun s : ℝ => ∫ t : ℝ, F q t s ∂μ) ν := by
    exact MeasureTheory.Integrable.integral_prod_right (f := fun z : ℝ × ℝ => F q z.1 z.2) hF
  let g : ℝ → ℝ := fun s => ∫ t in a..b, F q t s
  have hgs : (fun s : ℝ => ∫ t : ℝ, F q t s ∂μ) = g := by
    funext s
    dsimp [g]
    rw [intervalIntegral.integral_of_le hab]
  have hgν : Integrable g ν := by
    simpa [hgs] using hslice
  have hg_inline : g = fun s : ℝ => ∫ t in a..b,
        if s < q t then (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2) else 0 := by
    funext s
    dsimp [g, F, w, D]
  -- IntervalIntegrable g volume 0 1
  rw [← hg_inline]
  rw [IntervalIntegrable]
  constructor
  · -- IntegrableOn g (Ioc 0 1) volume
    have hg01 : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      simpa [ν] using hgν
    simpa [MeasureTheory.IntegrableOn] using hg01
  · -- IntegrableOn g (Ioc 1 0) volume: the interval is empty
    have hIoc : Set.Ioc (1 : ℝ) 0 = ∅ := by
      ext x
      constructor
      · rintro ⟨h1, h0⟩
        linarith
      · intro hx
        exact False.elim (by simpa using hx)
    simpa [MeasureTheory.IntegrableOn, hIoc] using
      (MeasureTheory.integrable_zero_measure (f := g) (μ := (0 : Measure ℝ)))

end Submission.Core

end
