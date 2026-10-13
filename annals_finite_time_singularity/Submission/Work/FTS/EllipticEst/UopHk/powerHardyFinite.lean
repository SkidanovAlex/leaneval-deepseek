/-
Copyright: work module for the Elgindi finite-time singularity project.

# The power Hardy inequality on `(0,a)`

The main statement `Work.FTS.EllipticEst.UopHk.powerHardyFinite`: for `0 ≤ η < 1`, `0 < a`
and `h` of class `C¹` on `(0,a)` with `h → 0` at `0⁺` whose `t^{-η}`-weighted squared
derivative is integrable on `(0,a)`, the function `t ↦ h t ^ 2 * t ^ (-(2+η))` is integrable
on `(0,a)` and

  `∫_0^a h² t^{-(2+η)} ≤ 4/(1+η)² ∫_0^a (h')² t^{-η}`.

This is the sharp power-weight Hardy inequality with `β = 1 + η`; the constant `4/(1+η)²` is
optimal (approached by `h(t) = t^λ`, `λ ↓ (1+η)/2`).

The proof is the classical one, carried out here without any a priori integrability of the
left-hand side:

* `hardySliceFin` — the slice estimate `(β/2) ∫_{(ε,b]} g² x^{-(β+1)}
  ≤ (2/β) ∫_{(ε,b]} (g')² x^{1-β} + (g ε)² ε^{-β}` on a subinterval `(ε,b]` of `(0,a)`
  (integration by parts against `x^{-β}` plus the pointwise weighted Young inequality),
  with every integrability requirement derived from the continuity hypotheses;
* `hardyCSBound` — the weighted Cauchy–Schwarz bound
  `(h t)² ≤ t^{1+η} ∫_{(0,t]} (h')² x^{-η}` at the lower endpoint, obtained from the
  fundamental theorem of calculus on `[c,t]` and monotone convergence as `c → 0⁺`;
* the two estimates are applied on the increasing family of intervals
  `(a/2^{n+2}, a - a/2^{n+2}]` (whose union is `(0,a)`) and the resulting uniform bound on the
  monotone sequence of integrals is transferred to the `lintegral` by
  `MeasureTheory.lintegral_iSup'`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst.UopHk

/-! ## The slice estimate -/

/-- **One slice of the sharp weighted Hardy inequality, with no integrability hypotheses.**
For `0 < β`, `0 < ε < b` and `g` of class `C¹` on `(ε,b)` with `g` and `g'` continuous up to
both endpoints,
  `(β/2) ∫_{(ε,b]} g² x^{-(β+1)} ≤ (2/β) ∫_{(ε,b]} (g')² x^{1-β} + (g ε)² ε^{-β}`.

This is the integration by parts `d/dx (g² x^{-β}) = 2 g g' x^{-β} - β g² x^{-(β+1)}` on
`(ε,b]` combined with the pointwise weighted Young inequality
`2 g g' x^{-β} ≤ (β/2) g² x^{-(β+1)} + (2/β) (g')² x^{1-β}`, dropping the (non-positive)
right boundary term `-(g b)² b^{-β}`. -/
theorem hardySliceFin {β ε b : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hεb : ε < b) {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc ε b))
    (hgd : ∀ x ∈ Set.Ioo ε b, HasDerivAt g (deriv g x) x)
    (hgdc : ContinuousOn (deriv g) (Set.Icc ε b)) :
    (β / 2) * (∫ x in Set.Ioc ε b, (g x) ^ 2 * x ^ (-(β + 1)))
      ≤ (2 / β) * (∫ x in Set.Ioc ε b, (deriv g x) ^ 2 * x ^ (1 - β))
        + (g ε) ^ 2 * ε ^ (-β) := by
  have hεle : ε ≤ b := le_of_lt hεb
  have hb0 : 0 < b := lt_trans hε hεb
  have hrp : ∀ p : ℝ, ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc ε b) := by
    intro p x hx
    exact (Real.continuousAt_rpow_const x p
      (Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1)))).continuousWithinAt
  have hcontL : ContinuousOn (fun x : ℝ => (g x) ^ 2 * x ^ (-(β + 1))) (Set.Icc ε b) :=
    (hgcont.pow 2).mul (hrp (-(β + 1)))
  have hcontP : ContinuousOn (fun x : ℝ => 2 * g x * deriv g x * x ^ (-β)) (Set.Icc ε b) :=
    (((continuousOn_const (c := (2 : ℝ))).mul hgcont).mul hgdc).mul (hrp (-β))
  have hcontf : ContinuousOn
      (fun x : ℝ => 2 * g x * deriv g x * x ^ (-β) - β * ((g x) ^ 2 * x ^ (-(β + 1))))
      (Set.Icc ε b) := hcontP.sub (hcontL.const_mul β)
  have hcontF : ContinuousOn (fun x : ℝ => (g x) ^ 2 * x ^ (-β)) (Set.Icc ε b) :=
    (hgcont.pow 2).mul (hrp (-β))
  have hintf : IntervalIntegrable
      (fun x : ℝ => 2 * g x * deriv g x * x ^ (-β) - β * ((g x) ^ 2 * x ^ (-(β + 1))))
      volume ε b := hcontf.intervalIntegrable_of_Icc hεle
  have hintP : IntervalIntegrable (fun x : ℝ => 2 * g x * deriv g x * x ^ (-β)) volume ε b :=
    hcontP.intervalIntegrable_of_Icc hεle
  have hintL : IntervalIntegrable (fun x : ℝ => (g x) ^ 2 * x ^ (-(β + 1))) volume ε b :=
    hcontL.intervalIntegrable_of_Icc hεle
  have hintR : IntervalIntegrable (fun x : ℝ => (deriv g x) ^ 2 * x ^ (1 - β)) volume ε b :=
    (((hgdc.pow 2)).mul (hrp (1 - β))).intervalIntegrable_of_Icc hεle
  have hderiv : ∀ x ∈ Set.Ioo ε b, HasDerivAt (fun y : ℝ => (g y) ^ 2 * y ^ (-β))
      (2 * g x * deriv g x * x ^ (-β) - β * ((g x) ^ 2 * x ^ (-(β + 1)))) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hε hx.1.le
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hg2 : HasDerivAt (fun y : ℝ => (g y) ^ 2) (2 * g x * deriv g x) x := by
      have h := (hgd x hx).mul (hgd x hx)
      have h' : HasDerivAt (fun y : ℝ => g y * g y) (2 * g x * deriv g x) x := by
        convert h using 1
        ring
      rwa [show (fun y : ℝ => g y * g y) = fun y : ℝ => (g y) ^ 2 from by
        funext y; ring] at h'
    have hp : HasDerivAt (fun y : ℝ => y ^ (-β)) (-β * x ^ (-(β + 1))) x := by
      have h := Real.hasDerivAt_rpow_const (p := -β) (Or.inl hxne)
      simpa only [show (-β - 1 : ℝ) = -(β + 1) by ring] using h
    have hmul := hg2.mul hp
    convert hmul using 1
    ring
  have hFTC : ∫ x in ε..b,
      (2 * g x * deriv g x * x ^ (-β) - β * ((g x) ^ 2 * x ^ (-(β + 1))))
      = (g b) ^ 2 * b ^ (-β) - (g ε) ^ 2 * ε ^ (-β) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεle hcontF hderiv hintf
  have hsplit : ∫ x in ε..b,
      (2 * g x * deriv g x * x ^ (-β) - β * ((g x) ^ 2 * x ^ (-(β + 1))))
      = (∫ x in ε..b, 2 * g x * deriv g x * x ^ (-β))
        - β * (∫ x in ε..b, (g x) ^ 2 * x ^ (-(β + 1))) := by
    rw [intervalIntegral.integral_sub hintP (hintL.const_mul β),
      intervalIntegral.integral_const_mul]
  have hAM : ∀ x ∈ Set.Icc ε b, 2 * g x * deriv g x * x ^ (-β) ≤
      (β / 2) * ((g x) ^ 2 * x ^ (-(β + 1))) + (2 / β) * ((deriv g x) ^ 2 * x ^ (1 - β)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
    have hx1 : x ^ (-(β + 1)) = x ^ (-β) / x := by
      rw [show -(β + 1) = -β - 1 by ring, Real.rpow_sub hx0, Real.rpow_one]
    have hx2 : x ^ (1 - β) = x ^ (-β) * x := by
      rw [show 1 - β = -β + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [hx1, hx2]
    have ht : 0 < x ^ (-β) := Real.rpow_pos_of_pos hx0 _
    have hAM' : 2 * g x * deriv g x * x ≤
        (β / 2) * (g x) ^ 2 + (2 / β) * ((deriv g x) * x) ^ 2 := by
      have hsq : 0 ≤ (β / 2) * (g x - (2 / β) * ((deriv g x) * x)) ^ 2 := by positivity
      have hid : (β / 2) * (g x - (2 / β) * ((deriv g x) * x)) ^ 2
          = (β / 2) * (g x) ^ 2 + (2 / β) * ((deriv g x) * x) ^ 2
            - 2 * g x * deriv g x * x := by
        field_simp
        ring
      linarith [hsq, hid]
    have hmult := mul_le_mul_of_nonneg_right hAM' (le_of_lt (div_pos ht hx0))
    calc 2 * g x * deriv g x * x ^ (-β) = (2 * g x * deriv g x * x) * (x ^ (-β) / x) := by
          field_simp
      _ ≤ ((β / 2) * (g x) ^ 2 + (2 / β) * ((deriv g x) * x) ^ 2) * (x ^ (-β) / x) := hmult
      _ = (β / 2) * ((g x) ^ 2 * (x ^ (-β) / x))
            + (2 / β) * ((deriv g x) ^ 2 * (x ^ (-β) * x)) := by field_simp
  have hmono : ∫ x in ε..b, 2 * g x * deriv g x * x ^ (-β) ≤
      ∫ x in ε..b,
        ((β / 2) * ((g x) ^ 2 * x ^ (-(β + 1)))
          + (2 / β) * ((deriv g x) ^ 2 * x ^ (1 - β))) :=
    intervalIntegral.integral_mono_on hεle hintP
      ((hintL.const_mul (β / 2)).add (hintR.const_mul (2 / β))) hAM
  have hlin : ∫ x in ε..b,
        ((β / 2) * ((g x) ^ 2 * x ^ (-(β + 1)))
          + (2 / β) * ((deriv g x) ^ 2 * x ^ (1 - β)))
      = (β / 2) * (∫ x in ε..b, (g x) ^ 2 * x ^ (-(β + 1)))
        + (2 / β) * (∫ x in ε..b, (deriv g x) ^ 2 * x ^ (1 - β)) := by
    rw [intervalIntegral.integral_add (hintL.const_mul (β / 2)) (hintR.const_mul (2 / β)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_of_le hεle] at hFTC hsplit hmono hlin
  have hFb : 0 ≤ (g b) ^ 2 * b ^ (-β) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hb0 _))
  have h1 : (∫ x in Set.Ioc ε b, 2 * g x * deriv g x * x ^ (-β)) ≤
      (β / 2) * (∫ x in Set.Ioc ε b, (g x) ^ 2 * x ^ (-(β + 1)))
        + (2 / β) * (∫ x in Set.Ioc ε b, (deriv g x) ^ 2 * x ^ (1 - β)) := by
    linarith [hmono, hlin]
  have h2 : (∫ x in Set.Ioc ε b, 2 * g x * deriv g x * x ^ (-β)) =
      β * (∫ x in Set.Ioc ε b, (g x) ^ 2 * x ^ (-(β + 1)))
        + ((g b) ^ 2 * b ^ (-β) - (g ε) ^ 2 * ε ^ (-β)) := by
    linarith [hFTC, hsplit]
  have hβ2 : β * (∫ x in Set.Ioc ε b, (g x) ^ 2 * x ^ (-(β + 1))) =
      2 * ((β / 2) * (∫ x in Set.Ioc ε b, (g x) ^ 2 * x ^ (-(β + 1)))) := by ring
  nlinarith [h1, h2, hFb, hβ2]

/-! ## The weighted Cauchy–Schwarz bound at the lower endpoint -/

/-- **The weighted Cauchy–Schwarz bound at `0`.** For `0 ≤ η`, `0 < t < a` and `h` of class
`C¹` on `(0,a)` with `h → 0` at `0⁺` whose `x^{-η}`-weighted squared derivative is integrable
on `(0,a]`,
  `(h t)² ≤ t^{1+η} ∫_{(0,t]} (h')² x^{-η}`.

Proof: FTC on `[c,t]` for `0 < c < t` writes `h t - h c = ∫_{(c,t]} h'`, and Cauchy–Schwarz
splits `h' = 1 · h'`, giving `(h t - h c)² ≤ (t - c) ∫_{(c,t]} (h')²`; then
`(h')² = x^η · x^{-η}(h')² ≤ t^η x^{-η}(h')²` on `(c,t]`.  Letting `c → 0⁺` along
`c_n = t/2^{n+1}`, with `h c_n → 0` and `MeasureTheory.tendsto_setIntegral_of_monotone`,
finishes the proof. -/
theorem hardyCSBound {a η t : ℝ} (hη : 0 ≤ η) (ht : 0 < t) (hta : t < a) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 h (Set.Ioo 0 a))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η)) (Set.Ioc 0 a)) :
    (h t) ^ 2 ≤ t ^ (1 + η) * ∫ x in Set.Ioc 0 t, (deriv h x) ^ 2 * x ^ (-η) := by
  have hDt : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η)) (Set.Ioc 0 t) :=
    hB.mono_set (fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hta)⟩)
  have hcont_d : ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) a) :=
    hsm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have key : ∀ c ∈ Set.Ioo (0 : ℝ) t,
      (h t - h c) ^ 2 ≤ t ^ (1 + η) * ∫ x in Set.Ioc 0 t, (deriv h x) ^ 2 * x ^ (-η) := by
    intro c hc
    have hc0 : 0 < c := hc.1
    have hct : c ≤ t := le_of_lt hc.2
    have hsub : Set.Icc c t ⊆ Set.Ioo (0 : ℝ) a := fun x hx =>
      ⟨lt_of_lt_of_le hc0 hx.1, lt_of_le_of_lt hx.2 hta⟩
    have hcont : ContinuousOn h (Set.Icc c t) := hsm.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo c t, HasDerivAt h (deriv h x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) a := hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      exact ((hsm.differentiableOn one_ne_zero x hx').differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hdcont : ContinuousOn (deriv h) (Set.Icc c t) := hcont_d.mono hsub
    have hint : IntervalIntegrable (deriv h) volume c t := hdcont.intervalIntegrable_of_Icc hct
    have hFTC : ∫ x in c..t, deriv h x = h t - h c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hct hcont hderiv hint
    have hFTC' : ∫ x in Set.Ioc c t, deriv h x = h t - h c := by
      rw [← intervalIntegral.integral_of_le hct]
      exact hFTC
    have hcont_d2 : ContinuousOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Icc c t) := hdcont.pow 2
    have hint_d2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc c t) :=
      (hcont_d2.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hcont_sq : ContinuousOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc c t) :=
      hcont_d2.mono Set.Ioc_subset_Icc_self
    have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc c t)) := memLp_const 1
    have hmem2 : MemLp (deriv h) 2 (volume.restrict (Set.Ioc c t)) :=
      (memLp_two_iff_integrable_sq (f := deriv h)
        ((hdcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
          measurableSet_Ioc)).mpr hint_d2
    have hCS := Work.Spaces.cs_integral (u := fun _ : ℝ => (1 : ℝ)) (v := deriv h) hmem1 hmem2
    have hIL : (∫ x in Set.Ioc c t, (1 : ℝ) * deriv h x) = ∫ x in Set.Ioc c t, deriv h x := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      ring
    have h1sq : (∫ x in Set.Ioc c t, (1 : ℝ) ^ 2) = t - c := by
      have h' : (∫ x in Set.Ioc c t, (1 : ℝ) ^ 2) = ∫ x in Set.Ioc c t, (1 : ℝ) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => by norm_num)
      rw [h', setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hct)]
    have hsq : (∫ x in Set.Ioc c t, deriv h x) ^ 2
        ≤ (t - c) * (∫ x in Set.Ioc c t, (deriv h x) ^ 2) := by
      rw [← hIL, ← h1sq]
      exact hCS
    have hbd : (∫ x in Set.Ioc c t, (deriv h x) ^ 2)
        ≤ t ^ η * (∫ x in Set.Ioc c t, (deriv h x) ^ 2 * x ^ (-η)) := by
      have hpt : ∀ x ∈ Set.Ioc c t, (deriv h x) ^ 2
          ≤ t ^ η * ((deriv h x) ^ 2 * x ^ (-η)) := by
        intro x hx
        have hx0 : 0 < x := lt_trans hc0 hx.1
        have h1 : x ^ η * x ^ (-η) = 1 := by
          rw [← Real.rpow_add hx0, show η + (-η) = 0 by ring, Real.rpow_zero]
        have h2 : x ^ η ≤ t ^ η := Real.rpow_le_rpow hx0.le hx.2 hη
        calc (deriv h x) ^ 2 = x ^ η * x ^ (-η) * (deriv h x) ^ 2 := by rw [h1, one_mul]
          _ = x ^ η * ((deriv h x) ^ 2 * x ^ (-η)) := by ring
          _ ≤ t ^ η * ((deriv h x) ^ 2 * x ^ (-η)) :=
              mul_le_mul_of_nonneg_right h2
                (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0.le _))
      have hInt2 : MeasureTheory.IntegrableOn
          (fun x : ℝ => t ^ η * ((deriv h x) ^ 2 * x ^ (-η))) (Set.Ioc c t) :=
        (hDt.mono_set (fun x hx => ⟨lt_trans hc0 hx.1, hx.2⟩)).const_mul (t ^ η)
      calc (∫ x in Set.Ioc c t, (deriv h x) ^ 2)
          ≤ ∫ x in Set.Ioc c t, t ^ η * ((deriv h x) ^ 2 * x ^ (-η)) :=
            setIntegral_mono_on hint_d2 hInt2 measurableSet_Ioc hpt
        _ = t ^ η * (∫ x in Set.Ioc c t, (deriv h x) ^ 2 * x ^ (-η)) := by
            rw [integral_const_mul]
    have hincl : (∫ x in Set.Ioc c t, (deriv h x) ^ 2 * x ^ (-η))
        ≤ ∫ x in Set.Ioc 0 t, (deriv h x) ^ 2 * x ^ (-η) := by
      refine setIntegral_mono_set hDt ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun x hx =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
      · exact Filter.Eventually.of_forall (fun x hx => ⟨lt_trans hc0 hx.1, hx.2⟩)
    calc (h t - h c) ^ 2 = (∫ x in Set.Ioc c t, deriv h x) ^ 2 := by rw [hFTC']
      _ ≤ (t - c) * (∫ x in Set.Ioc c t, (deriv h x) ^ 2) := hsq
      _ ≤ t * (t ^ η * ∫ x in Set.Ioc 0 t, (deriv h x) ^ 2 * x ^ (-η)) := by
          have h2 : (∫ x in Set.Ioc c t, (deriv h x) ^ 2)
              ≤ t ^ η * ∫ x in Set.Ioc 0 t, (deriv h x) ^ 2 * x ^ (-η) :=
            le_trans hbd (mul_le_mul_of_nonneg_left hincl (Real.rpow_nonneg ht.le η))
          refine mul_le_mul (by linarith) h2 ?_ (le_of_lt ht)
          exact setIntegral_nonneg measurableSet_Ioc (fun x hx => sq_nonneg _)
      _ = t ^ (1 + η) * ∫ x in Set.Ioc 0 t, (deriv h x) ^ 2 * x ^ (-η) := by
          have hpow : t * t ^ η = t ^ (1 + η) := by
            nth_rewrite 1 [← Real.rpow_one t]
            rw [← Real.rpow_add ht]
          rw [← mul_assoc, hpow]
  have hlim : Filter.Tendsto (fun n : ℕ => (h t - h (t / 2 ^ (n + 1))) ^ 2) Filter.atTop
      (nhds ((h t) ^ 2)) := by
    have hc_lim : Filter.Tendsto (fun n : ℕ => t / 2 ^ (n + 1)) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Filter.Tendsto (fun n : ℕ => t / 2 ^ (n + 1)) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop
            ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
              (tendsto_add_atTop_nat 1))
        exact h
      · exact Filter.Eventually.of_forall (fun n => div_pos ht (by positivity))
    have h1 : Filter.Tendsto (fun n : ℕ => h (t / 2 ^ (n + 1))) Filter.atTop (nhds 0) :=
      h0.comp hc_lim
    have h2 : Filter.Tendsto (fun n : ℕ => (h t - h (t / 2 ^ (n + 1))) ^ 2) Filter.atTop
        (nhds ((h t - 0) ^ 2)) := by
      have hsub : Filter.Tendsto (fun n : ℕ => h t - h (t / 2 ^ (n + 1))) Filter.atTop
          (nhds (h t - 0)) := tendsto_const_nhds.sub h1
      exact hsub.pow 2
    simpa using h2
  refine le_of_tendsto_of_tendsto' hlim tendsto_const_nhds (fun n => key _ ⟨?_, ?_⟩)
  · exact div_pos ht (by positivity)
  · exact div_lt_self ht (one_lt_pow₀ (by norm_num) (by omega))

theorem powerHardyFinite {η a : ℝ} (hη : 0 ≤ η) (hη1 : η < 1) (ha : 0 < a) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 h (Set.Ioo 0 a))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn (fun t : ℝ => (deriv h t) ^ 2 * t ^ (-η)) (Set.Ioo 0 a)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => h t ^ 2 * t ^ (-(2 + η))) (Set.Ioo 0 a) ∧
      (∫ t in Set.Ioo 0 a, h t ^ 2 * t ^ (-(2 + η)))
        ≤ 4 / (1 + η) ^ 2 * ∫ t in Set.Ioo 0 a, (deriv h t) ^ 2 * t ^ (-η) := by
  -- the exponent bound `η < 1` is not needed by the argument (only `0 ≤ η` is); it is
  -- part of the requested statement, so we keep a name for it
  have _hη1 : η < 1 := hη1
  have hβpos : (0 : ℝ) < 1 + η := by linarith
  have hB_Ioc : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η))
      (Set.Ioc 0 a) := hB.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hDcont : ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) a) :=
    hsm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hFcont : ContinuousOn (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η))) (Set.Ioo (0 : ℝ) a) :=
    (hsm.continuousOn.pow 2).mul (fun x hx =>
      (Real.continuousAt_rpow_const x (-(2 + η)) (Or.inl (ne_of_gt hx.1))).continuousWithinAt)
  have hHcont : ContinuousOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η)) (Set.Ioo (0 : ℝ) a) :=
    (hDcont.pow 2).mul (fun x hx =>
      (Real.continuousAt_rpow_const x (-η) (Or.inl (ne_of_gt hx.1))).continuousWithinAt)
  -- the endpoints and inclusions for the family of intervals
  have hεpos : ∀ n : ℕ, (0 : ℝ) < a / 2 ^ (n + 2) := fun n => div_pos ha (by positivity)
  have hεb : ∀ n : ℕ, a / 2 ^ (n + 2) < a - a / 2 ^ (n + 2) := by
    intro n
    have h3 : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have h4 : (2 : ℝ) < 2 ^ (n + 2) := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 ≤ n + 2)
      have h5 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [h5] at h
      linarith
    have h5 : a / 2 ^ (n + 2) * 2 ^ (n + 2) = a := by field_simp
    have h6 : (a - a / 2 ^ (n + 2)) * 2 ^ (n + 2) = a * 2 ^ (n + 2) - a := by
      rw [sub_mul, h5]
    rw [div_lt_iff₀ h3, h6]
    nlinarith [mul_lt_mul_of_pos_left h4 ha]
  have hb_lt : ∀ n : ℕ, a - a / 2 ^ (n + 2) < a := by
    intro n
    have := hεpos n
    linarith
  have hpow_le : ∀ n : ℕ, a / 2 ^ ((n + 1) + 2) ≤ a / 2 ^ (n + 2) := fun n =>
    div_le_div_of_nonneg_left ha.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hpow_le' : ∀ n : ℕ, a / 2 ^ (n + 2) ≤ a / 2 ^ (0 + 2) := fun n =>
    div_le_div_of_nonneg_left ha.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hsub_s : ∀ n : ℕ, Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
      ⊆ Set.Ioo (0 : ℝ) a := fun n x hx =>
    ⟨lt_trans (hεpos n) hx.1, lt_of_le_of_lt hx.2 (hb_lt n)⟩
  have hsub_Icc : ∀ n : ℕ, Set.Icc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
      ⊆ Set.Ioo (0 : ℝ) a := fun n x hx =>
    ⟨lt_of_lt_of_le (hεpos n) hx.1, lt_of_le_of_lt hx.2 (hb_lt n)⟩
  have hF_int : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η)))
      (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))) := fun n =>
    ((hFcont.mono (hsub_Icc n)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hsubIoc0 : Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)) ⊆ Set.Ioc 0 a := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (by rw [zero_add]; exact div_le_self ha.le (by norm_num))⟩
  -- the good point in each interval
  have hex : ∀ x ∈ Set.Ioo (0 : ℝ) a, ∃ n : ℕ,
      x ∈ Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)) := by
    intro x hx
    have hlim1 : Filter.Tendsto (fun n : ℕ => a / 2 ^ (n + 2)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
          (tendsto_add_atTop_nat 2))
    have hlim2 : Filter.Tendsto (fun n : ℕ => a - a / 2 ^ (n + 2)) Filter.atTop (nhds a) := by
      have h := hlim1.const_sub a
      simpa using h
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, a / 2 ^ (n + 2) < x :=
      hlim1.eventually (eventually_lt_nhds hx.1)
    have h2 : ∀ᶠ n : ℕ in Filter.atTop, x < a - a / 2 ^ (n + 2) :=
      hlim2.eventually (eventually_gt_nhds hx.2)
    exact ((h1.and h2).mono (fun n hn => ⟨hn.1, le_of_lt hn.2⟩)).exists
  -- ## Step 1: the slice estimates
  have key : ∀ n : ℕ,
      (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η)))
        ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
          + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
              (deriv h x) ^ 2 * x ^ (-η)) := by
    intro n
    have hε := hεpos n
    have hsl : (1 + η) / 2 * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
          h x ^ 2 * x ^ (-(2 + η)))
        ≤ 2 / (1 + η) * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
            (deriv h x) ^ 2 * x ^ (-η))
          + (h (a / 2 ^ (n + 2))) ^ 2 * (a / 2 ^ (n + 2)) ^ (-(1 + η)) := by
      have hsl' := hardySliceFin (β := 1 + η) hβpos hε (hεb n) (g := h)
        (hsm.continuousOn.mono (hsub_Icc n))
        (fun x hx => ((hsm.differentiableOn one_ne_zero x
          (hsub_Icc n ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).differentiableAt
            (isOpen_Ioo.mem_nhds
              (hsub_Icc n ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).hasDerivAt)
        (hDcont.mono (hsub_Icc n))
      simpa only [show -((1 + η) + 1) = -(2 + η) by ring,
        show (1 - (1 + η)) = -η by ring] using hsl'
    have hcsf : (h (a / 2 ^ (n + 2))) ^ 2 * (a / 2 ^ (n + 2)) ^ (-(1 + η))
        ≤ ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η) := by
      have hlt : a / 2 ^ (n + 2) < a :=
        div_lt_self ha (one_lt_pow₀ (by norm_num) (by omega))
      have hcs := hardyCSBound (a := a) (η := η) (t := a / 2 ^ (n + 2))
        hη hε hlt hsm h0 hB_Ioc
      have hprod : (a / 2 ^ (n + 2)) ^ (1 + η) * (a / 2 ^ (n + 2)) ^ (-(1 + η)) = 1 := by
        rw [← Real.rpow_add hε, show (1 + η) + (-(1 + η)) = 0 by ring, Real.rpow_zero]
      have h2 := mul_le_mul_of_nonneg_right hcs (Real.rpow_pos_of_pos hε (-(1 + η))).le
      calc (h (a / 2 ^ (n + 2))) ^ 2 * (a / 2 ^ (n + 2)) ^ (-(1 + η))
          ≤ (((a / 2 ^ (n + 2)) ^ (1 + η)
              * ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)))
            * (a / 2 ^ (n + 2)) ^ (-(1 + η)) := h2
        _ = ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η) := by
            rw [show (((a / 2 ^ (n + 2)) ^ (1 + η)
                * ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)))
                * (a / 2 ^ (n + 2)) ^ (-(1 + η))
                = (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η))
                  * ((a / 2 ^ (n + 2)) ^ (1 + η)
                    * (a / 2 ^ (n + 2)) ^ (-(1 + η))) from by ring,
              hprod, mul_one]
    have hBnd : (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
          (deriv h x) ^ 2 * x ^ (-η))
        ≤ ∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η) := by
      refine setIntegral_mono_set hB ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall (fun x hx =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
      · exact Filter.Eventually.of_forall (fun x hx => hsub_s n hx)
    have hstep : (1 + η) / 2 * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
          h x ^ 2 * x ^ (-(2 + η)))
        ≤ 2 / (1 + η) * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
          + (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)) := by
      have h1 : (2 / (1 + η)) * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
            (deriv h x) ^ 2 * x ^ (-η))
          ≤ (2 / (1 + η)) * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η)) :=
        mul_le_mul_of_nonneg_left hBnd (by positivity)
      linarith [hsl, h1, hcsf]
    have hne : (1 + η) ≠ 0 := ne_of_gt hβpos
    have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 2 / (1 + η))
    have e1 : (2 / (1 + η)) * ((1 + η) / 2 * (∫ x in Set.Ioc (a / 2 ^ (n + 2))
          (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))))
        = (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))) := by
      rw [← mul_assoc, mul_comm (2 / (1 + η)) ((1 + η) / 2)]
      field_simp
    have e2 : (2 / (1 + η)) * ((2 / (1 + η)) * (∫ x in Set.Ioo (0 : ℝ) a,
            (deriv h x) ^ 2 * x ^ (-η))
          + (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)))
        = 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
          + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
              (deriv h x) ^ 2 * x ^ (-η)) := by
      field_simp
      ring
    linarith [hmul, e1, e2]
  -- ## Step 2: monotonicity and boundedness of the sequence of slice integrals
  have hA_mono : Monotone (fun n : ℕ => ∫ x in Set.Ioc (a / 2 ^ (n + 2))
      (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    refine setIntegral_mono_set (hF_int (n + 1)) ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall (fun x hx =>
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans (hεpos (n + 1)) hx.1).le _)))
    · refine Filter.Eventually.of_forall (fun x hx => ⟨?_, ?_⟩)
      · have h4 := hpow_le n
        linarith [hx.1]
      · have h4 := hpow_le n
        linarith [hx.2]
  have hA_bdd : BddAbove (Set.range (fun n : ℕ => ∫ x in Set.Ioc (a / 2 ^ (n + 2))
      (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η)))) := by
    refine ⟨4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
      + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)),
          (deriv h x) ^ 2 * x ^ (-η)), ?_⟩
    rintro y ⟨n, rfl⟩
    have h1 := key n
    have h2 : (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η))
        ≤ (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)), (deriv h x) ^ 2 * x ^ (-η)) := by
      refine setIntegral_mono_set (hB_Ioc.mono_set hsubIoc0) ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun x hx =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
      · refine Filter.Eventually.of_forall (fun x hx => ⟨hx.1, ?_⟩)
        exact le_trans hx.2 (hpow_le' n)
    have h3 : 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
          (deriv h x) ^ 2 * x ^ (-η))
        ≤ 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)),
            (deriv h x) ^ 2 * x ^ (-η)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h3]
  -- ## Step 3: the tails vanish
  have hD_tend : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
      (deriv h x) ^ 2 * x ^ (-η)) Filter.atTop (nhds 0) := by
    have hanti : Antitone (fun n : ℕ => Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2))) := by
      refine antitone_nat_of_succ_le (fun n => ?_)
      exact Set.Ioc_subset_Ioc le_rfl (hpow_le n)
    have h0int : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η))
        (Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2))) := hB_Ioc.mono_set hsubIoc0
    have h := hanti.tendsto_setIntegral (fun n => measurableSet_Ioc) h0int
    have hinter : (⋂ n : ℕ, Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2))) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx0 : 0 < x := (Set.mem_iInter.mp hx 0).1
      have hxle : ∀ n : ℕ, x ≤ a / 2 ^ (n + 2) := fun n => (Set.mem_iInter.mp hx n).2
      have hlim : Filter.Tendsto (fun n : ℕ => a / 2 ^ (n + 2)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
            (tendsto_add_atTop_nat 2))
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hx0)).exists
      exact absurd (lt_of_le_of_lt (hxle n) hn) (lt_irrefl x)
    rw [hinter] at h
    simpa using h
  have hD_lim : Filter.Tendsto
      (fun n : ℕ => 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
        + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
            (deriv h x) ^ 2 * x ^ (-η)))
      Filter.atTop
      (nhds (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
        (deriv h x) ^ 2 * x ^ (-η)))) := by
    have h := (hD_tend.const_mul (2 / (1 + η))).const_add
      (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η)))
    simpa using h
  have hsup : (⨆ n : ℕ, (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
      h x ^ 2 * x ^ (-(2 + η))))
      ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η)) :=
    le_of_tendsto_of_tendsto' (tendsto_atTop_ciSup hA_mono hA_bdd) hD_lim key
  -- ## Step 4: monotone convergence to the full interval
  have hMCT : ∫⁻ x in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (h x ^ 2 * x ^ (-(2 + η)))
      ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
          (deriv h x) ^ 2 * x ^ (-η))) := by
    have hsup2 : (⨆ n : ℕ, ENNReal.ofReal (∫ x in Set.Ioc (a / 2 ^ (n + 2))
        (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))))
        ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
            (deriv h x) ^ 2 * x ^ (-η))) :=
      le_trans (iSup_le (fun n => ENNReal.ofReal_le_ofReal (le_ciSup hA_bdd n)))
        (ENNReal.ofReal_le_ofReal hsup)
    have hpoint : ∀ x : ℝ,
        (⨆ n : ℕ, (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
          (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x)
        = (Set.Ioo (0 : ℝ) a).indicator
          (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x := by
      intro x
      by_cases hx : x ∈ Set.Ioo (0 : ℝ) a
      · obtain ⟨N, hN⟩ := hex x hx
        refine le_antisymm (iSup_le (fun n => ?_)) ?_
        · by_cases hxn : x ∈ Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
          · rw [Set.indicator_of_mem hxn, Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hxn]
            exact zero_le
        · rw [Set.indicator_of_mem hx]
          calc (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x
              = (Set.Ioc (a / 2 ^ (N + 2)) (a - a / 2 ^ (N + 2))).indicator
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x :=
                (Set.indicator_of_mem hN
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η))))).symm
            _ ≤ ⨆ n : ℕ, (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x :=
                le_iSup (fun n : ℕ => (Set.Ioc (a / 2 ^ (n + 2))
                  (a - a / 2 ^ (n + 2))).indicator
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x) N
      · have hzero : ∀ n : ℕ, (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
            (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x = 0 := fun n =>
          Set.indicator_of_notMem (fun hcon => hx (hsub_s n hcon))
            (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η))))
        rw [Set.indicator_of_notMem hx]
        simp only [hzero]
        simp
    have hmeas_u : ∀ n : ℕ, AEMeasurable ((Set.Ioc (a / 2 ^ (n + 2))
        (a - a / 2 ^ (n + 2))).indicator
        (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η))))) volume := by
      intro n
      rw [aemeasurable_indicator_iff measurableSet_Ioc]
      exact (((hFcont.mono (hsub_s n)).aemeasurable measurableSet_Ioc)).ennreal_ofReal
    have hmono_u : ∀ᵐ x ∂(volume : Measure ℝ), Monotone (fun n : ℕ =>
        (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
          (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x) :=
      Filter.Eventually.of_forall (fun x => by
        refine monotone_nat_of_le_succ (fun n => ?_)
        by_cases hxn : x ∈ Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
        · have hxn' : x ∈ Set.Ioc (a / 2 ^ ((n + 1) + 2)) (a - a / 2 ^ ((n + 1) + 2)) :=
            ⟨lt_of_le_of_lt (hpow_le n) hxn.1, le_trans hxn.2 (by linarith [hpow_le n])⟩
          rw [Set.indicator_of_mem hxn, Set.indicator_of_mem hxn']
        · rw [Set.indicator_of_notMem hxn]
          exact zero_le)
    calc ∫⁻ x in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (h x ^ 2 * x ^ (-(2 + η)))
        = ⨆ n : ℕ, ENNReal.ofReal (∫ x in Set.Ioc (a / 2 ^ (n + 2))
            (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))) := by
          rw [← lintegral_indicator measurableSet_Ioo
              (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))),
            ← lintegral_congr hpoint, lintegral_iSup' hmeas_u hmono_u]
          refine iSup_congr (fun n => ?_)
          rw [lintegral_indicator measurableSet_Ioc]
          exact (ofReal_integral_eq_lintegral_ofReal (hF_int n)
            ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun x hx =>
              mul_nonneg (sq_nonneg _)
                (Real.rpow_nonneg (le_trans (hεpos n).le hx.1.le) _))))).symm
      _ ≤ _ := hsup2
  -- ## Step 5: integrability and the real inequality
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) a)]
      (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η))) :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall (fun x hx =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
  have hmeas : AEStronglyMeasurable (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) a)) := hFcont.aestronglyMeasurable measurableSet_Ioo
  have hfin : MeasureTheory.HasFiniteIntegral (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) a)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn_ae]
    exact lt_of_le_of_lt hMCT ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  have hCnn : (0 : ℝ) ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
      (deriv h x) ^ 2 * x ^ (-η)) := by
    have hBnn : 0 ≤ ∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η) :=
      setIntegral_nonneg measurableSet_Ioo (fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _))
    positivity
  have h2 : ENNReal.ofReal (∫ x in Set.Ioo (0 : ℝ) a, h x ^ 2 * x ^ (-(2 + η)))
      ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
          (deriv h x) ^ 2 * x ^ (-η))) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal ⟨hmeas, hfin⟩ hnn_ae]
    exact hMCT
  exact (ENNReal.ofReal_le_ofReal_iff hCnn).mp h2

end Work.FTS.EllipticEst.UopHk
