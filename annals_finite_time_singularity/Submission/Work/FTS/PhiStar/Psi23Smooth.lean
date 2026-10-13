import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

/-!
# Smoothness of the two telescoping iterates `ψ₂`, `ψ₃`

`ψ₂ = sin 2θ · LinvI ψ` and `ψ₃ = sin 2θ · LinvI ψ₂`, where

`Linv h θ = −(sin²θ cos³θ)⁻¹ · ∫₀^θ sin²t cos³t h t / sin 2t dt`,  `LinvI h θ = ∫₀^θ Linv h`.

The point of this file is that `LinvI h` is `C²` on `(0, b)` as soon as `h` is continuous and
bounded on `(0, b)`: the integrand of `LinvI` is `−(sin²θcos³θ)⁻¹ ∫₀^θ (sin t cos²t /2) h t dt`,
a quotient of a `C¹` primitive by a smooth non-vanishing weight.  No moment condition and no
endpoint behaviour of `h` is used: everything is local on a sub-interval `(0, b)`,
`b < π/2`, so the iterate can be fed back into itself.
-/

/-- The integrand of the zero-moment inverse, in its singular (quotient) form. -/
private def lsrc (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t

/-- The primitive of the source, i.e. the numerator of `Linv`. -/
private def lprim (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, lsrc h t

private lemma linv_eq_lprim (h : ℝ → ℝ) (θ : ℝ) :
    Linv h θ = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * lprim h θ) := rfl

private lemma lprim_eq (h : ℝ → ℝ) (x : ℝ) :
    lprim h x = ∫ t in (0 : ℝ)..x, lsrc h t := rfl

/-- On `(0, π/2)` the quotient defining `lsrc` is the regular expression `sin t cos²t h t / 2`. -/
private lemma lsrc_eq {h : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    lsrc h t = Real.sin t * Real.cos t ^ 2 / 2 * h t := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, Real.pi_pos]))
  have hc : Real.cos t ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  unfold lsrc
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  field_simp

/-- Pointwise bound on the source, from a bound on `h`. -/
private lemma lsrc_abs_le {h : ℝ → ℝ} {M b t : ℝ} (hbπ : b < Real.pi / 2)
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) (ht : t ∈ Set.Ioo 0 b) :
    |lsrc h t| ≤ M / 2 * Real.sin t := by
  have htπ : t < Real.pi / 2 := lt_trans ht.2 hbπ
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [Real.pi_pos])
  have hkey : |lsrc h t| = Real.sin t * Real.cos t ^ 2 / 2 * |h t| := by
    rw [lsrc_eq ⟨ht.1, htπ⟩, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sin t * Real.cos t ^ 2 / 2)]
  rw [hkey]
  have hc2 : Real.cos t ^ 2 ≤ 1 := by nlinarith [Real.cos_le_one t, Real.neg_one_le_cos t]
  have hM' : |h t| ≤ M := hM t ht
  calc Real.sin t * Real.cos t ^ 2 / 2 * |h t| ≤ Real.sin t * 1 / 2 * M := by gcongr
    _ = M / 2 * Real.sin t := by ring

/-- Continuity of the source on `(0, b)`, `b < π/2`. -/
private lemma lsrc_contOn {h : ℝ → ℝ} {b : ℝ} (hbπ : b < Real.pi / 2)
    (hcont : ContinuousOn h (Set.Ioo 0 b)) :
    ContinuousOn (lsrc h) (Set.Ioo 0 b) := by
  have hnum : ContinuousOn (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 * h t)
      (Set.Ioo 0 b) :=
    (((Real.continuous_sin.pow 2).continuousOn).mul
      ((Real.continuous_cos.pow 3).continuousOn)).mul hcont
  have hden : ContinuousOn (fun t : ℝ => Work.Construction.s2 t) (Set.Ioo 0 b) := by
    have hfun : (fun t : ℝ => Work.Construction.s2 t) = fun t => Real.sin (2 * t) := by
      funext t; exact Work.Construction.s2_eq t
    rw [hfun]
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  unfold lsrc
  refine hnum.div hden fun t ht => ?_
  rw [Work.Construction.s2_eq]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
    (by nlinarith [ht.2, hbπ, Real.pi_pos]))

/-- The source is interval-integrable on `[0, x]` for `x ∈ (0, b)`. -/
private lemma lsrc_intervalIntegrable {h : ℝ → ℝ} {M b x : ℝ} (hb : 0 < b)
    (hbπ : b < Real.pi / 2) (hcont : ContinuousOn h (Set.Ioo 0 b))
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) (hx : x ∈ Set.Ioo 0 b) :
    IntervalIntegrable (lsrc h) volume 0 x := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM (b / 2) ⟨by linarith, by linarith⟩)
  have hsub : Set.Ioc (0 : ℝ) x ⊆ Set.Ioo 0 b := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩
  have hfin : volume (Set.Ioc (0 : ℝ) x) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable (lsrc h) (volume.restrict (Set.Ioc (0 : ℝ) x)) :=
    MeasureTheory.AEStronglyMeasurable.mono_set hsub
      ((lsrc_contOn hbπ hcont).aestronglyMeasurable measurableSet_Ioo)
  rw [intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hx.1)]
  refine MeasureTheory.IntegrableOn.of_bound hfin haesm (M / 2) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs]
  calc |lsrc h t| ≤ M / 2 * Real.sin t := lsrc_abs_le hbπ hM (hsub ht)
    _ ≤ M / 2 := by nlinarith [Real.sin_le_one t, hMnn]

/-- `lprim h` is differentiable at every point of `(0, b)` with derivative `lsrc h`. -/
private lemma hasDerivAt_lprim {h : ℝ → ℝ} {M b x : ℝ} (hb : 0 < b)
    (hbπ : b < Real.pi / 2) (hcont : ContinuousOn h (Set.Ioo 0 b))
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) (hx : x ∈ Set.Ioo 0 b) :
    HasDerivAt (lprim h) (lsrc h x) x := by
  have hI := lsrc_intervalIntegrable hb hbπ hcont hM hx
  have hsm : StronglyMeasurableAtFilter (lsrc h) (𝓝 x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (lsrc_contOn hbπ hcont) x hx
  have hct : ContinuousAt (lsrc h) x :=
    (lsrc_contOn hbπ hcont).continuousAt (isOpen_Ioo.mem_nhds hx)
  change HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, lsrc h t) (lsrc h x) x
  exact intervalIntegral.integral_hasDerivAt_right hI hsm hct

/-- `lprim h` is `C¹` on `(0, b)`. -/
private lemma contDiffOn_one_lprim {h : ℝ → ℝ} {M b : ℝ} (hb : 0 < b)
    (hbπ : b < Real.pi / 2) (hcont : ContinuousOn h (Set.Ioo 0 b))
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) :
    ContDiffOn ℝ 1 (lprim h) (Set.Ioo 0 b) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  refine ⟨fun x hx =>
      (hasDerivAt_lprim hb hbπ hcont hM hx).differentiableAt.differentiableWithinAt, ?_⟩
  refine (lsrc_contOn hbπ hcont).congr fun x hx => ?_
  rw [derivWithin_of_isOpen isOpen_Ioo hx]
  exact (hasDerivAt_lprim hb hbπ hcont hM hx).deriv

/-- Bound on the primitive of the source: `|∫₀^x lsrc| ≤ (M/2)(1 − cos x)`. -/
private lemma abs_lprim_le {h : ℝ → ℝ} {M b x : ℝ} (hb : 0 < b) (hbπ : b < Real.pi / 2)
    (hcont : ContinuousOn h (Set.Ioo 0 b)) (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M)
    (hx : x ∈ Set.Ioo 0 b) : |lprim h x| ≤ M / 2 * (1 - Real.cos x) := by
  have hx0 : 0 < x := hx.1
  have hIntx : IntervalIntegrable (lsrc h) volume 0 x :=
    lsrc_intervalIntegrable hb hbπ hcont hM hx
  have hstep1 : |lprim h x| ≤ ∫ t in (0 : ℝ)..x, ‖lsrc h t‖ := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (a := (0 : ℝ)) (b := x) (f := lsrc h) (le_of_lt hx0)
    simpa only [Real.norm_eq_abs, lprim] using h
  have hstep2 : ∫ t in (0 : ℝ)..x, ‖lsrc h t‖ ≤ ∫ t in (0 : ℝ)..x, M / 2 * Real.sin t := by
    refine intervalIntegral.integral_mono_on (le_of_lt hx0) hIntx.norm
      ((continuous_const.mul Real.continuous_sin).intervalIntegrable 0 x) ?_
    intro t ht
    rw [Real.norm_eq_abs]
    rcases eq_or_lt_of_le ht.1 with h0 | ht0
    · rw [← h0]; simp [lsrc]
    · exact lsrc_abs_le hbπ hM ⟨ht0, lt_of_le_of_lt ht.2 hx.2⟩
  calc |lprim h x| ≤ ∫ t in (0 : ℝ)..x, ‖lsrc h t‖ := hstep1
    _ ≤ ∫ t in (0 : ℝ)..x, M / 2 * Real.sin t := hstep2
    _ = M / 2 * (1 - Real.cos x) := by
        rw [intervalIntegral.integral_const_mul, integral_sin, Real.cos_zero]

/-- Bound on `Linv h` on `(0, b)`: `|Linv h x| ≤ M / (2 cos³b)`. -/
private lemma abs_linv_le {h : ℝ → ℝ} {M b x : ℝ} (hb : 0 < b) (hbπ : b < Real.pi / 2)
    (hcont : ContinuousOn h (Set.Ioo 0 b)) (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M)
    (hx : x ∈ Set.Ioo 0 b) : |Linv h x| ≤ M / (2 * Real.cos b ^ 3) := by
  have hxπ : x < Real.pi / 2 := lt_trans hx.2 hbπ
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hxπ⟩
  have hcosb : 0 < Real.cos b :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hb], hbπ⟩
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM (b / 2) ⟨by linarith, by linarith⟩)
  have hmu : 0 < Real.sin x ^ 2 * Real.cos x ^ 3 := by positivity
  have h1 : |Linv h x| = (Real.sin x ^ 2 * Real.cos x ^ 3)⁻¹ * |lprim h x| := by
    rw [linv_eq_lprim h x, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hmu)]
  rw [h1]
  refine (mul_le_mul_of_nonneg_left (abs_lprim_le hb hbπ hcont hM hx) (by positivity)).trans ?_
  have hkey : (Real.sin x ^ 2 * Real.cos x ^ 3)⁻¹ * (M / 2 * (1 - Real.cos x))
      = M / 2 * ((1 - Real.cos x) / Real.sin x ^ 2) * (1 / Real.cos x ^ 3) := by
    field_simp
  rw [hkey]
  have hA : (1 - Real.cos x) / Real.sin x ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos hsin 2), Real.sin_sq]
    nlinarith [Real.cos_le_one x, hcos]
  have hB : 1 / Real.cos x ^ 3 ≤ 1 / Real.cos b ^ 3 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hcx : Real.cos b ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hx.1) (by linarith [hbπ, Real.pi_pos])
        (le_of_lt hx.2)
    exact pow_le_pow_left₀ (le_of_lt hcosb) hcx 3
  calc M / 2 * ((1 - Real.cos x) / Real.sin x ^ 2) * (1 / Real.cos x ^ 3)
      ≤ M / 2 * 1 * (1 / Real.cos b ^ 3) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hA (by linarith)) hB (by positivity)
          (by linarith)
    _ = M / (2 * Real.cos b ^ 3) := by
        rw [mul_one, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

/-- `Linv h` is `C¹` on `(0, b)`. -/
private lemma contDiffOn_one_linv {h : ℝ → ℝ} {M b : ℝ} (hb : 0 < b)
    (hbπ : b < Real.pi / 2) (hcont : ContinuousOn h (Set.Ioo 0 b))
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) :
    ContDiffOn ℝ 1 (Linv h) (Set.Ioo 0 b) := by
  have hmu : ContDiffOn ℝ 1 (fun θ : ℝ => (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹)
      (Set.Ioo 0 b) := by
    have h1 : ContDiff ℝ 1 (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3) := by fun_prop
    refine h1.contDiffOn.inv fun x hx => ?_
    have hxπ : x < Real.pi / 2 := lt_trans hx.2 hbπ
    have hs : Real.sin x ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos]))
    have hc : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hxπ⟩)
    exact mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 3 hc)
  have h2 := contDiffOn_one_lprim hb hbπ hcont hM
  have h3 : ContDiffOn ℝ 1
      (fun θ : ℝ => -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * lprim h θ)) (Set.Ioo 0 b) :=
    (hmu.mul h2).neg
  exact h3.congr fun x _ => (linv_eq_lprim h x).symm

/-- `LinvI h` has derivative `Linv h` at every point of `(0, b)`. -/
private lemma hasDerivAt_LinvI_local {h : ℝ → ℝ} {M b x : ℝ} (hb : 0 < b)
    (hbπ : b < Real.pi / 2) (hcont : ContinuousOn h (Set.Ioo 0 b))
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) (hx : x ∈ Set.Ioo 0 b) :
    HasDerivAt (LinvI h) (Linv h x) x := by
  have hlinvcontOn : ContinuousOn (Linv h) (Set.Ioo 0 b) :=
    (contDiffOn_one_linv hb hbπ hcont hM).continuousOn
  have hsub : Set.Ioc (0 : ℝ) x ⊆ Set.Ioo 0 b := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩
  have hfin : volume (Set.Ioc (0 : ℝ) x) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hInt : IntervalIntegrable (Linv h) volume 0 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hx.1)]
    refine MeasureTheory.IntegrableOn.of_bound hfin
      (MeasureTheory.AEStronglyMeasurable.mono_set hsub
        (hlinvcontOn.aestronglyMeasurable measurableSet_Ioo))
      (M / (2 * Real.cos b ^ 3)) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact abs_linv_le hb hbπ hcont hM (hsub ht)
  have hsm : StronglyMeasurableAtFilter (Linv h) (𝓝 x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hlinvcontOn x hx
  have hct : ContinuousAt (Linv h) x := hlinvcontOn.continuousAt (isOpen_Ioo.mem_nhds hx)
  change HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, Linv h t) (Linv h x) x
  exact intervalIntegral.integral_hasDerivAt_right hInt hsm hct

/-- **The main local result**: `LinvI h` is `C²` on `(0, b)` for any `h` continuous and bounded
on `(0, b)`, `0 < b < π/2`. -/
private lemma contDiffOn_two_LinvI {h : ℝ → ℝ} {M b : ℝ} (hb : 0 < b)
    (hbπ : b < Real.pi / 2) (hcont : ContinuousOn h (Set.Ioo 0 b))
    (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M) :
    ContDiffOn ℝ 2 (LinvI h) (Set.Ioo 0 b) := by
  rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 from rfl]
  refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (1 : ℕ∞ω))
    (f := LinvI h) (s := Set.Ioo 0 b) isOpen_Ioo).2 ⟨?_, ?_, ?_⟩
  · exact fun x hx =>
      (hasDerivAt_LinvI_local hb hbπ hcont hM hx).differentiableAt.differentiableWithinAt
  · intro hh
    exact absurd hh (by simp)
  · refine (contDiffOn_one_linv hb hbπ hcont hM).congr fun x hx => ?_
    exact deriv_eqOn isOpen_Ioo
      (fun y hy => (hasDerivAt_LinvI_local hb hbπ hcont hM hy).hasDerivWithinAt) hx

/-- The `sin 2θ` factor is smooth. -/
private lemma contDiffOn_two_s2 {b : ℝ} :
    ContDiffOn ℝ 2 (fun θ : ℝ => Work.Construction.s2 θ) (Set.Ioo 0 b) := by
  have h : ContDiff ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  exact h.contDiffOn.congr fun x _ => (Work.Construction.s2_eq x).symm

/-- Local bound on `LinvI h` on `(0, b)`. -/
private lemma abs_LinvI_le {h : ℝ → ℝ} {M b x : ℝ} (hb : 0 < b) (hbπ : b < Real.pi / 2)
    (hcont : ContinuousOn h (Set.Ioo 0 b)) (hM : ∀ t ∈ Set.Ioo 0 b, |h t| ≤ M)
    (hx : x ∈ Set.Ioo 0 b) : |LinvI h x| ≤ b * M / (2 * Real.cos b ^ 3) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM (b / 2) ⟨by linarith, by linarith⟩)
  have hcosb : 0 < Real.cos b :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hb], hbπ⟩
  have hsub : Set.Ioc (0 : ℝ) x ⊆ Set.Ioo 0 b := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩
  have hcontLinv : ContinuousOn (Linv h) (Set.Ioo 0 b) :=
    (contDiffOn_one_linv hb hbπ hcont hM).continuousOn
  have hfin : volume (Set.Ioc (0 : ℝ) x) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hInt : IntervalIntegrable (Linv h) volume 0 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hx.1)]
    refine MeasureTheory.IntegrableOn.of_bound hfin
      (MeasureTheory.AEStronglyMeasurable.mono_set hsub
        (hcontLinv.aestronglyMeasurable measurableSet_Ioo))
      (M / (2 * Real.cos b ^ 3)) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact abs_linv_le hb hbπ hcont hM (hsub ht)
  have h1 : |LinvI h x| ≤ ∫ t in (0 : ℝ)..x, ‖Linv h t‖ := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (a := (0 : ℝ)) (b := x) (f := Linv h) (le_of_lt hx.1)
    simpa only [Real.norm_eq_abs, LinvI] using h
  have h2 : ∫ t in (0 : ℝ)..x, ‖Linv h t‖ ≤ ∫ t in (0 : ℝ)..x, M / (2 * Real.cos b ^ 3) := by
    refine intervalIntegral.integral_mono_on (le_of_lt hx.1) hInt.norm
      intervalIntegrable_const ?_
    intro t ht
    rw [Real.norm_eq_abs]
    rcases eq_or_lt_of_le ht.1 with h0 | ht0
    · subst h0
      have hz : Linv h 0 = 0 := by unfold Linv; simp
      rw [hz, abs_zero]
      exact div_nonneg hMnn (by positivity)
    · exact abs_linv_le hb hbπ hcont hM ⟨ht0, lt_of_le_of_lt ht.2 hx.2⟩
  calc |LinvI h x| ≤ ∫ t in (0 : ℝ)..x, ‖Linv h t‖ := h1
    _ ≤ ∫ t in (0 : ℝ)..x, M / (2 * Real.cos b ^ 3) := h2
    _ = x * (M / (2 * Real.cos b ^ 3)) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ b * (M / (2 * Real.cos b ^ 3)) :=
        mul_le_mul_of_nonneg_right (le_of_lt hx.2) (div_nonneg hMnn (by positivity))
    _ = b * M / (2 * Real.cos b ^ 3) := by ring

theorem Psi23Smooth {α : ℝ} {ψ : ℝ → ℝ} (hψ : Work.FTS.PhiStar.AngModel α ψ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Work.FTS.PhiStar.Psi2 ψ) θ ∧
    ContDiffAt ℝ 2 (Work.FTS.PhiStar.Psi3 ψ) θ := by
  set b : ℝ := (θ + Real.pi / 2) / 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith [hθ.1, Real.pi_pos]
  have hbπ : b < Real.pi / 2 := by rw [hbdef]; linarith [hθ.2]
  have hθb : θ ∈ Set.Ioo 0 b := by refine ⟨hθ.1, ?_⟩; rw [hbdef]; linarith [hθ.2]
  -- the bound and continuity of `ψ` on the sub-interval
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hψ.cont
  have hM' : ∀ x ∈ Set.Icc 0 (Real.pi / 2), |ψ x| ≤ M := by
    intro x hx; simpa only [Real.norm_eq_abs] using hM x hx
  have hsub : Set.Ioo 0 b ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 hbπ)⟩
  have hψcont : ContinuousOn ψ (Set.Ioo 0 b) := hψ.cont.mono hsub
  have hψbdd : ∀ t ∈ Set.Ioo 0 b, |ψ t| ≤ M := fun t ht => hM' t (hsub ht)
  -- step 1: `ψ₂` is `C²` at `θ`
  have hCD2 : ContDiffOn ℝ 2 (Psi2 ψ) (Set.Ioo 0 b) :=
    contDiffOn_two_s2.mul (contDiffOn_two_LinvI hb hbπ hψcont hψbdd)
  have hPsi2 : ContDiffAt ℝ 2 (Psi2 ψ) θ := hCD2.contDiffAt (isOpen_Ioo.mem_nhds hθb)
  -- the bound and continuity of `ψ₂` on the sub-interval, for the second iteration
  have hPsi2cont : ContinuousOn (Psi2 ψ) (Set.Ioo 0 b) := hCD2.continuousOn
  have hPsi2bdd : ∀ t ∈ Set.Ioo 0 b, |Psi2 ψ t| ≤ b * M / (2 * Real.cos b ^ 3) := by
    intro t ht
    have hx : |LinvI ψ t| ≤ b * M / (2 * Real.cos b ^ 3) :=
      abs_LinvI_le hb hbπ hψcont hψbdd ht
    have hs2le : |Work.Construction.s2 t| ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.abs_sin_le_one _
    calc |Psi2 ψ t| = |Work.Construction.s2 t * LinvI ψ t| := by rfl
      _ = |Work.Construction.s2 t| * |LinvI ψ t| := by rw [abs_mul]
      _ ≤ 1 * (b * M / (2 * Real.cos b ^ 3)) :=
          mul_le_mul hs2le hx (abs_nonneg _) zero_le_one
      _ = b * M / (2 * Real.cos b ^ 3) := by ring
  -- step 2: `ψ₃` is `C²` at `θ`
  have hCD3 : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Construction.s2 θ * LinvI (Psi2 ψ) θ)
      (Set.Ioo 0 b) :=
    contDiffOn_two_s2.mul (contDiffOn_two_LinvI hb hbπ hPsi2cont hPsi2bdd)
  have hPsi3 : ContDiffAt ℝ 2 (Psi3 ψ) θ := hCD3.contDiffAt (isOpen_Ioo.mem_nhds hθb)
  exact ⟨hPsi2, hPsi3⟩

end Work.FTS.PhiStar
