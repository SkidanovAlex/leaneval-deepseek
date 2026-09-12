import Mathlib

/-!
# D2-core: lower bound over one full period

The pointwise estimate `‖1 - q e^{it}‖² = 1 - 2q cos t + q² ≥ sin²t`
(equality of the difference with `(cos t - q)² ≥ 0`) together with
`‖1 - q e^{it}‖ ≥ 1` for `cos t ≤ 0` shows

    log ‖1 - q(t) e^{it}‖  ≥  m(t),
    m(t) := log|sin t|  for cos t ≥ 0,   and  m(t) := 0  for cos t < 0,

for every `q(t) ∈ [0,1]`.  Since `m` is `2π`-periodic and
`∫_0^{2π} m = 2·∫_0^{π/2} log(sin t) dt = -π log 2`
(with the two `cos ≥ 0` windows each contributing `-(π/2) log 2`), any
function `q : ℝ → [0,1]` satisfies, over any interval of length exactly
`2π`,

    ∫_u^{u+2π} log ‖1 - q(t) e^{it}‖ dt  ≥  -π log 2.

Mathlib hints: `Real.sin_sq_add_cos_sq`, `Real.log_mul` etc.; the integral
of `log(sin)` is `∫_0^{π/2} log(sin x) = -(π/2) log 2` (search Mathlib for
`integral_log_sin`, `integral_log_cos`; they occur near the Beta/Gamma
function material, e.g. in
Mathlib/Analysis/SpecialFunctions/Integrals/... or Gamma files).  Use
`intervalIntegral` notation `∫ x in a..b, ...`.
-/

noncomputable section

open scoped Real Complex
open Complex

namespace Submission.Core

abbrev E (t : ℝ) : ℂ := cexp ((t : ℂ) * Complex.I)

/-- The integrand `log ‖1 - q(t)·e^{it}‖`. -/
noncomputable def perF (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖

/-- The pointwise lower bound `m(t) = log(sin t)` when `cos t > 0`, else `0`
(using mathlib's convention `log x = log |x|` for `x < 0`). -/
noncomputable def perM (t : ℝ) : ℝ :=
  if 0 < Real.cos t then Real.log (Real.sin t) else 0

open MeasureTheory

/-- `‖1 - q·e^{it}‖² = 1 - 2q cos t + q²` for real `q`. -/
lemma norm_sq_one_sub_ofReal_mul_exp (q t : ℝ) :
    ‖(1 : ℂ) - (q : ℂ) * E t‖ ^ 2 = 1 - 2 * q * Real.cos t + q ^ 2 := by
  have hE : E t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
    simpa [E] using (Complex.exp_ofReal_mul_I t)
  rw [hE]
  have hz : (1 : ℂ) - (q : ℂ) * ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)
      = ((1 - q * Real.cos t : ℝ) : ℂ) + ((-q * Real.sin t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.ofReal_mul]
    · simp [Complex.ofReal_mul]
  rw [hz, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hsc : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  nlinarith

/-- `|sin t| ≤ ‖1 - q·e^{it}‖` for every real `q`. -/
lemma abs_sin_le_norm_one_sub (q t : ℝ) : |Real.sin t| ≤ ‖(1 : ℂ) - (q : ℂ) * E t‖ := by
  have hsc : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  have hs : (Real.sin t) ^ 2 ≤ ‖(1 : ℂ) - (q : ℂ) * E t‖ ^ 2 := by
    nlinarith [norm_sq_one_sub_ofReal_mul_exp q t, sq_nonneg (Real.cos t - q)]
  simpa [pow_two] using abs_le_of_sq_le_sq hs (norm_nonneg _)

/-- If `cos t ≤ 0` and `q ≥ 0`, then `‖1 - q·e^{it}‖ ≥ 1`. -/
lemma one_le_norm_one_sub_of_cos_nonpos (q : ℝ) (t : ℝ) (hq0 : 0 ≤ q)
    (hcos : Real.cos t ≤ 0) : 1 ≤ ‖(1 : ℂ) - (q : ℂ) * E t‖ := by
  have hsq : 1 ≤ ‖(1 : ℂ) - (q : ℂ) * E t‖ ^ 2 := by
    rw [norm_sq_one_sub_ofReal_mul_exp q t]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hq0 hcos, sq_nonneg q]
  exact (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp (by simpa using hsq)

/-- Pointwise lower bound `m(t) ≤ log ‖1 - q(t)·e^{it}‖` away from the zeros
of `sin`. -/
lemma perM_le_perF_of_sin_ne_zero (q : ℝ → ℝ) (t : ℝ)
    (hq0 : 0 ≤ q t) (hsin : Real.sin t ≠ 0) :
    perM t ≤ perF q t := by
  unfold perM perF
  by_cases hc : 0 < Real.cos t
  · rw [if_pos hc]
    rw [← Real.log_abs (Real.sin t)]
    exact Real.log_le_log (abs_pos.2 hsin) (abs_sin_le_norm_one_sub (q t) t)
  · rw [if_neg hc]
    simpa using Real.log_le_log zero_lt_one
      (one_le_norm_one_sub_of_cos_nonpos (q t) t hq0 (le_of_not_gt hc))

/-- The set of zeros of `sin` is countable. -/
lemma countable_setOf_sin_eq_zero : {t : ℝ | Real.sin t = 0}.Countable := by
  let f : ℤ → ℝ := fun n => (n : ℝ) * Real.pi
  have hset : {t : ℝ | Real.sin t = 0} = Set.range f := by
    ext t
    constructor
    · intro ht
      rcases (Real.sin_eq_zero_iff.mp ht) with ⟨n, hn⟩
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      rw [← hn]
      exact Real.sin_eq_zero_iff.mpr ⟨n, rfl⟩
  rw [hset]
  exact Set.countable_range f

/-- Almost every real number is not a zero of `sin`. -/
lemma ae_sin_ne_zero : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Real.sin t ≠ 0 := by
  simpa using countable_setOf_sin_eq_zero.ae_notMem volume

/-- The pointwise bound holds almost everywhere (for `q` taking values in
`[0,∞)`). -/
lemma ae_perM_le_perF (q : ℝ → ℝ) (hq0 : ∀ t : ℝ, 0 ≤ q t) :
    ∀ᵐ t ∂(volume : Measure ℝ), perM t ≤ perF q t := by
  filter_upwards [ae_sin_ne_zero] with t ht
  exact perM_le_perF_of_sin_ne_zero q t (hq0 t) ht

/-- `perM` is measurable. -/
lemma measurable_perM : Measurable perM := by
  unfold perM
  exact Measurable.ite (p := fun t : ℝ => 0 < Real.cos t)
    (Real.continuous_cos.measurable (isOpen_Ioi.measurableSet : MeasurableSet (Set.Ioi (0 : ℝ))))
    (by fun_prop) (by fun_prop)

/-- `log(sin t) ≤ 0` (for every `t`, with the usual conventions). -/
lemma log_sin_nonpos (t : ℝ) : Real.log (Real.sin t) ≤ 0 := by
  by_cases h : Real.sin t = 0
  · simp [h]
  · have hpos : 0 < |Real.sin t| := abs_pos.2 h
    have hle : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
    have := Real.log_le_log hpos hle
    simpa using this

/-- `|perM t| ≤ |log(sin t)|` pointwise. -/
lemma abs_perM_le_abs_log_sin (t : ℝ) : |perM t| ≤ |Real.log (Real.sin t)| := by
  unfold perM
  by_cases hc : 0 < Real.cos t
  · simp [hc]
  · simp [hc]

/-- `perM` is interval integrable over every interval. -/
lemma intervalIntegrable_perM (a b : ℝ) : IntervalIntegrable perM volume a b := by
  let g : ℝ → ℝ := fun t => |Real.log (Real.sin t)|
  have hg : IntervalIntegrable g volume a b := (intervalIntegrable_log_sin (a := a) (b := b)).abs
  refine IntervalIntegrable.mono_fun' (g := g) hg ?hfm ?hle
  · have hmeas : AEStronglyMeasurable perM volume := measurable_perM.aemeasurable.aestronglyMeasurable
    exact hmeas.mono_measure (Measure.restrict_le_self)
  · apply ae_of_all
    intro t
    exact abs_perM_le_abs_log_sin t

/-- `perM` is `2π`-periodic. -/
lemma perM_periodic : Function.Periodic perM (2 * Real.pi) := by
  intro t
  unfold perM
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma perM_of_cos_pos {t : ℝ} (h : 0 < Real.cos t) : perM t = Real.log (Real.sin t) := by
  simp [perM, h]

lemma perM_of_cos_nonpos {t : ℝ} (h : ¬ 0 < Real.cos t) : perM t = 0 := by
  simp [perM, h]

/-- `m(t) + m(t + π) = log(sin t)` for every `t`. -/
lemma perM_add_period_half (t : ℝ) : perM t + perM (t + Real.pi) = Real.log (Real.sin t) := by
  by_cases hc : 0 < Real.cos t
  · rw [perM_of_cos_pos hc]
    have hc2 : ¬ 0 < Real.cos (t + Real.pi) := by
      rw [Real.cos_add_pi]
      exact not_lt_of_ge (by linarith)
    rw [perM_of_cos_nonpos hc2]
    ring
  · by_cases hc0 : Real.cos t = 0
    · have hc2 : ¬ 0 < Real.cos (t + Real.pi) := by
        rw [Real.cos_add_pi]
        simp [hc0]
      rw [perM_of_cos_nonpos hc, perM_of_cos_nonpos hc2]
      have hsin : Real.sin t = 1 ∨ Real.sin t = -1 := Real.cos_eq_zero_iff_sin_eq.mp hc0
      rcases hsin with h1 | h2
      · simp [h1]
      · rw [h2, Real.log_neg_eq_log]
        simp
    · have hlt : Real.cos t < 0 := lt_of_le_of_ne (le_of_not_gt hc) hc0
      have hc2 : 0 < Real.cos (t + Real.pi) := by
        rw [Real.cos_add_pi]
        linarith
      rw [perM_of_cos_nonpos hc, perM_of_cos_pos hc2]
      rw [Real.sin_add_pi]
      simp

/-- `∫_0^{2π} m = -π log 2`. -/
lemma integral_perM_zero_two_pi :
    (∫ t in 0..(2 * Real.pi), perM t) = -Real.pi * Real.log 2 := by
  have h1 : IntervalIntegrable perM volume 0 Real.pi := intervalIntegrable_perM 0 Real.pi
  have h2 : IntervalIntegrable perM volume Real.pi (2 * Real.pi) :=
    intervalIntegrable_perM Real.pi (2 * Real.pi)
  have hI2 : IntervalIntegrable (fun t : ℝ => perM (t + Real.pi)) volume 0 Real.pi := by
    have htmp : IntervalIntegrable (fun t : ℝ => perM (t + Real.pi)) volume 0 (2 * Real.pi - Real.pi) := by
      simpa using (intervalIntegrable_perM Real.pi (2 * Real.pi)).comp_add_right Real.pi
    have hsub : 2 * Real.pi - Real.pi = Real.pi := by ring
    simpa [hsub] using htmp
  calc
    (∫ t in 0..(2 * Real.pi), perM t)
        = (∫ t in 0..Real.pi, perM t) + ∫ t in Real.pi..(2 * Real.pi), perM t := by
            rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    _ = (∫ t in 0..Real.pi, perM t) + ∫ t in 0..Real.pi, perM (t + Real.pi) := by
            congr 1
            simpa [two_mul] using
              (intervalIntegral.integral_comp_add_right (f := perM) (d := Real.pi)).symm
    _ = ∫ t in 0..Real.pi, (perM t + perM (t + Real.pi)) := by
            rw [← intervalIntegral.integral_add h1 hI2]
    _ = ∫ t in 0..Real.pi, Real.log (Real.sin t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact perM_add_period_half t
    _ = -Real.pi * Real.log 2 := by
            rw [integral_log_sin_zero_pi]
            ring

/-- **Full-period D2 core.**  For ANY `q : ℝ → [0,1]` and any starting
point `u`, the integral of `log ‖1 - q(t)·e^{it}‖` over one full period
`[u, u+2π]` is at least `-π·log 2`. -/
theorem period_lower_bound (u : ℝ) (q : ℝ → ℝ)
    (hq0 : ∀ t : ℝ, 0 ≤ q t) (hq1 : ∀ t : ℝ, q t ≤ 1) :
    (∫ t in u..(u + 2 * Real.pi),
        Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖)
      ≥ -Real.pi * Real.log 2 := by
  by_cases hF : IntervalIntegrable (perF q) volume u (u + 2 * Real.pi)
  · have hM : IntervalIntegrable perM volume u (u + 2 * Real.pi) :=
      intervalIntegrable_perM u (u + 2 * Real.pi)
    have hAE : ∀ᵐ t ∂(volume : Measure ℝ), perM t ≤ perF q t := ae_perM_le_perF q hq0
    have hmono : (∫ t in u..(u + 2 * Real.pi), perM t)
        ≤ ∫ t in u..(u + 2 * Real.pi), perF q t :=
      intervalIntegral.integral_mono_ae
        (by nlinarith [Real.pi_pos.le]) hM hF hAE
    have hval : (∫ t in u..(u + 2 * Real.pi), perM t) = -Real.pi * Real.log 2 := by
      calc
        (∫ t in u..(u + 2 * Real.pi), perM t)
            = ∫ t in 0..(0 + 2 * Real.pi), perM t := perM_periodic.intervalIntegral_add_eq u 0
        _ = ∫ t in 0..(2 * Real.pi), perM t := by simp
        _ = -Real.pi * Real.log 2 := integral_perM_zero_two_pi
    rw [hval] at hmono
    simpa [perF] using hmono
  · have hzero : (∫ t in u..(u + 2 * Real.pi),
        Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖) = 0 := by
      have hFraw : ¬ IntervalIntegrable
          (fun t : ℝ => Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖)
          volume u (u + 2 * Real.pi) := by
        change ¬ IntervalIntegrable (perF q) volume u (u + 2 * Real.pi)
        exact hF
      exact intervalIntegral.integral_undef hFraw
    rw [hzero]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith


/-- Unimodal on `[a,b]` with peak `m`: monotone increasing up to `m`, then
non-increasing after `m`.  (Shared definition used by the D2 modules.) -/
def UnimodalOn (a b m : ℝ) (q : ℝ → ℝ) : Prop :=
  a ≤ m ∧ m ≤ b ∧ MonotoneOn q (Set.Icc a m) ∧ AntitoneOn q (Set.Icc m b)

/-- **L2: unimodality makes superlevel sets intervals.**  For a unimodal
`q` on `[a,b]`, the set `{t ∈ [a,b] | s < q t}` is order-connected
(an interval, possibly empty) for every level `s`. -/
lemma superlevel_ordConnected (a b m s : ℝ) (q : ℝ → ℝ)
    (hu : UnimodalOn a b m q) :
    Set.OrdConnected {t : ℝ | a ≤ t ∧ t ≤ b ∧ s < q t} := by
  rw [Set.ordConnected_iff]
  intro x hx y hy hxy z hzxy
  have hxz : x ≤ z := hzxy.1
  have hzy : z ≤ y := hzxy.2
  have hxL : a ≤ x ∧ x ≤ b ∧ s < q x := hx
  have hyL : a ≤ y ∧ y ≤ b ∧ s < q y := hy
  have hmr : m ≤ b := hu.2.1
  have hmono : MonotoneOn q (Set.Icc a m) := hu.2.2.1
  have hanti : AntitoneOn q (Set.Icc m b) := hu.2.2.2
  constructor
  · exact le_trans hxL.1 hxz
  constructor
  · exact le_trans hzy hyL.2.1
  · by_cases hzm : z ≤ m
    · have hxz_le : q x ≤ q z := hmono (Set.mem_Icc.mpr ⟨hxL.1, le_trans hxz hzm⟩)
        (Set.mem_Icc.mpr ⟨le_trans hxL.1 hxz, hzm⟩) hxz
      exact lt_of_lt_of_le hxL.2.2 hxz_le
    · have hmz : m ≤ z := le_of_not_ge hzm
      have hzy_ge : q y ≤ q z := hanti (Set.mem_Icc.mpr ⟨hmz, le_trans hzy hyL.2.1⟩)
        (Set.mem_Icc.mpr ⟨le_trans hmz hzy, hyL.2.1⟩) hzy
      exact lt_of_lt_of_le hyL.2.2 hzy_ge


end Submission.Core

end
