import Mathlib
import Submission.Commons.Analysis.Oscillatory.van_der_corput_bound
import Submission.Commons.Analysis.Oscillatory.poly_first_derivative_test
import Submission.Commons.Analysis.Calculus.exists_band_split

open MeasureTheory Set
open scoped Real Interval ComplexConjugate

namespace Commons.Analysis.Oscillatory

noncomputable section

/-- The quadratic phase `t ↦ 2π(ct² + dt)`. -/
def quadPhase (c d : ℝ) : ℝ → ℝ := fun t => 2 * Real.pi * (c * t ^ 2 + d * t)

@[simp] lemma quadPhase_apply (c d t : ℝ) : quadPhase c d t = 2 * Real.pi * (c * t ^ 2 + d * t) := rfl

lemma deriv_quadPhase (c d x : ℝ) :
    deriv (quadPhase c d) x = 2 * Real.pi * (2 * c * x + d) := by
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have h1 : HasDerivAt (fun t : ℝ => c * t ^ 2 + d * t) (c * (2 * x) + d * 1) x :=
    (hp.const_mul c).add ((hasDerivAt_id x).const_mul d)
  have h1' : HasDerivAt (fun t : ℝ => c * t ^ 2 + d * t) (2 * c * x + d) x := by
    convert h1 using 1
    ring
  have h2 : HasDerivAt (fun t : ℝ => 2 * Real.pi * (c * t ^ 2 + d * t))
      (2 * Real.pi * (2 * c * x + d)) x := h1'.const_mul (2 * Real.pi)
  change deriv (fun t : ℝ => 2 * Real.pi * (c * t ^ 2 + d * t)) x
      = 2 * Real.pi * (2 * c * x + d)
  exact h2.deriv

/-- Extend a lower bound `lam ≤ |f|` from the open interval to the closed interval,
using continuity of `f`. -/
lemma abs_ge_on_Icc_of_Ioo {a b lam : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ x ∈ Set.Ioo a b, lam ≤ |f x|) :
    ∀ x ∈ Set.Icc a b, lam ≤ |f x| := by
  have hclosed : IsClosed {x : ℝ | lam ≤ |f x|} :=
    isClosed_le continuous_const (continuous_abs.comp hf)
  have hcl := closure_minimal (fun x hx => h x hx) hclosed
  rw [closure_Ioo hab.ne] at hcl
  exact fun x hx => hcl hx

/-- First-derivative van der Corput test with the lower bound required only on the
open interval. -/
lemma vdc_first_deriv_Ioo {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hφ : ContDiff ℝ 2 φ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc a b) ∨ AntitoneOn (deriv φ) (Set.Icc a b))
    (hbound : ∀ x ∈ Set.Ioo a b, lam ≤ |deriv φ x|) :
    ‖∫ t in a..b, osc φ t‖ ≤ 4 / lam := by
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq
    simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  · have hderiv_cont : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
    have hb' := abs_ge_on_Icc_of_Ioo hlt hderiv_cont hbound
    simpa [osc] using vdc_first_deriv (le_of_lt hlt) hlam hφ hmono hb'

/-- Quadratic-phase oscillatory integral bound, positive leading coefficient:
`‖∫_a^b e^{2πi(ct²+dt)}‖ ≤ 8/√c` for `0 < c` and `a ≤ b`. -/
lemma quad_phase_pos_le {c d a b : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    ‖∫ t in a..b, osc (quadPhase c d) t‖ ≤ 8 / Real.sqrt c := by
  set Λ : ℝ := 4 * Real.pi * c with hΛdef
  have hΛpos : 0 < Λ := by rw [hΛdef]; positivity
  have hφdiff : ContDiff ℝ 2 (quadPhase c d) := by unfold quadPhase; fun_prop
  have hderivφ_cont : Continuous (deriv (quadPhase c d)) := by
    rw [show deriv (quadPhase c d) = fun x => 2 * Real.pi * (2 * c * x + d) from
      funext (deriv_quadPhase c d)]
    fun_prop
  have hmono : Monotone (deriv (quadPhase c d)) := by
    intro x y hxy
    rw [deriv_quadPhase c d x, deriv_quadPhase c d y]
    have hpos2 : (0:ℝ) < 2 * Real.pi * (2 * c) := by positivity
    nlinarith [hxy]
  set μ : ℝ := 2 * Real.sqrt Λ with hμdef
  have hμpos : 0 < μ := by
    rw [hμdef]; exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hΛpos)
  have hgr : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      Λ * (y - x) ≤ deriv (quadPhase c d) y - deriv (quadPhase c d) x := by
    intro x y _ _ hxy
    rw [deriv_quadPhase c d x, deriv_quadPhase c d y, hΛdef]
    exact le_of_eq (by ring)
  obtain ⟨p, q, hap, hpq, hqb, hleft, hright, hlen⟩ :=
    Commons.Analysis.Calculus.exists_band_split hab hμpos hΛpos (deriv (quadPhase c d))
      hderivφ_cont.continuousOn hgr
  have hL : ∀ x ∈ Set.Ioo a p, μ ≤ |deriv (quadPhase c d) x| := by
    intro x hx
    have h1 : deriv (quadPhase c d) x ≤ -μ := hleft x hx
    have h2 : deriv (quadPhase c d) x < 0 := by linarith
    rw [abs_of_neg h2]
    linarith
  have hint_left : ‖∫ t in a..p, osc (quadPhase c d) t‖ ≤ 4 / μ :=
    vdc_first_deriv_Ioo hap hμpos hφdiff (Or.inl (hmono.monotoneOn _)) hL
  have hR : ∀ x ∈ Set.Ioo q b, μ ≤ |deriv (quadPhase c d) x| := by
    intro x hx
    have h1 : μ ≤ deriv (quadPhase c d) x := hright x hx
    rw [abs_of_nonneg (by linarith)]
    exact h1
  have hint_right : ‖∫ t in q..b, osc (quadPhase c d) t‖ ≤ 4 / μ :=
    vdc_first_deriv_Ioo hqb hμpos hφdiff (Or.inl (hmono.monotoneOn _)) hR
  have hint_mid : ‖∫ t in p..q, osc (quadPhase c d) t‖ ≤ 2 * μ / Λ := by
    have h1 : ‖∫ t in p..q, osc (quadPhase c d) t‖ ≤ ∫ t in p..q, ‖osc (quadPhase c d) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hpq
    have h2 : (∫ t in p..q, ‖osc (quadPhase c d) t‖) = ∫ t in p..q, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact osc_norm (quadPhase c d) t
    rw [h2, intervalIntegral.integral_const] at h1
    simp only [smul_eq_mul, mul_one] at h1
    linarith [hlen]
  have hφc : Continuous (quadPhase c d) := hφdiff.continuous
  have hosc_cont : Continuous (fun t => osc (quadPhase c d) t) := by
    rw [show (fun t => osc (quadPhase c d) t)
        = (fun t => Complex.exp (Complex.I * (quadPhase c d t : ℂ))) from rfl]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hφc))
  have hInt1 : (∫ t in a..p, osc (quadPhase c d) t) + (∫ t in p..q, osc (quadPhase c d) t)
      = ∫ t in a..q, osc (quadPhase c d) t :=
    intervalIntegral.integral_add_adjacent_intervals (hosc_cont.intervalIntegrable a p)
      (hosc_cont.intervalIntegrable p q)
  have hInt2 : (∫ t in a..q, osc (quadPhase c d) t) + (∫ t in q..b, osc (quadPhase c d) t)
      = ∫ t in a..b, osc (quadPhase c d) t :=
    intervalIntegral.integral_add_adjacent_intervals (hosc_cont.intervalIntegrable a q)
      (hosc_cont.intervalIntegrable q b)
  have hsumE : (∫ t in a..b, osc (quadPhase c d) t)
      = (∫ t in a..p, osc (quadPhase c d) t) + (∫ t in p..q, osc (quadPhase c d) t)
        + (∫ t in q..b, osc (quadPhase c d) t) := by
    rw [← hInt2, ← hInt1]
  have hsum : ‖∫ t in a..b, osc (quadPhase c d) t‖ ≤
      ‖∫ t in a..p, osc (quadPhase c d) t‖ + ‖∫ t in p..q, osc (quadPhase c d) t‖
        + ‖∫ t in q..b, osc (quadPhase c d) t‖ := by
    rw [hsumE]
    have h1 := norm_add_le (∫ t in a..p, osc (quadPhase c d) t)
      (∫ t in p..q, osc (quadPhase c d) t)
    have h2 := norm_add_le ((∫ t in a..p, osc (quadPhase c d) t)
        + (∫ t in p..q, osc (quadPhase c d) t))
      (∫ t in q..b, osc (quadPhase c d) t)
    linarith
  have hΛne : Λ ≠ 0 := ne_of_gt hΛpos
  have hs : Real.sqrt Λ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hΛpos)
  have hsq : (Real.sqrt Λ) ^ 2 = Λ := Real.sq_sqrt (le_of_lt hΛpos)
  have hcomb : 4 / μ + 2 * μ / Λ + 4 / μ = 8 / Real.sqrt Λ := by
    rw [hμdef]
    field_simp
    ring_nf
    rw [hsq]
    ring
  have hLam_sqrt : Real.sqrt Λ = 2 * Real.sqrt (Real.pi * c) := by
    rw [hΛdef]
    rw [show (4:ℝ) * Real.pi * c = 4 * (Real.pi * c) from by ring]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hspi1 : (1:ℝ) ≤ Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hfinal4 : (4:ℝ) / Real.sqrt (Real.pi * c) ≤ 8 / Real.sqrt c := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos) c]
    rw [div_le_div_iff₀ (by positivity) hsqrtc]
    nlinarith [hsqrtc, hspi1]
  calc ‖∫ t in a..b, osc (quadPhase c d) t‖
      ≤ ‖∫ t in a..p, osc (quadPhase c d) t‖ + ‖∫ t in p..q, osc (quadPhase c d) t‖
          + ‖∫ t in q..b, osc (quadPhase c d) t‖ := hsum
    _ ≤ 4 / μ + 2 * μ / Λ + 4 / μ := by linarith [hint_left, hint_mid, hint_right]
    _ = 8 / Real.sqrt Λ := hcomb
    _ = 4 / Real.sqrt (Real.pi * c) := by rw [hLam_sqrt]; field_simp; norm_num
    _ ≤ 8 / Real.sqrt c := hfinal4

private lemma integral_quadratic_phase_le_aux (c d a b : ℝ) (hc : c ≠ 0) (hab : a ≤ b) :
    ‖∫ t in a..b, osc (quadPhase c d) t‖ ≤ 8 / Real.sqrt |c| := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hcabs : (0:ℝ) < |c| := abs_pos.mpr hc
    have habs : |c| = -c := abs_of_neg hcneg
    have hnegcong : ‖∫ t in a..b, osc (quadPhase (-c) (-d)) t‖
        = ‖∫ t in a..b, osc (quadPhase c d) t‖ := by
      have hcomp : quadPhase (-c) (-d) = fun x => -(quadPhase c d x) := by
        funext x
        simp only [quadPhase_apply]
        ring
      have hfun : (fun t => osc (quadPhase (-c) (-d)) t)
          = (fun t => starRingEnd ℂ (osc (quadPhase c d) t)) := by
        funext t
        rw [hcomp]
        exact osc_neg_conj (quadPhase c d) t
      have hcj : (∫ t in a..b, osc (quadPhase (-c) (-d)) t)
          = starRingEnd ℂ (∫ t in a..b, osc (quadPhase c d) t) := by
        rw [hfun]
        exact intervalIntegral.intervalIntegral_conj
      rw [hcj, Complex.norm_conj]
    have hfun : quadPhase (-c) (-d) = quadPhase |c| (-d) := by
      funext t
      simp only [quadPhase_apply, habs]
    rw [← hnegcong, hfun]
    exact quad_phase_pos_le hcabs hab
  · rw [abs_of_pos hcpos]
    exact quad_phase_pos_le hcpos hab

theorem integral_quadratic_phase_le (c d a b : ℝ) (hc : c ≠ 0) :
    ‖∫ t in a..b, Complex.exp (((2 * Real.pi * (c * t ^ 2 + d * t) : ℝ) : ℂ) * Complex.I)‖
      ≤ 8 / Real.sqrt |c| := by
  have hconv : (∫ t in a..b,
        Complex.exp (((2 * Real.pi * (c * t ^ 2 + d * t) : ℝ) : ℂ) * Complex.I))
      = ∫ t in a..b, osc (quadPhase c d) t := by
    rw [integral_exp_comm]
    rfl
  rw [hconv]
  rcases le_total a b with hab | hba
  · exact integral_quadratic_phase_le_aux c d a b hc hab
  · have hsym : (∫ t in a..b, osc (quadPhase c d) t)
        = -∫ t in b..a, osc (quadPhase c d) t :=
      intervalIntegral.integral_symm b a
    rw [hsym, norm_neg]
    exact integral_quadratic_phase_le_aux c d b a hc hba

end

end Commons.Analysis.Oscillatory
