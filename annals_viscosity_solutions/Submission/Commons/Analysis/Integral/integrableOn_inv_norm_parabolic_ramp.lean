import Mathlib
import Submission.Commons.Analysis.Real.exists_cos_sin_of_sq_add_sq_eq_one
import Submission.Commons.Analysis.Integral.integrableOn_inv_sqrt_abs_trig
import Submission.Commons.Analysis.Integral.integrableOn_inv_sqrt_abs_parabolic_ramp_sub

open MeasureTheory Set Real
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Integral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma norm_sq_general (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (g A θ : ℝ) :
    ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖^2
      = g^2 * ‖xi‖^2 + A^2
        + 2*g*A*(Real.cos θ * inner ℝ xi e + Real.sin θ * inner ℝ xi f) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm, hef, he, hf,
    starRingEnd_apply, star_trivial]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

private lemma bessel (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) :
    (inner ℝ xi e)^2 + (inner ℝ xi f)^2 ≤ ‖xi‖^2 := by
  set p := inner ℝ xi e with hp
  set q := inner ℝ xi f with hq
  have hpu : inner ℝ xi (p • e + q • f) = p^2+q^2 := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, hp, hq]; ring
  have hnu : ‖p • e + q • f‖^2 = p^2+q^2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hef, mul_zero,
        norm_smul, norm_smul, he, hf, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one,
        sq_abs, sq_abs]
    ring
  have hexp : ‖xi - (p • e + q • f)‖^2 = ‖xi‖^2 - (p^2+q^2) := by
    rw [show xi - (p•e+q•f) = xi + (-(p•e+q•f)) by abel]
    rw [norm_add_sq_real, inner_neg_right, norm_neg, hpu, hnu]
    ring
  have h3 : (0:ℝ) ≤ ‖xi - (p • e + q • f)‖^2 := by positivity
  rw [hexp] at h3
  linarith

private lemma cos_sin_linear_ge (p q θ : ℝ) :
    -(Real.sqrt (p^2 + q^2)) ≤ p * Real.cos θ + q * Real.sin θ := by
  have h2 : (p * Real.cos θ + q * Real.sin θ)^2 ≤ p^2 + q^2 := by
    nlinarith [sq_nonneg (p * Real.sin θ - q * Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have h3 : |p * Real.cos θ + q * Real.sin θ| ≤ Real.sqrt (p^2 + q^2) :=
    Real.abs_le_sqrt h2
  linarith [neg_le_abs (p * Real.cos θ + q * Real.sin θ)]

private lemma caseA_real (p q θ z g A : ℝ) (hg : 0 ≤ g) (hA : 0 ≤ A)
    (hpq : p^2 + q^2 ≤ z^2) :
    g^2*(z^2 - p^2 - q^2) ≤ g^2*z^2 + A^2 + 2*g*A*(p*Real.cos θ + q*Real.sin θ) := by
  set R := Real.sqrt (p^2 + q^2) with hRdef
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = p^2 + q^2 := by rw [hRdef, Real.sq_sqrt (by positivity)]
  have hcs : p*Real.cos θ + q*Real.sin θ ≥ -R := by
    have hh := cos_sin_linear_ge p q θ
    rw [← hRdef] at hh; exact hh
  have hgA : 0 ≤ 2*g*A := by nlinarith
  have hmul : 2*g*A*(-R) ≤ 2*g*A*(p*Real.cos θ + q*Real.sin θ) :=
    mul_le_mul_of_nonneg_left hcs hgA
  nlinarith [hmul, sq_nonneg (g*R - A), hR2, hpq, sq_nonneg g]

private lemma caseB_real (X Y c s : ℝ) (h : c^2 + s^2 = 1) :
    |X^2 - Y^2| * |s| ≤ X^2 + Y^2 + 2*X*Y*c := by
  have hsq : ((X^2 - Y^2) * s)^2 ≤ (X^2 + Y^2 + 2*X*Y*c)^2 := by
    have h2 : s^2 = 1 - c^2 := by linarith
    have h3 : ((X^2 - Y^2) * s)^2 = (X^2 - Y^2)^2 * s^2 := by ring
    rw [h3, h2]
    nlinarith [sq_nonneg (2*X*Y + c*(X^2 + Y^2))]
  have hLnonneg : 0 ≤ X^2 + Y^2 + 2*X*Y*c := by
    nlinarith [sq_nonneg (X + Y*c), sq_nonneg (Y*s), h]
  rw [← abs_mul]
  exact abs_le_of_sq_le_sq hsq hLnonneg

private lemma sqrt_inv_eq {X h z : ℝ} (hz : 0 < z) :
    (Real.sqrt (|X| * |h| / z))⁻¹
      = (Real.sqrt z * (Real.sqrt |X|)⁻¹) * (Real.sqrt |h|)⁻¹ := by
  rw [show |X| * |h| / z = |X| * (|h| / z) by ring]
  rw [Real.sqrt_mul (abs_nonneg X) (|h| / z), Real.sqrt_div (abs_nonneg h) z]
  rw [show √|X| * (√|h| / √z) = √|X| * √|h| / √z by ring]
  rw [inv_div, div_eq_mul_inv, mul_inv]
  ring

private lemma caseB_pointwise {e f xi : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0)
    {c T ρ z : ℝ} (hz : 0 < z) (hxi : ‖xi‖ = z)
    (hpq : (inner ℝ xi e)^2 + (inner ℝ xi f)^2 = z^2)
    {θ t : ℝ}
    (hX : (c * z * t ^ ((2:ℝ)/3))^2 - (min ρ (max 0 (T - t)))^2 ≠ 0)
    (hh : inner ℝ xi e * Real.sin θ - inner ℝ xi f * Real.cos θ ≠ 0) :
    (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) •
        (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
      ≤ (Real.sqrt z * (Real.sqrt |(c * z * t ^ ((2:ℝ)/3))^2
            - (min ρ (max 0 (T - t)))^2|)⁻¹)
        * (Real.sqrt |inner ℝ xi e * Real.sin θ - inner ℝ xi f * Real.cos θ|)⁻¹ := by
  set g : ℝ := c * t ^ ((2:ℝ)/3) with hg
  set A : ℝ := min ρ (max 0 (T - t)) with hA
  set p0 : ℝ := inner ℝ xi e with hp0
  set q0 : ℝ := inner ℝ xi f with hq0
  have hnorm := norm_sq_general e f xi he hf hef g A θ
  rw [hxi] at hnorm
  have hXeq : (g * z)^2 = (c * z * t ^ ((2:ℝ)/3))^2 := by rw [hg]; ring
  have hXg : (g * z)^2 - A^2 ≠ 0 := by rw [hXeq, hA]; exact hX
  have hh' : p0 * Real.sin θ - q0 * Real.cos θ ≠ 0 := by rw [hp0, hq0]; exact hh
  set cc : ℝ := (p0 * Real.cos θ + q0 * Real.sin θ) / z with hcc
  set ss : ℝ := (p0 * Real.sin θ - q0 * Real.cos θ) / z with hss
  have hccss : cc^2 + ss^2 = 1 := by
    rw [hcc, hss, hp0, hq0]
    field_simp
    nlinarith [hpq, Real.sin_sq_add_cos_sq θ]
  have hcaseB := caseB_real (g*z) A cc ss hccss
  have hval : (g*z)^2 + A^2 + 2*(g*z)*A*cc
      = ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖^2 := by
    rw [hnorm, hcc]
    field_simp
    ring
  rw [hval] at hcaseB
  have hssabs : |ss| = |p0 * Real.sin θ - q0 * Real.cos θ| / z := by
    rw [hss, abs_div, abs_of_pos hz]
  rw [hssabs, hXeq] at hcaseB
  have hbnd : |(c * z * t ^ ((2:ℝ)/3))^2 - A^2| * |p0 * Real.sin θ - q0 * Real.cos θ| / z
      ≤ ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖^2 := by
    rw [mul_div_assoc]; exact hcaseB
  have hle : Real.sqrt (|(c * z * t ^ ((2:ℝ)/3))^2 - A^2|
        * |p0 * Real.sin θ - q0 * Real.cos θ| / z)
      ≤ ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (g • xi + A • (Real.cos θ • e + Real.sin θ • f)))]
    exact Real.sqrt_le_sqrt hbnd
  have hpos : 0 < Real.sqrt (|(c * z * t ^ ((2:ℝ)/3))^2 - A^2|
        * |p0 * Real.sin θ - q0 * Real.cos θ| / z) := by
    apply Real.sqrt_pos.mpr
    apply div_pos
    · exact mul_pos (abs_pos.mpr (by rw [hA] at hX; exact hX)) (abs_pos.mpr hh')
    · exact hz
  have hle' : (‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
      ≤ (Real.sqrt (|(c * z * t ^ ((2:ℝ)/3))^2 - A^2|
        * |p0 * Real.sin θ - q0 * Real.cos θ| / z))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hle
  have hfinal := sqrt_inv_eq (X := (c * z * t ^ ((2:ℝ)/3))^2 - A^2)
      (h := p0 * Real.sin θ - q0 * Real.cos θ) hz
  rw [hfinal] at hle'
  rw [hg, hA, hp0, hq0] at hle'
  exact hle'

private lemma caseA_pointwise {e f xi : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0)
    {c T ρ z : ℝ} (hc : 0 < c) (hρ : 0 ≤ ρ) (hxi : ‖xi‖ = z)
    (hpq : (inner ℝ xi e)^2 + (inner ℝ xi f)^2 < z^2) {θ t : ℝ} (ht : 0 < t) :
    (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) •
        (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
      ≤ (c * t ^ ((2:ℝ)/3) * Real.sqrt (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2))⁻¹ := by
  set g : ℝ := c * t ^ ((2:ℝ)/3) with hg
  set A : ℝ := min ρ (max 0 (T - t)) with hA
  have hgnn : 0 ≤ g := by rw [hg]; exact mul_nonneg hc.le (Real.rpow_nonneg ht.le _)
  have hAnn : 0 ≤ A := by rw [hA]; exact le_min hρ (le_max_left 0 _)
  have hnorm := norm_sq_general e f xi he hf hef g A θ
  rw [hxi] at hnorm
  have hcaseA := caseA_real (inner ℝ xi e) (inner ℝ xi f) θ z g A hgnn hAnn (le_of_lt hpq)
  have hbnd : g^2 * (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2)
      ≤ ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖^2 := by
    rw [hnorm]
    have e1 : Real.cos θ * inner ℝ xi e = inner ℝ xi e * Real.cos θ := mul_comm _ _
    have e2 : Real.sin θ * inner ℝ xi f = inner ℝ xi f * Real.sin θ := mul_comm _ _
    rw [e1, e2]
    exact hcaseA
  have hwpos : 0 < z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2 := by linarith
  have hbnd2 : (g * Real.sqrt (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2))^2
      ≤ ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖^2 := by
    have hs : (Real.sqrt (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2))^2
        = z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2 := Real.sq_sqrt (le_of_lt hwpos)
    nlinarith [hbnd, hs]
  have hle : g * Real.sqrt (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2)
      ≤ ‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (mul_nonneg hgnn (Real.sqrt_nonneg _))]
    exact Real.sqrt_le_sqrt hbnd2
  have hpos : 0 < g * Real.sqrt (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2) := by
    apply mul_pos
    · rw [hg]; exact mul_pos hc (Real.rpow_pos_of_pos ht _)
    · exact Real.sqrt_pos.mpr hwpos
  have hstep : (‖g • xi + A • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
      ≤ (g * Real.sqrt (z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hle
  rw [hg, hA] at hstep
  exact hstep

private lemma integrableOn_inv_rpow_two_thirds {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ ((2:ℝ)/3))⁻¹) (Set.uIoc 0 T) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-((2:ℝ)/3))) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hOn : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-((2:ℝ)/3))) (Set.Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hint
  have hEq : Set.EqOn (fun t : ℝ => t ^ (-((2:ℝ)/3))) (fun t : ℝ => (t ^ ((2:ℝ)/3))⁻¹) (Set.Ioc 0 T) := by
    intro t ht
    exact Real.rpow_neg ht.1.le (2/3)
  have hreal := hOn.congr_fun hEq measurableSet_Ioc
  rwa [Set.uIoc_of_le hT.le]

private lemma ae_trig_ne_zero {p q z : ℝ} (hz : 0 < z) (hpq : p^2 + q^2 = z^2) :
    ∀ᵐ θ ∂(volume.restrict (Set.uIoc 0 (2*Real.pi))),
      p * Real.sin θ - q * Real.cos θ ≠ 0 := by
  have h1 : (p/z)^2 + (q/z)^2 = 1 := by
    rw [div_pow, div_pow, ← add_div, hpq]
    exact div_self (by positivity)
  obtain ⟨φ, hc, hs⟩ := Commons.Analysis.Real.exists_cos_sin_of_sq_add_sq_eq_one h1
  have hkey : ∀ θ, p * Real.sin θ - q * Real.cos θ = z * Real.sin (θ - φ) := by
    intro θ
    rw [Real.sin_sub, hc, hs]
    field_simp
  have hcount : ({θ : ℝ | p * Real.sin θ - q * Real.cos θ = 0}).Countable := by
    apply Set.Countable.mono _ (Set.countable_range (fun n : ℤ => φ + n * Real.pi))
    intro θ hθ
    rw [Set.mem_setOf_eq, hkey θ, mul_eq_zero] at hθ
    rcases hθ with h | h
    · exact absurd h (ne_of_gt hz)
    · rw [Real.sin_eq_zero_iff] at h
      obtain ⟨n, hn⟩ := h
      refine ⟨n, ?_⟩
      linarith [hn]
  rw [ae_restrict_iff' measurableSet_uIoc, ae_iff]
  apply measure_mono_null _ (Set.Countable.measure_zero hcount volume)
  intro x hx
  by_contra hc2
  exact hx (fun _ => hc2)

private lemma parA_strictMonoOn (c z : ℝ) (hc : 0 < c) (hz : 0 < z) :
    StrictMonoOn (fun t : ℝ => c * z * t ^ ((2:ℝ)/3)) (Set.Ioi 0) := by
  intro s hs t ht hst
  have h1 : s ^ ((2:ℝ)/3) < t ^ ((2:ℝ)/3) :=
    Real.rpow_lt_rpow hs.le hst (by norm_num)
  have h2 : (0:ℝ) < c * z := mul_pos hc hz
  nlinarith [h1]

private lemma rampD_antitoneOn (ρ T : ℝ) :
    AntitoneOn (fun t : ℝ => min ρ (max 0 (T - t))) (Set.Ioi 0) := by
  intro s hs t ht hst
  exact min_le_min_left ρ (max_le_max_left 0 (by linarith))

private lemma ae_ramp_ne_par {c T ρ z : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      min ρ (max 0 (T - t)) ≠ c * z * t ^ ((2:ℝ)/3) := by
  have hdecr : ∀ s t : ℝ, 0 < s → s < t →
      min ρ (max 0 (T - t)) - c * z * t ^ ((2:ℝ)/3)
        < min ρ (max 0 (T - s)) - c * z * s ^ ((2:ℝ)/3) := by
    intro s t hs hst
    have ht0 : 0 < t := lt_trans hs hst
    have hdd : min ρ (max 0 (T - t)) ≤ min ρ (max 0 (T - s)) :=
      rampD_antitoneOn ρ T hs ht0 hst.le
    have haa : c * z * s ^ ((2:ℝ)/3) < c * z * t ^ ((2:ℝ)/3) :=
      parA_strictMonoOn c z hc hz hs ht0 hst
    linarith
  have hsub : (Set.Ioc (0:ℝ) T ∩ {t : ℝ | min ρ (max 0 (T - t)) = c * z * t ^ ((2:ℝ)/3)}).Subsingleton := by
    rintro s ⟨hsI, hsS⟩ t ⟨htI, htS⟩
    rcases lt_trichotomy s t with h | h | h
    · exfalso
      have := hdecr s t hsI.1 h
      rw [← hsS, ← htS] at this
      linarith
    · exact h
    · exfalso
      have := hdecr t s htI.1 h
      rw [← hsS, ← htS] at this
      linarith
  have hnull : volume (Set.Ioc (0:ℝ) T ∩ {t : ℝ | min ρ (max 0 (T - t)) = c * z * t ^ ((2:ℝ)/3)}) = 0 := by
    obtain he | ⟨x, hx⟩ := hsub.eq_empty_or_singleton
    · rw [he]; simp
    · rw [hx]; simp
  rw [ae_restrict_iff' measurableSet_Ioc]
  rw [ae_iff]
  have hset : {t : ℝ | ¬ (t ∈ Set.Ioc 0 T →
        min ρ (max 0 (T - t)) ≠ c * z * t ^ ((2:ℝ)/3))}
      = Set.Ioc (0:ℝ) T ∩ {t : ℝ | min ρ (max 0 (T - t)) = c * z * t ^ ((2:ℝ)/3)} := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioc]; tauto
  rw [hset]
  exact hnull

theorem integrableOn_inv_norm_parabolic_ramp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0)
    {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T)
    (hxi : ‖xi‖ = z) (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (‖(c * p.2 ^ ((2:ℝ)/3)) • xi
          + (min ρ (max 0 (T - p.2))) • (Real.cos p.1 • e + Real.sin p.1 • f)‖)⁻¹)
      (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 T) := by
  set S1 : Set ℝ := Set.uIoc 0 (2 * Real.pi) with hS1
  set S2 : Set ℝ := Set.uIoc 0 T with hS2
  have hS1m : MeasurableSet S1 := measurableSet_uIoc
  have hS2m : MeasurableSet S2 := measurableSet_uIoc
  have hbessel : (inner ℝ xi e)^2 + (inner ℝ xi f)^2 ≤ z^2 := by
    have h := bessel e f xi he hf hef
    rwa [hxi] at h
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (‖(c * p.2 ^ ((2:ℝ)/3)) • xi
          + (min ρ (max 0 (T - p.2))) • (Real.cos p.1 • e + Real.sin p.1 • f)‖)⁻¹)
      (volume.restrict (S1 ×ˢ S2)) := by
    have hcont : Continuous (fun p : ℝ × ℝ => (c * p.2 ^ ((2:ℝ)/3)) • xi
          + (min ρ (max 0 (T - p.2))) • (Real.cos p.1 • e + Real.sin p.1 • f)) := by
      have hp23 : Continuous (fun p : ℝ × ℝ => p.2 ^ ((2:ℝ)/3)) :=
        (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 2/3)).comp continuous_snd
      have hc1 : Continuous (fun p : ℝ × ℝ => (c * p.2 ^ ((2:ℝ)/3)) • xi) :=
        (continuous_const.mul hp23).smul continuous_const
      have hA : Continuous (fun p : ℝ × ℝ => min ρ (max 0 (T - p.2))) := by fun_prop
      have hc2 : Continuous (fun p : ℝ × ℝ => (Real.cos p.1 • e + Real.sin p.1 • f)) := by fun_prop
      exact hc1.add (hA.smul hc2)
    exact ((hcont.norm).measurable.inv).aestronglyMeasurable
  by_cases hw : (inner ℝ xi e)^2 + (inner ℝ xi f)^2 = z^2
  · -- Case B
    set Ht : ℝ → ℝ := fun θ => (Real.sqrt |inner ℝ xi e * Real.sin θ - inner ℝ xi f * Real.cos θ|)⁻¹ with hHt
    set Ft : ℝ → ℝ := fun t => Real.sqrt z * (Real.sqrt |(c * z * t ^ ((2:ℝ)/3))^2
        - (min ρ (max 0 (T - t)))^2|)⁻¹ with hFt
    have hHt_int : IntegrableOn Ht S1 := by
      rw [hHt, hS1]
      exact integrableOn_inv_sqrt_abs_trig hz hw
    have hFt_int : IntegrableOn Ft S2 := by
      rw [hFt, hS2]
      exact (integrableOn_inv_sqrt_abs_parabolic_ramp_sub hc hT hρ hρT hz).const_mul (Real.sqrt z)
    have hprod : Integrable (fun p : ℝ × ℝ => Ht p.1 * Ft p.2)
        ((volume.restrict S1).prod (volume.restrict S2)) := hHt_int.mul_prod hFt_int
    have hdom_int : IntegrableOn (fun p : ℝ × ℝ => Ht p.1 * Ft p.2) (S1 ×ˢ S2) := by
      change Integrable (fun p : ℝ × ℝ => Ht p.1 * Ft p.2)
        ((volume.prod volume).restrict (S1 ×ˢ S2))
      rw [← MeasureTheory.Measure.prod_restrict]
      exact hprod
    have hθae : ∀ᵐ θ ∂(volume.restrict S1),
        inner ℝ xi e * Real.sin θ - inner ℝ xi f * Real.cos θ ≠ 0 := by
      rw [hS1]; exact ae_trig_ne_zero hz hw
    have htae : ∀ᵐ t ∂(volume.restrict S2),
        (c * z * t ^ ((2:ℝ)/3))^2 - (min ρ (max 0 (T - t)))^2 ≠ 0 := by
      have h' : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
          (c * z * t ^ ((2:ℝ)/3))^2 - (min ρ (max 0 (T - t)))^2 ≠ 0 := by
        filter_upwards [ae_ramp_ne_par (T := T) hc hρ hz, ae_restrict_mem measurableSet_Ioc]
          with t ht htmem
        intro h0
        apply ht
        have hA : 0 ≤ min ρ (max 0 (T - t)) := le_min hρ.le (le_max_left 0 _)
        have hB : 0 ≤ c * z * t ^ ((2:ℝ)/3) :=
          mul_nonneg (mul_nonneg hc.le hz.le) (Real.rpow_nonneg (le_of_lt htmem.1) _)
        have h2 : (c * z * t ^ ((2:ℝ)/3))^2 = (min ρ (max 0 (T - t)))^2 := by linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h1 | h1
        · exact h1.symm
        · linarith
      rwa [hS2, Set.uIoc_of_le hT.le]
    have hprodae : ∀ᵐ p ∂(volume.restrict (S1 ×ˢ S2)),
        ((c * z * p.2 ^ ((2:ℝ)/3))^2 - (min ρ (max 0 (T - p.2)))^2 ≠ 0)
        ∧ (inner ℝ xi e * Real.sin p.1 - inner ℝ xi f * Real.cos p.1 ≠ 0) := by
      change ∀ᵐ p ∂((volume.prod volume).restrict (S1 ×ˢ S2)), _
      rw [← MeasureTheory.Measure.prod_restrict]
      have hset : MeasurableSet {x : ℝ × ℝ |
          ((c * z * x.2 ^ ((2:ℝ)/3))^2 - (min ρ (max 0 (T - x.2)))^2 ≠ 0)
          ∧ (inner ℝ xi e * Real.sin x.1 - inner ℝ xi f * Real.cos x.1 ≠ 0)} := by
        measurability
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [hθae] with θ hθ
      filter_upwards [htae] with t ht
      exact ⟨ht, hθ⟩
    refine hdom_int.mono' hmeas ?_
    filter_upwards [hprodae, ae_restrict_mem (hS1m.prod hS2m)] with p hpbad hpmem
    obtain ⟨hXt, hθt⟩ := hpbad
    have hpt := caseB_pointwise (c := c) (T := T) (ρ := ρ) he hf hef hz hxi hw
      (θ := p.1) (t := p.2) hXt hθt
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    calc (‖(c * p.2 ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - p.2))) •
            (Real.cos p.1 • e + Real.sin p.1 • f)‖)⁻¹
        ≤ (Real.sqrt z * (Real.sqrt |(c * z * p.2 ^ ((2:ℝ)/3))^2
            - (min ρ (max 0 (T - p.2)))^2|)⁻¹)
          * (Real.sqrt |inner ℝ xi e * Real.sin p.1 - inner ℝ xi f * Real.cos p.1|)⁻¹ := hpt
      _ = Ht p.1 * Ft p.2 := by rw [hHt, hFt]; ring
  · -- Case A
    have hlt : (inner ℝ xi e)^2 + (inner ℝ xi f)^2 < z^2 := lt_of_le_of_ne hbessel hw
    set w : ℝ := z^2 - (inner ℝ xi e)^2 - (inner ℝ xi f)^2 with hwdef
    have hwpos : 0 < w := by rw [hwdef]; linarith
    set F1 : ℝ → ℝ := fun t => (c * t ^ ((2:ℝ)/3) * Real.sqrt w)⁻¹ with hF1
    have hF1_int : IntegrableOn F1 S2 := by
      rw [hF1, hS2]
      refine MeasureTheory.IntegrableOn.congr_fun
        ((integrableOn_inv_rpow_two_thirds hT).const_mul ((c * Real.sqrt w)⁻¹))
        ?_ measurableSet_uIoc
      intro t ht
      simp only [mul_inv]; ring
    have hF1' : IntegrableOn (fun p : ℝ × ℝ => F1 p.2) (S1 ×ˢ S2) := by
      change Integrable (fun p : ℝ × ℝ => F1 p.2)
        ((volume.prod volume).restrict (S1 ×ˢ S2))
      rw [← MeasureTheory.Measure.prod_restrict]
      have hone : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict S1) := by
        rw [hS1]
        haveI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) :=
          isFiniteMeasure_restrict.mpr (by rw [volume_uIoc]; exact ENNReal.ofReal_ne_top)
        exact integrable_const _
      simpa only [one_mul] using hone.mul_prod hF1_int
    refine hF1'.mono' hmeas ?_
    filter_upwards [ae_restrict_mem (hS1m.prod hS2m)] with p hp
    have htpos : 0 < p.2 := by
      have : p.2 ∈ Set.uIoc 0 T := hp.2
      rw [Set.uIoc_of_le hT.le] at this; exact this.1
    have hpt := caseA_pointwise (c := c) (T := T) (ρ := ρ) he hf hef hc hρ.le hxi hlt
      (θ := p.1) (t := p.2) htpos
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hF1, hwdef] at *
    exact hpt

end Commons.Analysis.Integral
