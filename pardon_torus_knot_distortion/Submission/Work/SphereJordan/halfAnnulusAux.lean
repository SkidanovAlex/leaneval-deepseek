import Mathlib
import Submission.Work.SphereJordan.halfAnnulusSetup
import Submission.Work.SphereJordan.bdVec_mem_upRectBd
import Submission.Work.SphereJordan.bdVec_eq_imp_smul

/-!
# Auxiliary facts about the explicit half-annulus map

This file collects the elementary facts about `bdVec`, `radVec`, `toCplx` and the standard
boundary curve `stdVec`/`stdHalf` of `Submission/Work/SphereJordan/halfAnnulusSetup.lean`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

open Work.Smooth.SphereJordan (perPt circlePoint srcUpB srcDnB cutDir)

/-! ## Facts about the period reduction `perPt` -/

theorem perPt_eq_self {σ : ℝ} (h1 : 0 ≤ σ) (h2 : σ < 2 * Real.pi) : perPt σ = σ := by
  unfold Work.Smooth.SphereJordan.perPt
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  have h : ⌊σ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h1 hpos.le, (div_lt_one hpos).mpr h2⟩
  rw [h]
  push_cast
  ring

theorem perPt_mem_Ico (τ : ℝ) : perPt τ ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  unfold Work.Smooth.SphereJordan.perPt
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  constructor
  · have := Int.floor_le (τ / (2 * Real.pi))
    have := (le_div_iff₀ hpos).mp this
    linarith
  · have := Int.lt_floor_add_one (τ / (2 * Real.pi))
    have := (div_lt_iff₀ hpos).mp this
    linarith

theorem perPt_circlePoint (τ : ℝ) :
    circlePoint (perPt τ) = circlePoint τ := by
  unfold Work.Smooth.SphereJordan.perPt
  rw [show ((τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))) =
      τ + ((-⌊τ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  exact Work.Smooth.SphereJordan.circlePoint_add_int_mul τ (-⌊τ / (2 * Real.pi)⌋)

/-! ## The complexification of the radial coordinates -/

theorem norm_toCplx {p : ℝ × ℝ} (hp : p ∈ upRect) : ‖toCplx p‖ = p.1 := by
  have h1 : 0 < p.1 := lt_of_lt_of_le (by norm_num) hp.1
  rw [toCplx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos h1]

theorem im_toCplx_up {p : ℝ × ℝ} (hp : p ∈ upRect) : 0 ≤ (toCplx p).im := by
  have h1 : 0 ≤ p.1 := le_trans (by norm_num) hp.1
  simp only [toCplx, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  exact mul_nonneg h1 (Real.sin_nonneg_of_mem_Icc ⟨hp.2.2.1, hp.2.2.2⟩)

theorem toCplx_range_up : toCplx '' upRect = {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ 0 ≤ z.im} := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨by rw [norm_toCplx hp]; exact hp.1, by rw [norm_toCplx hp]; exact hp.2.1,
      im_toCplx_up hp⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(‖z‖, Complex.arg z), ⟨h1, h2, Complex.arg_nonneg_iff.mpr h3,
      Complex.arg_le_pi z⟩, ?_⟩
    exact Complex.norm_mul_exp_arg_mul_I z

theorem radius_pos {p : ℝ × ℝ} (hp : p ∈ upRect) : 0 < p.1 := lt_of_lt_of_le (by norm_num) hp.1

theorem exp_eq_of_toCplx_eq {p q : ℝ × ℝ} (hp : p ∈ upRect) (hq : q ∈ upRect)
    (h : toCplx p = toCplx q) :
    Complex.exp ((p.2 : ℂ) * Complex.I) = Complex.exp ((q.2 : ℂ) * Complex.I) := by
  have h1 : p.1 = q.1 := by
    have := congrArg norm h
    rwa [norm_toCplx hp, norm_toCplx hq] at this
  have hne : (p.1 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (radius_pos hp)
  have h2 : (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
      = (q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) := h
  rw [← h1] at h2
  exact mul_left_cancel₀ hne h2

theorem toCplx_injOn : Set.InjOn toCplx upRect := by
  intro p hp q hq hpq
  have h1 : p.1 = q.1 := by
    have := congrArg norm hpq
    rwa [norm_toCplx hp, norm_toCplx hq] at this
  have h2 : p.2 = q.2 := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      (exp_eq_of_toCplx_eq hp hq hpq)
    have h3 : ((p.2 : ℂ) - (q.2 : ℂ) - (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I = 0 := by
      rw [sub_mul, sub_mul, sub_eq_zero, hn]; ring
    have h4 : (p.2 : ℂ) - (q.2 : ℂ) - (n : ℂ) * (2 * (Real.pi : ℂ)) = 0 :=
      (mul_eq_zero.mp h3).resolve_right Complex.I_ne_zero
    have h4b : ((p.2 - q.2 - (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) = 0 := by
      push_cast
      exact h4
    have h5 : (p.2 : ℝ) = q.2 + (n : ℝ) * (2 * Real.pi) := by
      have hre := congrArg Complex.re h4b
      simp only [Complex.ofReal_re, Complex.zero_re] at hre
      linarith
    have hlt : (n : ℝ) < 1 := by
      have hp2 : (n : ℝ) * (2 * Real.pi) ≤ Real.pi := by linarith [hp.2.2.2, hq.2.2.1]
      nlinarith [Real.pi_pos]
    have hgt : (-1 : ℝ) < (n : ℝ) := by
      have hp2 : -Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by linarith [hp.2.2.1, hq.2.2.2]
      nlinarith [Real.pi_pos]
    have hn0 : n = 0 := by
      have h1' : n < 1 := by exact_mod_cast hlt
      have h2' : -1 < n := by exact_mod_cast hgt
      omega
    rw [h5, hn0]; push_cast; ring
  exact Prod.ext h1 h2

/-! ## Membership of the interpolated point -/

theorem radVec_mem {z : ℂ} (hz : ‖z‖ ≤ 1) : radVec z ∈ upRect := by
  have hb : bdVec z ∈ upRect := (bdVec_mem_upRectBd z).1
  have hb1 : (1/2:ℝ) ≤ (bdVec z).1 := hb.1
  have hb2 : (bdVec z).1 ≤ 1 := hb.2.1
  have hb3 : (0:ℝ) ≤ (bdVec z).2 := hb.2.2.1
  have hb4 : (bdVec z).2 ≤ Real.pi := hb.2.2.2
  have h0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [radVec_fst]; nlinarith
  · rw [radVec_fst]; nlinarith
  · rw [radVec_snd]; nlinarith [Real.pi_pos]
  · rw [radVec_snd]; nlinarith [Real.pi_pos]

/-! ## The comparison with the source boundary curves -/

theorem srcUpB_eq_smul {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (τ : ℝ) :
    Work.Smooth.SphereJordan.srcUpB S τ =
      Work.Smooth.SphereJordan.cutDir S * Work.SphereJordan.stdHalf τ := by
  simp only [Work.Smooth.SphereJordan.srcUpB, Work.Smooth.SphereJordan.srcOuterUp,
    Work.Smooth.SphereJordan.srcInnerUp, Work.SphereJordan.stdHalf, Work.SphereJordan.stdVec,
    Complex.real_smul]
  split_ifs with h1 h2 h3
  · rw [Work.SphereJordan.toCplx_pair, Complex.ofReal_one, one_mul,
      show Real.pi * (Work.Smooth.SphereJordan.perPt τ / (Real.pi / 2))
        = 2 * Work.Smooth.SphereJordan.perPt τ from by field_simp]
  · rw [Work.SphereJordan.toCplx_pair, Complex.exp_pi_mul_I,
      show (-1 + (Work.Smooth.SphereJordan.perPt τ - Real.pi / 2) / (Real.pi / 2) / 2 : ℝ)
        = -(3 / 2 - Work.Smooth.SphereJordan.perPt τ / Real.pi) from by field_simp; ring]
    push_cast
    ring
  · rw [Work.SphereJordan.toCplx_pair,
      show Real.pi * (1 - (Work.Smooth.SphereJordan.perPt τ - Real.pi) / (Real.pi / 2))
        = 3 * Real.pi - 2 * Work.Smooth.SphereJordan.perPt τ from by field_simp; ring]
    push_cast
    ring
  · rw [Work.SphereJordan.toCplx_pair,
      show (1 / 2 + (Work.Smooth.SphereJordan.perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) / 2 : ℝ)
        = Work.Smooth.SphereJordan.perPt τ / Real.pi - 1 from by field_simp; ring]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring

theorem srcDnB_eq_neg {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (τ : ℝ) :
    Work.Smooth.SphereJordan.srcDnB S τ =
      -(Work.Smooth.SphereJordan.cutDir S * Work.SphereJordan.stdHalf τ) := by
  simp only [Work.Smooth.SphereJordan.srcDnB, Work.Smooth.SphereJordan.srcOuterDn,
    Work.Smooth.SphereJordan.srcInnerDn, Work.SphereJordan.stdHalf, Work.SphereJordan.stdVec,
    Complex.real_smul]
  split_ifs with h1 h2 h3
  · rw [Work.SphereJordan.toCplx_pair,
      show Real.pi * (Work.Smooth.SphereJordan.perPt τ / (Real.pi / 2))
        = 2 * Work.Smooth.SphereJordan.perPt τ from by field_simp]
    simp only [Complex.ofReal_one, one_mul]
    ring
  · rw [Work.SphereJordan.toCplx_pair, Complex.exp_pi_mul_I,
      show (1 - (Work.Smooth.SphereJordan.perPt τ - Real.pi / 2) / (Real.pi / 2) / 2 : ℝ)
        = 3 / 2 - Work.Smooth.SphereJordan.perPt τ / Real.pi from by field_simp; ring]
    push_cast
    ring
  · rw [Work.SphereJordan.toCplx_pair,
      show -(Real.pi * ((Work.Smooth.SphereJordan.perPt τ - Real.pi) / (Real.pi / 2)))
        = 2 * Real.pi - 2 * Work.Smooth.SphereJordan.perPt τ from by field_simp; ring]
    have h : Complex.exp (↑(2 * Real.pi - 2 * Work.Smooth.SphereJordan.perPt τ) * Complex.I)
        = -Complex.exp (↑(3 * Real.pi - 2 * Work.Smooth.SphereJordan.perPt τ) * Complex.I) := by
      rw [show ((2 * Real.pi - 2 * Work.Smooth.SphereJordan.perPt τ : ℝ) : ℂ) * Complex.I
          = ((3 * Real.pi - 2 * Work.Smooth.SphereJordan.perPt τ : ℝ) : ℂ) * Complex.I
            + (-(↑Real.pi * Complex.I)) by push_cast; ring]
      rw [Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
      ring
    rw [h]
    push_cast
    ring
  · rw [Work.SphereJordan.toCplx_pair,
      show (-(1 / 2) - (Work.Smooth.SphereJordan.perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) / 2 : ℝ)
        = -(Work.Smooth.SphereJordan.perPt τ / Real.pi - 1) from by field_simp; ring]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring

private theorem leg1 {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ Real.pi / 2) :
    bdVec (circlePoint σ) = (1, 2 * σ) := by
  have hsin : 0 ≤ (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [Real.pi_pos]⟩
  have hcos : 0 ≤ (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).re := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) h1
  have harc : Real.arcsin ((((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im
      / ‖(((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ)‖) = σ := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im,
      Complex.norm_exp_ofReal_mul_I, div_one]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) h1
  rw [bdVec, if_pos hsin, if_pos hcos, harc]

private theorem leg2 {σ : ℝ} (h1 : Real.pi / 2 < σ) (h2 : σ ≤ Real.pi) :
    bdVec (circlePoint σ) = (3 / 2 - σ / Real.pi, Real.pi) := by
  have hsin : 0 ≤ (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcos : (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).re < 0 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos])
  have harc : Real.arcsin ((((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im
      / ‖(((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ)‖) = Real.pi - σ := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im,
      Complex.norm_exp_ofReal_mul_I, div_one,
      show Real.sin σ = Real.sin (Real.pi - σ) from (Real.sin_pi_sub σ).symm]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)
  rw [bdVec, if_pos hsin, if_neg (not_le_of_gt hcos), harc]
  congr 1
  field_simp
  ring

private theorem leg3 {σ : ℝ} (h1 : Real.pi < σ) (h2 : σ < 3 * Real.pi / 2) :
    bdVec (circlePoint σ) = (1 / 2, 3 * Real.pi - 2 * σ) := by
  have hsin : (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im < 0 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im,
      ← Real.sin_sub_two_pi σ]
    exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have hcos : (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).re < 0 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have harc : Real.arcsin (-(((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im
      / ‖(((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ)‖) = σ - Real.pi := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im,
      Complex.norm_exp_ofReal_mul_I, div_one]
    rw [show -Real.sin σ = Real.sin (σ - Real.pi) from by rw [Real.sin_sub_pi]]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)
  rw [bdVec, if_neg (not_le_of_gt hsin), if_neg (not_le_of_gt hcos), harc]
  congr 1
  ring

private theorem leg4 {σ : ℝ} (h1 : 3 * Real.pi / 2 ≤ σ) (h2 : σ < 2 * Real.pi) :
    bdVec (circlePoint σ) = (σ / Real.pi - 1, 0) := by
  have hsin : (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im < 0 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im,
      ← Real.sin_sub_two_pi σ]
    exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have hcos : 0 ≤ (((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).re := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_re,
      ← Real.cos_sub_two_pi σ]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have harc : Real.arcsin (-(((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ).im
      / ‖(((circlePoint σ : Work.Smooth.Jordan.Disc)) : ℂ)‖) = 2 * Real.pi - σ := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I_im,
      Complex.norm_exp_ofReal_mul_I, div_one]
    rw [show -Real.sin σ = Real.sin (2 * Real.pi - σ) from by rw [Real.sin_two_pi_sub]]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)
  rw [bdVec, if_neg (not_le_of_gt hsin), if_pos hcos, harc]
  congr 1
  field_simp
  ring


theorem stdVec_leg1 {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ Real.pi / 2) : stdVec σ = (1, 2 * σ) := by
  rw [stdVec, perPt_eq_self h0 (by linarith [Real.pi_pos]), if_pos h1]

theorem stdVec_leg2 {σ : ℝ} (h1 : Real.pi / 2 < σ) (h2 : σ ≤ Real.pi) :
    stdVec σ = (3 / 2 - σ / Real.pi, Real.pi) := by
  rw [stdVec, perPt_eq_self (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
    if_neg (not_le.mpr h1), if_pos h2]

theorem stdVec_leg3 {σ : ℝ} (h1 : Real.pi < σ) (h2 : σ ≤ 3 * Real.pi / 2) :
    stdVec σ = (1 / 2, 3 * Real.pi - 2 * σ) := by
  rw [stdVec, perPt_eq_self (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
    if_neg (not_le.mpr (by linarith [Real.pi_pos] : Real.pi / 2 < σ)),
    if_neg (not_le.mpr h1), if_pos h2]

theorem stdVec_leg4 {σ : ℝ} (h1 : 3 * Real.pi / 2 < σ) (h2 : σ < 2 * Real.pi) :
    stdVec σ = (σ / Real.pi - 1, 0) := by
  rw [stdVec, perPt_eq_self (by linarith [Real.pi_pos]) h2,
    if_neg (not_le.mpr (by linarith [Real.pi_pos] : Real.pi / 2 < σ)),
    if_neg (not_le.mpr (by linarith [Real.pi_pos] : Real.pi < σ)),
    if_neg (not_le.mpr h1)]

private theorem leg4_3pi2_helper :
    bdVec (circlePoint (3 * Real.pi / 2)) = (1 / 2, 0) := by
  have h := leg4 (σ := 3 * Real.pi / 2) le_rfl (by linarith [Real.pi_pos])
  rw [h]
  congr 1
  field_simp
  ring

theorem stdVec_3pi2 : stdVec (3 * Real.pi / 2) = (1 / 2, 0) := by
  rw [stdVec, perPt_eq_self (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
    if_neg (not_le.mpr (by linarith [Real.pi_pos] : Real.pi / 2 < 3 * Real.pi / 2)),
    if_neg (not_le.mpr (by linarith [Real.pi_pos] : Real.pi < 3 * Real.pi / 2)),
    if_pos le_rfl]
  congr 1
  ring

theorem bdVec_circlePoint_aux {σ : ℝ} (h0 : 0 ≤ σ) (h2 : σ < 2 * Real.pi) :
    bdVec (circlePoint σ) = stdVec σ := by
  rcases le_or_gt σ (Real.pi / 2) with hc | hc
  · rw [stdVec_leg1 h0 hc]; exact leg1 h0 hc
  · rcases le_or_gt σ Real.pi with hc2 | hc2
    · rw [stdVec_leg2 hc hc2]; exact leg2 hc hc2
    · rcases lt_trichotomy σ (3 * Real.pi / 2) with hc3 | hc3 | hc3
      · rw [stdVec_leg3 hc2 hc3.le]; exact leg3 hc2 hc3
      · rw [hc3, stdVec_3pi2]; exact leg4_3pi2_helper
      · rw [stdVec_leg4 hc3 h2]; exact leg4 hc3.le h2

theorem bdVec_circlePoint (τ : ℝ) : bdVec (circlePoint τ) = stdVec τ := by
  have hmem := perPt_mem_Ico τ
  have hper : perPt (perPt τ) = perPt τ := perPt_eq_self hmem.1 hmem.2
  have hstd : stdVec (perPt τ) = stdVec τ := by
    rw [stdVec, stdVec, hper]
  rw [← perPt_circlePoint τ, bdVec_circlePoint_aux hmem.1 hmem.2, hstd]

theorem stdVec_surj {p : ℝ × ℝ} (hp : p ∈ upRectBd) : ∃ τ : ℝ, stdVec τ = p := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨h1a, h1b, h1c, h1d⟩ := hp1
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rcases hp2 with h | h | h | h
  · rcases eq_or_lt_of_le h1d with h2 | h2
    · refine ⟨Real.pi, ?_⟩
      rw [stdVec_leg2 (by linarith [Real.pi_pos]) le_rfl]
      have e1 : (3 / 2 - Real.pi / Real.pi) = p.1 := by rw [h]; field_simp; norm_num
      rw [e1, h2.symm]
    · refine ⟨Real.pi + (Real.pi - p.2) / 2, ?_⟩
      have hlt : Real.pi < Real.pi + (Real.pi - p.2) / 2 := by linarith
      have hle : Real.pi + (Real.pi - p.2) / 2 ≤ 3 * Real.pi / 2 := by linarith
      rw [stdVec_leg3 hlt hle]
      have e2 : 3 * Real.pi - 2 * (Real.pi + (Real.pi - p.2) / 2) = p.2 := by ring
      rw [h.symm, e2]
  · refine ⟨p.2 / 2, ?_⟩
    have h0 : 0 ≤ p.2 / 2 := by linarith
    have hle : p.2 / 2 ≤ Real.pi / 2 := by linarith
    rw [stdVec_leg1 h0 hle]
    have e2 : 2 * (p.2 / 2) = p.2 := by ring
    rw [h.symm, e2]
  · rcases eq_or_lt_of_le h1b with h1eq | h1lt
    · refine ⟨0, ?_⟩
      rw [stdVec_leg1 le_rfl (by linarith [Real.pi_pos])]
      have e2 : 2 * (0:ℝ) = p.2 := by rw [h]; ring
      rw [h1eq.symm, e2]
    · rcases eq_or_lt_of_le h1a with h1eq | h1gt
      · refine ⟨3 * Real.pi / 2, ?_⟩
        rw [stdVec_3pi2]
        have hp' : p = (1 / 2, 0) := by
          ext
          · rw [← h1eq]
          · rw [← h]
        rw [hp']
      · refine ⟨Real.pi * (p.1 + 1), ?_⟩
        have hlt : 3 * Real.pi / 2 < Real.pi * (p.1 + 1) := by
          have : Real.pi * (3 / 2) < Real.pi * (p.1 + 1) :=
            mul_lt_mul_of_pos_left (by linarith) hpi
          linarith
        have hle : Real.pi * (p.1 + 1) < 2 * Real.pi := by
          have : Real.pi * (p.1 + 1) < Real.pi * 2 :=
            mul_lt_mul_of_pos_left (by linarith) hpi
          linarith
        rw [stdVec_leg4 hlt hle]
        have e1 : Real.pi * (p.1 + 1) / Real.pi - 1 = p.1 := by field_simp; ring
        rw [e1, h.symm]
  · rcases eq_or_lt_of_le h1b with h1eq | h1lt
    · refine ⟨Real.pi / 2, ?_⟩
      rw [stdVec_leg1 (by linarith [Real.pi_pos]) le_rfl]
      have e2 : 2 * (Real.pi / 2) = p.2 := by rw [h]; ring
      rw [h1eq.symm, e2]
    · refine ⟨Real.pi * (3 / 2 - p.1), ?_⟩
      have hlt : Real.pi / 2 < Real.pi * (3 / 2 - p.1) := by
        have : Real.pi * (1 / 2) < Real.pi * (3 / 2 - p.1) :=
          mul_lt_mul_of_pos_left (by linarith) hpi
        linarith
      have hle : Real.pi * (3 / 2 - p.1) ≤ Real.pi := by
        have : Real.pi * (3 / 2 - p.1) ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hpi.le
        linarith
      rw [stdVec_leg2 hlt hle]
      have e1 : 3 / 2 - Real.pi * (3 / 2 - p.1) / Real.pi = p.1 := by field_simp; ring
      rw [e1, h.symm]

theorem bdVec_surj {p : ℝ × ℝ} (hp : p ∈ upRectBd) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ bdVec z = p := by
  obtain ⟨τ, hτ⟩ := stdVec_surj hp
  exact ⟨circlePoint τ, Work.Smooth.SphereJordan.norm_circlePoint_plain τ,
    by rw [bdVec_circlePoint, hτ]⟩




theorem radVec_surj {q : ℝ × ℝ} (hq : q ∈ upRect) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ radVec z = q := by
  obtain ⟨h1a, h1b, h1c, h1d⟩ := hq
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  by_cases hc : q = ctrUp
  · refine ⟨0, by norm_num, ?_⟩
    rw [radVec, norm_zero, segVec_zero, hc]
  · set s : ℝ := max (|q.1 - 3 / 4| / (1 / 4)) (|q.2 - Real.pi / 2| / (Real.pi / 2)) with hsdef
    have hαle : |q.1 - 3 / 4| / (1 / 4) ≤ s := by rw [hsdef]; exact le_max_left _ _
    have hβle : |q.2 - Real.pi / 2| / (Real.pi / 2) ≤ s := by rw [hsdef]; exact le_max_right _ _
    have hαnn : 0 ≤ |q.1 - 3 / 4| / (1 / 4) := div_nonneg (abs_nonneg _) (by norm_num)
    have hβnn : 0 ≤ |q.2 - Real.pi / 2| / (Real.pi / 2) :=
      div_nonneg (abs_nonneg _) (by linarith : (0:ℝ) ≤ Real.pi / 2)
    have hαb : |q.1 - 3 / 4| / (1 / 4) ≤ 1 := by
      rw [div_le_one (by norm_num), abs_le]
      exact ⟨by linarith, by linarith⟩
    have hβb : |q.2 - Real.pi / 2| / (Real.pi / 2) ≤ 1 := by
      rw [div_le_one (by linarith), abs_le]
      exact ⟨by linarith, by linarith⟩
    have hs1 : s ≤ 1 := by rw [hsdef]; exact max_le hαb hβb
    have hsnonneg : 0 ≤ s := le_trans hαnn hαle
    have hb1 : |q.1 - 3 / 4| ≤ s * (1 / 4) := by
      have h := hαle
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 4)] at h
      exact h
    have hb2 : |q.2 - Real.pi / 2| ≤ s * (Real.pi / 2) := by
      have h := hβle
      rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi / 2)] at h
      exact h
    have hs0 : 0 < s := by
      refine lt_of_le_of_ne hsnonneg ?_
      intro h0
      have hα0 : |q.1 - 3 / 4| / (1 / 4) = 0 := le_antisymm (by simpa [h0.symm] using hαle) hαnn
      have hβ0 : |q.2 - Real.pi / 2| / (Real.pi / 2) = 0 :=
        le_antisymm (by simpa [h0.symm] using hβle) hβnn
      have e1 : q.1 = 3 / 4 := by
        have := (div_eq_zero_iff.mp hα0).resolve_right (by norm_num)
        exact sub_eq_zero.mp (abs_eq_zero.mp this)
      have e2 : q.2 = Real.pi / 2 := by
        have := (div_eq_zero_iff.mp hβ0).resolve_right (ne_of_gt (by linarith : (0:ℝ) < Real.pi / 2))
        exact sub_eq_zero.mp (abs_eq_zero.mp this)
      exact hc (by ext <;> simp [ctrUp, e1, e2])
    have hp1 : (ctrUp + s⁻¹ • (q - ctrUp)).1 = 3 / 4 + s⁻¹ * (q.1 - 3 / 4) := by
      simp [ctrUp, smul_eq_mul]
    have hp2 : (ctrUp + s⁻¹ • (q - ctrUp)).2 = Real.pi / 2 + s⁻¹ * (q.2 - Real.pi / 2) := by
      simp [ctrUp, smul_eq_mul]
    have hc1 : |s⁻¹ * (q.1 - 3 / 4)| ≤ 1 / 4 := by
      rw [abs_mul, abs_inv, abs_of_pos hs0]
      calc s⁻¹ * |q.1 - 3 / 4| ≤ s⁻¹ * (s * (1 / 4)) :=
            mul_le_mul_of_nonneg_left hb1 (inv_nonneg.mpr hs0.le)
        _ = 1 / 4 := by field_simp
    have hc2 : |s⁻¹ * (q.2 - Real.pi / 2)| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_inv, abs_of_pos hs0]
      calc s⁻¹ * |q.2 - Real.pi / 2| ≤ s⁻¹ * (s * (Real.pi / 2)) :=
            mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hs0.le)
        _ = Real.pi / 2 := by field_simp
    have hpmem : ctrUp + s⁻¹ • (q - ctrUp) ∈ upRectBd := by
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hp1]; linarith [(abs_le.mp hc1).1]
      · rw [hp1]; linarith [(abs_le.mp hc1).2]
      · rw [hp2]; linarith [(abs_le.mp hc2).1]
      · rw [hp2]; linarith [(abs_le.mp hc2).2]
      · rcases max_choice (|q.1 - 3 / 4| / (1 / 4)) (|q.2 - Real.pi / 2| / (Real.pi / 2)) with h' | h'
        · have hs_eq : s = |q.1 - 3 / 4| / (1 / 4) := by rw [hsdef]; exact h'
          have hb1' : |q.1 - 3 / 4| = s * (1 / 4) := by
            rw [hs_eq]; field_simp
          have habs : |s⁻¹ * (q.1 - 3 / 4)| = 1 / 4 := by
            rw [abs_mul, abs_inv, abs_of_pos hs0, hb1']
            field_simp
          rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1 / 4)).mp habs with hv | hv
          · right; left; rw [hp1, hv]; norm_num
          · left; rw [hp1, hv]; norm_num
        · have hs_eq : s = |q.2 - Real.pi / 2| / (Real.pi / 2) := by rw [hsdef]; exact h'
          have hb2' : |q.2 - Real.pi / 2| = s * (Real.pi / 2) := by
            rw [hs_eq]; field_simp
          have habs : |s⁻¹ * (q.2 - Real.pi / 2)| = Real.pi / 2 := by
            rw [abs_mul, abs_inv, abs_of_pos hs0, hb2']
            field_simp
          rcases (abs_eq (by linarith : (0:ℝ) ≤ Real.pi / 2)).mp habs with hv | hv
          · right; right; right; rw [hp2, hv]; ring
          · right; right; left; rw [hp2, hv]; ring
    obtain ⟨z₀, hz₀⟩ := bdVec_surj hpmem
    refine ⟨s • z₀, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hz₀.1, mul_one]
      exact hs1
    · have hn : ‖s • z₀‖ = s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hz₀.1, mul_one]
      rw [radVec, bdVec_smul_pos z₀ hs0, hn, hz₀.2, segVec]
      show ctrUp + s • (ctrUp + s⁻¹ • (q - ctrUp) - ctrUp) = q
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, add_sub_cancel]



theorem segVec_notBd {p : ℝ × ℝ} (hp : p ∈ upRect) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    segVec p t ∉ upRectBd := by
  intro hcon
  obtain ⟨hq, hdisj⟩ := hcon
  obtain ⟨hq1a, hq1b, hq2a, hq2b⟩ := hq
  obtain ⟨hp1a, hp1b, hp2a, hp2b⟩ := hp
  have e1 : (segVec p t).1 = 3 / 4 + t * (p.1 - 3 / 4) := by simp [segVec, ctrUp, smul_eq_mul]
  have e2 : (segVec p t).2 = Real.pi / 2 + t * (p.2 - Real.pi / 2) := by
    simp [segVec, ctrUp, smul_eq_mul]
  rcases hdisj with h | h | h | h
  · rw [e1] at h; nlinarith [ht0, ht1, hp1a]
  · rw [e1] at h; nlinarith [ht0, ht1, hp1b]
  · rw [e2] at h; nlinarith [ht0, ht1, hp2a, Real.pi_pos]
  · rw [e2] at h; nlinarith [ht0, ht1, hp2b, Real.pi_pos]

theorem ctrUp_notBd : ctrUp ∉ upRectBd := by
  intro hcon
  obtain ⟨-, hdisj⟩ := hcon
  rcases hdisj with h | h | h | h <;> simp only [ctrUp] at h <;> linarith [Real.pi_pos]

theorem norm_bdVec_sub_ctr_ne_zero {z : ℂ} (h : bdVec z = ctrUp) : False :=
  ctrUp_notBd (h ▸ bdVec_mem_upRectBd z)

theorem radVec_injOn : Set.InjOn radVec (Metric.closedBall (0:ℂ) 1) := by
  intro z hz z' hz' h
  have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hz'le : ‖z'‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hvec : ‖z‖ • (bdVec z - ctrUp) = ‖z'‖ • (bdVec z' - ctrUp) := by
    have hh := h
    rw [radVec, radVec, segVec, segVec] at hh
    exact add_left_cancel hh
  rcases eq_or_ne ‖z‖ 0 with hz0 | hz0
  · have ez : z = 0 := norm_eq_zero.mp hz0
    subst ez
    rw [norm_zero, zero_smul] at hvec
    rcases eq_or_ne ‖z'‖ 0 with hz'0 | hz'0
    · exact (norm_eq_zero.mp hz'0).symm
    · exact absurd (sub_eq_zero.mp ((smul_eq_zero.mp hvec.symm).resolve_left hz'0)) (norm_bdVec_sub_ctr_ne_zero (z := z'))
  · rcases eq_or_ne ‖z'‖ 0 with hz'0 | hz'0
    · have ez : z' = 0 := norm_eq_zero.mp hz'0
      subst ez
      rw [norm_zero, zero_smul] at hvec
      exact absurd (sub_eq_zero.mp ((smul_eq_zero.mp hvec).resolve_left hz0)) (norm_bdVec_sub_ctr_ne_zero (z := z))
    · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
      have hz'p : 0 < ‖z'‖ := lt_of_le_of_ne (norm_nonneg z') (Ne.symm hz'0)
      have hzm : z ≠ 0 := norm_pos_iff.mp hzp
      have hz'm : z' ≠ 0 := norm_pos_iff.mp hz'p
      have hp : bdVec z - ctrUp = (‖z‖⁻¹ * ‖z'‖) • (bdVec z' - ctrUp) := by
        have hh := congrArg (fun v : ℝ × ℝ => ‖z‖⁻¹ • v) hvec
        simpa [smul_smul, inv_mul_cancel₀ hz0] using hh
      have hl0 : 0 < ‖z‖⁻¹ * ‖z'‖ := mul_pos (inv_pos.mpr hzp) hz'p
      rcases lt_trichotomy (‖z‖⁻¹ * ‖z'‖) 1 with hl | hl | hl
      · exfalso
        have heq : bdVec z = segVec (bdVec z') (‖z‖⁻¹ * ‖z'‖) := by
          rw [segVec, ← hp]; abel
        exact segVec_notBd (bdVec_mem_upRectBd z').1 hl0 hl (heq ▸ bdVec_mem_upRectBd z)
      · have hbd : bdVec z = bdVec z' := by
          have h1 : bdVec z - ctrUp = bdVec z' - ctrUp := by rw [hp, hl, one_smul]
          have h2 := congrArg (fun v : ℝ × ℝ => v + ctrUp) h1
          simpa using h2
        obtain ⟨c, hc0, hcz⟩ := bdVec_eq_imp_smul z z' hzm hz'm hbd
        have hcn : c = 1 := by
          have h1 : ‖z'‖ = c * ‖z‖ := by
            rw [hcz, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
          have h2 : ‖z'‖ = ‖z‖ := by
            have h3 : ‖z‖⁻¹ * ‖z'‖ = 1 := hl
            field_simp at h3
            linarith
          have : c * ‖z‖ = 1 * ‖z‖ := by rw [← h1, h2, one_mul]
          exact mul_right_cancel₀ hzp.ne' this
        rw [hcn, one_smul] at hcz
        exact hcz.symm
      · exfalso
        have hinv : (‖z‖⁻¹ * ‖z'‖)⁻¹ < 1 := by
          have hA0 : 0 < ‖z‖⁻¹ * ‖z'‖ := hl0
          have hA1 : 1 < ‖z‖⁻¹ * ‖z'‖ := hl
          have hmul : ‖z‖⁻¹ * ‖z'‖ * (‖z‖⁻¹ * ‖z'‖)⁻¹ = 1 := mul_inv_cancel₀ hA0.ne'
          nlinarith [inv_pos.mpr hA0]
        have hinv0 : 0 < (‖z‖⁻¹ * ‖z'‖)⁻¹ := inv_pos.mpr hl0
        have heq : bdVec z' = segVec (bdVec z) ((‖z‖⁻¹ * ‖z'‖)⁻¹) := by
          rw [segVec]
          have hthis : bdVec z' - ctrUp = (‖z‖⁻¹ * ‖z'‖)⁻¹ • (bdVec z - ctrUp) := by
            have hh : (‖z‖⁻¹ * ‖z'‖)⁻¹ • (bdVec z - ctrUp) = bdVec z' - ctrUp := by
              rw [hp, smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
            exact hh.symm
          rw [← hthis]; abel
        exact segVec_notBd (bdVec_mem_upRectBd z).1 hinv0 hinv (heq ▸ bdVec_mem_upRectBd z')


/-! ## Continuity of the interpolated map -/

def bd1 (z : ℂ) : ℝ × ℝ := ((1 : ℝ), 2 * Real.arcsin (z.im / ‖z‖))
def bd2 (z : ℂ) : ℝ × ℝ := (1 / 2 + Real.arcsin (z.im / ‖z‖) / Real.pi, Real.pi)
def bd3 (z : ℂ) : ℝ × ℝ := (1 - Real.arcsin (-z.im / ‖z‖) / Real.pi, 0)
def bd4 (z : ℂ) : ℝ × ℝ := (1 / 2, Real.pi - 2 * Real.arcsin (-z.im / ‖z‖))

def radW (b : ℂ → ℝ × ℝ) : ℂ → ℝ × ℝ := fun z => ctrUp + ‖z‖ • (b z - ctrUp)

theorem continuousOn_bd1 : ContinuousOn bd1 {z : ℂ | z ≠ 0} := by
  have hf : ContinuousOn (fun z : ℂ => z.im / ‖z‖) {z : ℂ | z ≠ 0} :=
    Complex.continuous_im.continuousOn.div continuous_norm.continuousOn
      (fun z hz => norm_ne_zero_iff.mpr hz)
  have h2 : ContinuousOn (fun z : ℂ => 2 * Real.arcsin (z.im / ‖z‖)) {z : ℂ | z ≠ 0} :=
    ((Real.continuous_arcsin.const_mul 2).continuousOn).comp hf (Set.mapsTo_univ _ _)
  exact continuousOn_const.prodMk h2

theorem continuousOn_bd2 : ContinuousOn bd2 {z : ℂ | z ≠ 0} := by
  have hf : ContinuousOn (fun z : ℂ => z.im / ‖z‖) {z : ℂ | z ≠ 0} :=
    Complex.continuous_im.continuousOn.div continuous_norm.continuousOn
      (fun z hz => norm_ne_zero_iff.mpr hz)
  have h2 : ContinuousOn (fun z : ℂ => Real.arcsin (z.im / ‖z‖) / Real.pi) {z : ℂ | z ≠ 0} :=
    (Real.continuous_arcsin.continuousOn.div_const Real.pi).comp hf (Set.mapsTo_univ _ _)
  exact (continuousOn_const.add h2).prodMk continuousOn_const

theorem continuousOn_bd3 : ContinuousOn bd3 {z : ℂ | z ≠ 0} := by
  have hf : ContinuousOn (fun z : ℂ => -z.im / ‖z‖) {z : ℂ | z ≠ 0} :=
    (continuous_neg.comp_continuousOn Complex.continuous_im.continuousOn).div
      continuous_norm.continuousOn (fun z hz => norm_ne_zero_iff.mpr hz)
  have h2 : ContinuousOn (fun z : ℂ => Real.arcsin (-z.im / ‖z‖) / Real.pi) {z : ℂ | z ≠ 0} :=
    (Real.continuous_arcsin.continuousOn.div_const Real.pi).comp hf (Set.mapsTo_univ _ _)
  exact (continuousOn_const.sub h2).prodMk continuousOn_const

theorem continuousOn_bd4 : ContinuousOn bd4 {z : ℂ | z ≠ 0} := by
  have hf : ContinuousOn (fun z : ℂ => -z.im / ‖z‖) {z : ℂ | z ≠ 0} :=
    (continuous_neg.comp_continuousOn Complex.continuous_im.continuousOn).div
      continuous_norm.continuousOn (fun z hz => norm_ne_zero_iff.mpr hz)
  have h2 : ContinuousOn (fun z : ℂ => 2 * Real.arcsin (-z.im / ‖z‖)) {z : ℂ | z ≠ 0} :=
    ((Real.continuous_arcsin.const_mul 2).continuousOn).comp hf (Set.mapsTo_univ _ _)
  exact continuousOn_const.prodMk (continuousOn_const.sub h2)

theorem norm_bd1_le (z : ℂ) : ‖bd1 z‖ ≤ 2 * Real.pi + 1 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have h2 : ‖(2 * Real.arcsin (z.im / ‖z‖) : ℝ)‖ ≤ Real.pi := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := abs_le.mpr (Real.arcsin_mem_Icc (z.im / ‖z‖))
    linarith
  rw [bd1, Prod.norm_def]
  dsimp only
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_one]; linarith [Real.pi_pos]
  · linarith [h2, Real.pi_pos]

theorem norm_bd2_le (z : ℂ) : ‖bd2 z‖ ≤ 2 * Real.pi + 1 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hb : |Real.arcsin (z.im / ‖z‖) / Real.pi| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
    have := abs_le.mpr (Real.arcsin_mem_Icc (z.im / ‖z‖))
    linarith
  have hb1 : Real.arcsin (z.im / ‖z‖) / Real.pi ≤ 1 / 2 := (le_abs_self _).trans hb
  have hb2 : -(1 / 2) ≤ Real.arcsin (z.im / ‖z‖) / Real.pi :=
    (neg_le_neg hb).trans (neg_abs_le _)
  have h1 : ‖(1 / 2 + Real.arcsin (z.im / ‖z‖) / Real.pi : ℝ)‖ ≤ 2 * Real.pi + 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [Real.pi_pos], by linarith [hb1, Real.pi_pos]⟩
  rw [bd2, Prod.norm_def]
  dsimp only
  refine max_le ?_ ?_
  · exact h1
  · rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]; linarith

theorem norm_bd3_le (z : ℂ) : ‖bd3 z‖ ≤ 2 * Real.pi + 1 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hb : |Real.arcsin (-z.im / ‖z‖) / Real.pi| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
    have := abs_le.mpr (Real.arcsin_mem_Icc (-z.im / ‖z‖))
    linarith
  have hb1 : Real.arcsin (-z.im / ‖z‖) / Real.pi ≤ 1 / 2 := (le_abs_self _).trans hb
  have hb2 : -(1 / 2) ≤ Real.arcsin (-z.im / ‖z‖) / Real.pi :=
    (neg_le_neg hb).trans (neg_abs_le _)
  have h1 : ‖(1 - Real.arcsin (-z.im / ‖z‖) / Real.pi : ℝ)‖ ≤ 2 * Real.pi + 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hb1, Real.pi_pos], by linarith [hb2, Real.pi_pos]⟩
  rw [bd3, Prod.norm_def]
  dsimp only
  refine max_le ?_ ?_
  · exact h1
  · rw [Real.norm_eq_abs, abs_zero]; linarith [Real.pi_pos]

theorem norm_bd4_le (z : ℂ) : ‖bd4 z‖ ≤ 2 * Real.pi + 1 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have h2 : ‖(2 * Real.arcsin (-z.im / ‖z‖) : ℝ)‖ ≤ Real.pi := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := abs_le.mpr (Real.arcsin_mem_Icc (-z.im / ‖z‖))
    linarith
  have h1 : ‖(Real.pi - 2 * Real.arcsin (-z.im / ‖z‖) : ℝ)‖ ≤ 2 * Real.pi + 1 := by
    have hb := h2
    rw [Real.norm_eq_abs] at hb ⊢
    rw [abs_le] at hb ⊢
    exact ⟨by linarith [hb.2, Real.pi_pos], by linarith [hb.1, Real.pi_pos]⟩
  rw [bd4, Prod.norm_def]
  dsimp only
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]; linarith [Real.pi_pos]
  · exact h1



theorem continuous_radW {b : ℂ → ℝ × ℝ} (hb : ContinuousOn b {z : ℂ | z ≠ 0})
    {C : ℝ} (hbdd : ∀ z : ℂ, ‖b z‖ ≤ C) :
    Continuous (fun z : ℂ => ctrUp + ‖z‖ • (b z - ctrUp)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rcases eq_or_ne z₀ 0 with h | h
  · subst h
    have hC1 : 0 < C + ‖ctrUp‖ + 1 := by
      have := le_trans (norm_nonneg (b 0)) (hbdd 0)
      have := norm_nonneg ctrUp
      linarith
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / (C + ‖ctrUp‖ + 1), by positivity,
      fun z hz => ?_⟩
    have hb' : ‖b z - ctrUp‖ ≤ C + ‖ctrUp‖ := by
      calc ‖b z - ctrUp‖ ≤ ‖b z‖ + ‖ctrUp‖ := norm_sub_le _ _
        _ ≤ C + ‖ctrUp‖ := by linarith [hbdd z]
    rw [dist_eq_norm] at hz
    have h2 : ‖z‖ * (C + ‖ctrUp‖ + 1) < ε := by
      rw [lt_div_iff₀ hC1] at hz
      simpa using hz
    simp only [norm_zero, zero_smul, add_zero]
    rw [dist_eq_norm, show ctrUp + ‖z‖ • (b z - ctrUp) - ctrUp = ‖z‖ • (b z - ctrUp) from by
      abel, norm_smul, Real.norm_of_nonneg (norm_nonneg z)]
    have h4 : ‖z‖ * (C + ‖ctrUp‖) ≤ ‖z‖ * (C + ‖ctrUp‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg z)
    calc ‖z‖ * ‖b z - ctrUp‖ ≤ ‖z‖ * (C + ‖ctrUp‖) :=
          mul_le_mul_of_nonneg_left hb' (norm_nonneg z)
      _ ≤ ‖z‖ * (C + ‖ctrUp‖ + 1) := h4
      _ < ε := h2
  · have hbcont : ContinuousAt b z₀ := hb.continuousAt (isOpen_ne.mem_nhds h)
    have hnorm : ContinuousAt (fun z : ℂ => ‖z‖) z₀ := continuous_norm.continuousAt
    exact continuousAt_const.add (hnorm.smul (hbcont.sub continuousAt_const))

theorem radVec_eq_radW1 {z : ℂ} (hz : 0 ≤ z.im) (hz' : 0 ≤ z.re) : radVec z = radW bd1 z := by
  simp only [radVec, radW, segVec, bdVec, bd1, if_pos hz, if_pos hz']

theorem radVec_eq_radW2 {z : ℂ} (hz : 0 ≤ z.im) (hz' : z.re < 0) : radVec z = radW bd2 z := by
  simp only [radVec, radW, segVec, bdVec, bd2, if_pos hz, if_neg (not_le_of_gt hz')]

theorem radVec_eq_radW3 {z : ℂ} (hz : z.im < 0) (hz' : 0 ≤ z.re) : radVec z = radW bd3 z := by
  simp only [radVec, radW, segVec, bdVec, bd3, if_neg (not_le_of_gt hz), if_pos hz']

theorem radVec_eq_radW4 {z : ℂ} (hz : z.im < 0) (hz' : z.re < 0) : radVec z = radW bd4 z := by
  simp only [radVec, radW, segVec, bdVec, bd4, if_neg (not_le_of_gt hz), if_neg (not_le_of_gt hz')]

theorem radW_bd1_eq_bd2 {z : ℂ} (hre : z.re = 0) (him : 0 ≤ z.im) : radW bd1 z = radW bd2 z := by
  rcases eq_or_ne z 0 with h | h
  · subst h; simp [radW]
  · have himpos : 0 < z.im := lt_of_le_of_ne him (by
      intro h0
      exact h (Complex.ext (by simp [hre]) (by simp [h0])))
    have hnorm : ‖z‖ = z.im := by
      have h2 : ‖z‖ ^ 2 = z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre]; ring
      nlinarith [norm_nonneg z, him]
    have hdiv : z.im / ‖z‖ = 1 := by rw [hnorm, div_self himpos.ne']
    have hA : (2:ℝ) * Real.arcsin (z.im / ‖z‖) = Real.pi := by rw [hdiv, Real.arcsin_one]; ring
    have hB : (1:ℝ) / 2 + Real.arcsin (z.im / ‖z‖) / Real.pi = 1 := by
      rw [hdiv, Real.arcsin_one]; field_simp; norm_num
    simp only [radW, bd1, bd2, hA, hB]

theorem radW_bd3_eq_bd4 {z : ℂ} (hre : z.re = 0) (him : z.im ≤ 0) : radW bd3 z = radW bd4 z := by
  rcases eq_or_ne z 0 with h | h
  · subst h; simp [radW]
  · have himneg : z.im < 0 := lt_of_le_of_ne him (by
      intro h0
      exact h (Complex.ext (by simp [hre]) (by simp [h0])))
    have hnorm : ‖z‖ = -z.im := by
      have h2 : ‖z‖ ^ 2 = z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre]; ring
      nlinarith [norm_nonneg z, him]
    have hdiv : -z.im / ‖z‖ = 1 := by rw [hnorm, div_self (neg_pos.mpr himneg).ne']
    have hA : (1:ℝ) - Real.arcsin (-z.im / ‖z‖) / Real.pi = 1 / 2 := by
      rw [hdiv, Real.arcsin_one]; field_simp; norm_num
    have hB : Real.pi - 2 * Real.arcsin (-z.im / ‖z‖) = 0 := by
      rw [hdiv, Real.arcsin_one]; ring
    simp only [radW, bd3, bd4, hA, hB]

theorem radW_bd1_eq_bd3 {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : radW bd1 z = radW bd3 z := by
  simp only [radW, bd1, bd3, him, neg_zero, zero_div, Real.arcsin_zero, mul_zero]
  norm_num

theorem radW_bd2_eq_bd4 {z : ℂ} (him : z.im = 0) (hre : z.re ≤ 0) : radW bd2 z = radW bd4 z := by
  simp only [radW, bd2, bd4, him, neg_zero, zero_div, Real.arcsin_zero, mul_zero]
  norm_num

theorem radVec_eq_radW_congr {z : ℂ} (hz : 0 ≤ z.im ∧ 0 ≤ z.re) : radVec z = radW bd1 z :=
  radVec_eq_radW1 hz.1 hz.2



theorem radW_bd2_eq_bd4' {z : ℂ} (him : z.im = 0) (hre : z.re ≤ 0) : radW bd2 z = radW bd4 z :=
  radW_bd2_eq_bd4 him hre

theorem radW_bd1_eq_bd3' {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : radW bd1 z = radW bd3 z :=
  radW_bd1_eq_bd3 him hre

theorem continuous_radVec : Continuous radVec := by
  have hQ1 : IsClosed {z : ℂ | 0 ≤ z.im ∧ 0 ≤ z.re} :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hQ2 : IsClosed {z : ℂ | 0 ≤ z.im ∧ z.re ≤ 0} :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hQ3 : IsClosed {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} :=
    (isClosed_le Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hQ4 : IsClosed {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} :=
    (isClosed_le Complex.continuous_im continuous_const).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have h1 : ContinuousOn radVec {z : ℂ | 0 ≤ z.im ∧ 0 ≤ z.re} :=
    ((continuous_radW continuousOn_bd1 norm_bd1_le).continuousOn).congr
      (fun z hz => radVec_eq_radW1 hz.1 hz.2)
  have h2 : ContinuousOn radVec {z : ℂ | 0 ≤ z.im ∧ z.re ≤ 0} :=
    ((continuous_radW continuousOn_bd2 norm_bd2_le).continuousOn).congr (fun z hz => by
      rcases lt_or_eq_of_le hz.2 with h | h
      · exact radVec_eq_radW2 hz.1 h
      · exact (radVec_eq_radW1 hz.1 (le_of_eq h.symm)).trans (radW_bd1_eq_bd2 h hz.1))
  have h3 : ContinuousOn radVec {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} :=
    ((continuous_radW continuousOn_bd3 norm_bd3_le).continuousOn).congr (fun z hz => by
      rcases lt_or_eq_of_le hz.1 with h | h
      · exact radVec_eq_radW3 h hz.2
      · exact (radVec_eq_radW1 (le_of_eq h.symm) hz.2).trans (radW_bd1_eq_bd3 h hz.2))
  have h4 : ContinuousOn radVec {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} :=
    ((continuous_radW continuousOn_bd4 norm_bd4_le).continuousOn).congr (fun z hz => by
      rcases lt_or_eq_of_le hz.1 with him | him <;> rcases lt_or_eq_of_le hz.2 with hre | hre
      · exact radVec_eq_radW4 him hre
      · exact (radVec_eq_radW3 him (le_of_eq hre.symm)).trans (radW_bd3_eq_bd4 hre him.le)
      · exact (radVec_eq_radW2 (le_of_eq him.symm) hre).trans (radW_bd2_eq_bd4 him hre.le)
      · rw [show z = 0 from Complex.ext (by simpa using hre) (by simpa using him)]
        simp [radVec, radW, segVec_zero])
  have h12 := h1.union_of_isClosed h2 hQ1 hQ2
  have h34 := h3.union_of_isClosed h4 hQ3 hQ4
  have hunion : ({z : ℂ | 0 ≤ z.im ∧ 0 ≤ z.re} ∪ {z : ℂ | 0 ≤ z.im ∧ z.re ≤ 0})
      ∪ ({z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases le_total 0 z.im with h | h <;> rcases le_total 0 z.re with h' | h'
    · exact Or.inl (Or.inl ⟨h, h'⟩)
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h, h'⟩)
  have hc1 : IsClosed ({z : ℂ | 0 ≤ z.im ∧ 0 ≤ z.re} ∪ {z : ℂ | 0 ≤ z.im ∧ z.re ≤ 0}) :=
    hQ1.union hQ2
  have hc2 : IsClosed ({z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0}) :=
    hQ3.union hQ4
  have hall : ContinuousOn radVec Set.univ := by
    rw [← hunion]
    exact h12.union_of_isClosed h34 hc1 hc2
  exact continuousOn_univ.mp hall

end

end Work.SphereJordan
