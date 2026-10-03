import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Work.FIArea6Hecke.R.LvalStripGrowthAux
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea6Hecke.R.LvalStripNegHalfAux
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIArea5.S16Hecke.twistAux

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Metric

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A two-lines Phragmén–Lindelöf bound on `-1/2 ≤ re z ≤ 3/2` -/

private noncomputable def cP (z : ℂ) : ℂ := (z + (1 / 2 : ℂ)) ^ 2 + 16 * Complex.I

private noncomputable def cW (B₁ B₂ : ℝ) (z : ℂ) : ℂ :=
  ((2 * (B₁ / 2 + B₂ / 4) : ℝ) : ℂ)
    * Complex.exp ((((3 / 2 : ℝ) : ℂ) - z) * (Real.log 2 : ℂ)) * cP z

private lemma cW_arg_re (z : ℂ) :
    ((((3 / 2 : ℝ) : ℂ) - z) * (Real.log 2 : ℂ)).re = (3 / 2 - z.re) * Real.log 2 := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

private lemma exp_two_log_two : Real.exp (2 * Real.log 2) = 4 := by
  rw [two_mul, Real.exp_add, Real.exp_log (by norm_num)]
  norm_num

private lemma cW_norm (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (z : ℂ) :
    ‖cW B₁ B₂ z‖
      = 2 * (B₁ / 2 + B₂ / 4) * Real.exp ((3 / 2 - z.re) * Real.log 2) * ‖cP z‖ := by
  have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
  rw [cW, norm_mul, norm_mul, Complex.norm_of_nonneg h2M, Complex.norm_exp, cW_arg_re]

private lemma one_add_abs_sq_le_two_norm' (t : ℝ) :
    (1 + |t|) ^ 2 ≤ 2 * ‖((t : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
  set z : ℂ := ((t : ℂ) * Complex.I) ^ 2 + 16 * Complex.I with hz
  have hre : z.re = -(t ^ 2) := by
    rw [hz]
    norm_num [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have him : z.im = 16 := by
    rw [hz]
    norm_num [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two]
  have hns : Complex.normSq z = t ^ 4 + 256 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hnorm2 : ‖z‖ ^ 2 = t ^ 4 + 256 := by
    rw [← Complex.normSq_eq_norm_sq, hns]
  have hzn : ‖z‖ = Real.sqrt (t ^ 4 + 256) := by
    have h2' : ‖z‖ ^ 2 = (Real.sqrt (t ^ 4 + 256)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]; exact hnorm2
    have habs : |‖z‖| = |Real.sqrt (t ^ 4 + 256)| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h2'
    rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  rw [hzn]
  by_cases h : |t| ≤ 4
  · have h1 : (1 + |t|) ^ 2 ≤ 25 := by nlinarith [abs_nonneg t, h]
    have h16 : (16 : ℝ) ≤ Real.sqrt (t ^ 4 + 256) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [sq_nonneg t]
    linarith
  · have hu : (4 : ℝ) ≤ |t| := by
      have : (4 : ℝ) < |t| := not_le.mp h; linarith
    have h1 : (1 + |t|) ^ 2 ≤ 2 * |t| ^ 2 := by nlinarith [abs_nonneg t, hu]
    have hle : |t| ^ 2 ≤ Real.sqrt (t ^ 4 + 256) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have hs : (|t| ^ 2) ^ 2 = t ^ 4 := by rw [sq_abs]; ring
      rw [hs]; linarith [sq_nonneg t]
    linarith

private lemma cP_ge_one (z : ℂ) (h1 : -1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 2) :
    1 ≤ ‖cP z‖ := by
  rw [cP]
  let w : ℂ := z + (1 / 2 : ℂ)
  have hwre : w.re = z.re + 1 / 2 := by simp [w]
  have ha0 : 0 ≤ w.re := by rw [hwre]; linarith
  have ha2 : w.re ≤ 2 := by rw [hwre]; linarith
  have hre : (w ^ 2 + 16 * Complex.I).re = w.re ^ 2 - w.im ^ 2 := by
    have h16 : (16 : ℂ).im = 0 := by norm_num
    have h16' : (16 : ℂ).re = 16 := by norm_num
    simp only [Complex.add_re, sq, Complex.mul_re, h16, h16', Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
  have him : (w ^ 2 + 16 * Complex.I).im = 2 * w.re * w.im + 16 := by
    have h16 : (16 : ℂ).im = 0 := by norm_num
    have h16' : (16 : ℂ).re = 16 := by norm_num
    simp only [Complex.add_im, sq, Complex.mul_im, h16, h16', Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero]
    ring
  have hns : Complex.normSq (w ^ 2 + 16 * Complex.I)
      = (w.re ^ 2 - w.im ^ 2) ^ 2 + (2 * w.re * w.im + 16) ^ 2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hkey : 1 ≤ Complex.normSq (w ^ 2 + 16 * Complex.I) := by
    rw [hns]
    rcases lt_or_ge w.im 3 with hb3 | hb3
    · rcases lt_or_ge w.im (-3) with hb3' | hb3'
      · have hb2 : 9 ≤ w.im ^ 2 := by nlinarith [sq_nonneg (w.im + 3)]
        have ha2sq : w.re ^ 2 ≤ 4 := by
          nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ 2 - w.re by linarith)]
        nlinarith [sq_nonneg (w.re ^ 2 - w.im ^ 2 + 5), sq_nonneg (2 * w.re * w.im + 16)]
      · have hab : -6 ≤ w.re * w.im := by
          nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ w.im + 3 by linarith)]
        nlinarith [sq_nonneg (w.re ^ 2 - w.im ^ 2), sq_nonneg (2 * w.re * w.im + 16 - 4)]
    · have hb2 : 9 ≤ w.im ^ 2 := by nlinarith [sq_nonneg (w.im - 3)]
      have ha2sq : w.re ^ 2 ≤ 4 := by
        nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ 2 - w.re by linarith)]
      nlinarith [sq_nonneg (w.re ^ 2 - w.im ^ 2 + 5), sq_nonneg (2 * w.re * w.im + 16)]
  have hsq : 1 ≤ ‖w ^ 2 + 16 * Complex.I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact hkey
  have hfin : 1 ≤ ‖w ^ 2 + 16 * Complex.I‖ := by
    rw [one_le_sq_iff_one_le_abs] at hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using hsq
  simpa [w] using hfin

private lemma cP_le (σ t : ℝ) (h1 : 3 / 8 ≤ σ) (h2 : σ ≤ 1) :
    ‖cP ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 20 * (1 + |t|) ^ 2 := by
  rw [cP]
  set w : ℂ := (((σ + 1 / 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I with hw
  have hPeq : ((σ : ℂ) + (t : ℂ) * Complex.I) + (1 / 2 : ℂ) = w := by
    rw [hw]; push_cast; ring
  rw [hPeq]
  have hnormw : ‖w‖ ^ 2 = (σ + 1 / 2) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hw]
    ring
  have h0 : (0 : ℝ) ≤ σ + 1 / 2 := by linarith
  have h3 : σ + 1 / 2 ≤ 3 / 2 := by linarith
  have hs1 : (σ + 1 / 2) ^ 2 ≤ (3 / 2) ^ 2 := by nlinarith
  have htri : ‖w ^ 2 + 16 * Complex.I‖ ≤ ‖w ^ 2‖ + ‖(16 : ℂ) * Complex.I‖ := norm_add_le _ _
  have hw2 : ‖w ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_pow]
  have h16 : ‖(16 : ℂ) * Complex.I‖ = 16 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hfin : (3 / 2) ^ 2 + t ^ 2 + 16 ≤ 20 * (1 + |t|) ^ 2 := by
    nlinarith [sq_nonneg t, abs_nonneg t, sq_abs t]
  calc ‖w ^ 2 + 16 * Complex.I‖ ≤ ‖w ^ 2‖ + ‖(16 : ℂ) * Complex.I‖ := htri
    _ = ‖w‖ ^ 2 + 16 := by rw [hw2, h16]
    _ = (σ + 1 / 2) ^ 2 + t ^ 2 + 16 := by rw [hnormw]
    _ ≤ (3 / 2) ^ 2 + t ^ 2 + 16 := by linarith
    _ ≤ 20 * (1 + |t|) ^ 2 := hfin

private theorem two_lines_PL :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ), AnalyticOn ℂ f Set.univ →
      ∀ (B₁ B₂ : ℝ), 0 < B₁ → 0 < B₂ →
      (∀ t : ℝ, ‖f (((3 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B₁) →
      (∀ t : ℝ, ‖f (((-1 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B₂ * (1 + |t|) ^ (2 : ℕ)) →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
        ‖f z‖ ≤ Real.exp (K * (1 + |z.im|))) →
      ∀ σ t : ℝ, 3 / 8 ≤ σ → σ ≤ 1 →
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (B₁ + B₂) * (1 + |t|) ^ (10 : ℕ) := by
  refine ⟨80, by norm_num, ?_⟩
  intro f hf B₁ B₂ hB₁ hB₂ h1 h2 hg
  obtain ⟨K, hK0, hK⟩ := hg
  have hB₁' : (0 : ℝ) ≤ B₁ := le_of_lt hB₁
  have hB₂' : (0 : ℝ) ≤ B₂ := le_of_lt hB₂
  have hMpos : (0 : ℝ) < 2 * (B₁ / 2 + B₂ / 4) := by linarith
  have hW_diff : Differentiable ℂ (cW B₁ B₂) := by
    unfold cW cP
    fun_prop
  have hW_an : AnalyticOn ℂ (cW B₁ B₂) Set.univ :=
    hW_diff.differentiableOn.analyticOn isOpen_univ
  have hPge : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → (1 : ℝ) ≤ ‖cP z‖ :=
    fun z hz1 hz2 => cP_ge_one z hz1 hz2
  have hWne : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → cW B₁ B₂ z ≠ 0 := by
    intro z hz1 hz2
    have hP : (1 : ℝ) ≤ ‖cP z‖ := hPge z hz1 hz2
    have hPne : cP z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hP
      linarith
    rw [cW]
    exact mul_ne_zero (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hMpos)) (Complex.exp_ne_zero _)) hPne
  set U : Set ℂ := {z : ℂ | cW B₁ B₂ z ≠ 0} with hUdef
  have hF_an : AnalyticOn ℂ (fun z => f z / cW B₁ B₂ z) U := by
    refine AnalyticOn.div (hf.mono (Set.subset_univ U)) (hW_an.mono (Set.subset_univ U)) ?_
    intro z hz
    exact hz
  have hclo_sub : closure (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2)) ⊆ U := by
    refine fun z hz => ?_
    have hz' : z ∈ Complex.re ⁻¹' Set.Icc (-1 / 2) (3 / 2) :=
      closure_minimal
        (fun w hw => show w ∈ Complex.re ⁻¹' Set.Icc (-1 / 2) (3 / 2) from
          ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
        (IsClosed.preimage Complex.continuous_re isClosed_Icc) hz
    exact hWne z hz'.1 hz'.2
  have hF_dcl : DiffContOnCl ℂ (fun z => f z / cW B₁ B₂ z)
      (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2)) := by
    refine ⟨hF_an.differentiableOn.mono ?_, hF_an.continuousOn.mono hclo_sub⟩
    intro z hz
    exact hWne z (le_of_lt hz.1) (le_of_lt hz.2)
  have hbd_a : ∀ z : ℂ, z.re = -1 / 2 → ‖f z / cW B₁ B₂ z‖ ≤ 1 := by
    intro z hzr
    have hzdec : z = ((-1 : ℝ) / 2 : ℂ) + (z.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hzr]
      norm_num
    have hfz : ‖f z‖ ≤ B₂ * (1 + |z.im|) ^ 2 := by
      conv_lhs => rw [hzdec]
      exact h2 z.im
    have hPval : ‖cP z‖ = ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
      have hzz : ((-1 : ℝ) / 2 : ℂ) + (z.im : ℂ) * Complex.I + 1 / 2 = (z.im : ℂ) * Complex.I := by
        norm_num
      conv_lhs => rw [cP, hzdec, hzz]
    have hWval : ‖cW B₁ B₂ z‖
        = 2 * (B₁ / 2 + B₂ / 4) * 4 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
      rw [cW_norm B₁ B₂ hB₁' hB₂' z, hzr,
        show (3 / 2 : ℝ) - (-1 / 2) = 2 by norm_num, hPval, exp_two_log_two]
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [hWval]
    have hq := one_add_abs_sq_le_two_norm' z.im
    have hQnn : (0 : ℝ) ≤ ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := norm_nonneg _
    have hstep1 : B₂ * (1 + |z.im|) ^ 2 ≤ B₂ * (2 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖) :=
      mul_le_mul_of_nonneg_left hq hB₂'
    have hstep2 : B₂ * (2 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖)
        ≤ (2 * (B₁ / 2 + B₂ / 4) * 4) * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ := by
      rw [show B₂ * (2 * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖)
          = (B₂ * 2) * ‖((z.im : ℂ) * Complex.I) ^ 2 + 16 * Complex.I‖ by ring]
      apply mul_le_mul_of_nonneg_right _ hQnn
      linarith
    exact le_trans hfz (le_trans hstep1 hstep2)
  have hbd_b : ∀ z : ℂ, z.re = 3 / 2 → ‖f z / cW B₁ B₂ z‖ ≤ 1 := by
    intro z hzr
    have hzdec : z = (3 / 2 : ℂ) + (z.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hzr]
      norm_num
    have hfz : ‖f z‖ ≤ B₁ := by
      conv_lhs => rw [hzdec]
      exact h1 z.im
    have hPval : (1 : ℝ) ≤ ‖cP z‖ := cP_ge_one z (by rw [hzr]; norm_num) (by rw [hzr])
    have hWval : ‖cW B₁ B₂ z‖ = 2 * (B₁ / 2 + B₂ / 4) * ‖cP z‖ := by
      rw [cW_norm B₁ B₂ hB₁' hB₂' z, hzr,
        show (3 / 2 : ℝ) - 3 / 2 = 0 by norm_num, zero_mul, Real.exp_zero]
      ring
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [hWval]
    have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
    calc ‖f z‖ ≤ B₁ := hfz
      _ ≤ 2 * (B₁ / 2 + B₂ / 4) * 1 := by linarith
      _ ≤ 2 * (B₁ / 2 + B₂ / 4) * ‖cP z‖ := by
            exact mul_le_mul_of_nonneg_left hPval h2M
  have hgrowth : ∃ c < Real.pi / ((3 / 2 : ℝ) - (-1 / 2)), ∃ B' : ℝ,
      (fun z => f z / cW B₁ B₂ z) =O[Filter.comap (abs ∘ Complex.im) Filter.atTop
        ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2))]
        fun z => Real.exp (B' * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, K, ?_⟩
    · rw [show (3 / 2 : ℝ) - (-1 / 2) = 2 by norm_num]
      linarith [Real.pi_gt_three]
    · rw [Asymptotics.isBigO_iff]
      refine ⟨1 / (2 * (B₁ / 2 + B₂ / 4)), ?_⟩
      refine Filter.Eventually.filter_mono inf_le_right ?_
      rw [Filter.eventually_principal]
      intro z hz
      have hzr1 : -1 / 2 ≤ z.re := le_of_lt hz.1
      have hzr2 : z.re ≤ 3 / 2 := le_of_lt hz.2
      have hfz : ‖f z‖ ≤ Real.exp (K * (1 + |z.im|)) := hK z hzr1 hzr2
      have hP1 : (1 : ℝ) ≤ ‖cP z‖ := cP_ge_one z hzr1 hzr2
      have hexp1 : (1 : ℝ) ≤ Real.exp ((3 / 2 - z.re) * Real.log 2) :=
        Real.one_le_exp (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
      have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
      have hWval := cW_norm B₁ B₂ hB₁' hB₂' z
      have hWlb : 2 * (B₁ / 2 + B₂ / 4) ≤ ‖cW B₁ B₂ z‖ := by
        rw [hWval]
        have hstep : (2 * (B₁ / 2 + B₂ / 4) * 1) * 1
            ≤ (2 * (B₁ / 2 + B₂ / 4) * Real.exp ((3 / 2 - z.re) * Real.log 2)) * ‖cP z‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp1 h2M) hP1 zero_le_one (by positivity)
        simpa using hstep
      rw [norm_div, Real.norm_of_nonneg (Real.exp_nonneg _)]
      calc ‖f z‖ / ‖cW B₁ B₂ z‖ ≤ Real.exp (K * (1 + |z.im|)) / (2 * (B₁ / 2 + B₂ / 4)) :=
            div_le_div₀ (Real.exp_nonneg _) hfz hMpos hWlb
        _ = (1 / (2 * (B₁ / 2 + B₂ / 4))) * Real.exp (K * (1 + |z.im|)) := by ring
        _ ≤ (1 / (2 * (B₁ / 2 + B₂ / 4))) * Real.exp (K * Real.exp (1 * |z.im|)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp.mpr
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hK0
  intro σ t hσ1 hσ2
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : z.re = σ := by rw [hz]; simp
  have hzim : z.im = t := by rw [hz]; simp
  have hza : -1 / 2 ≤ z.re := by rw [hzre]; linarith
  have hzb : z.re ≤ 3 / 2 := by rw [hzre]; linarith
  have hF1 : ‖f z / cW B₁ B₂ z‖ ≤ 1 :=
    PhragmenLindelof.vertical_strip (f := fun w => f w / cW B₁ B₂ w)
      (a := (-1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) hF_dcl hgrowth hbd_a hbd_b hza hzb
  have hWpos : 0 < ‖cW B₁ B₂ z‖ := norm_pos_iff.mpr (hWne z hza hzb)
  have hfW : ‖f z‖ ≤ ‖cW B₁ B₂ z‖ := by
    rw [norm_div] at hF1
    have := (div_le_iff₀ hWpos).mp hF1
    simpa using this
  have hPle : ‖cP z‖ ≤ 20 * (1 + |t|) ^ 2 := by
    rw [show z = (σ : ℂ) + (t : ℂ) * Complex.I from hz]
    exact cP_le σ t hσ1 hσ2
  have hexp_le : Real.exp ((3 / 2 - z.re) * Real.log 2) ≤ 4 := by
    rw [hzre]
    calc Real.exp ((3 / 2 - σ) * Real.log 2) ≤ Real.exp (2 * Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          nlinarith
      _ = 4 := exp_two_log_two
  have hWup2 : ‖cW B₁ B₂ z‖ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ 2 := by
    rw [cW_norm B₁ B₂ hB₁' hB₂' z]
    have h2M : (0 : ℝ) ≤ 2 * (B₁ / 2 + B₂ / 4) := by linarith
    calc 2 * (B₁ / 2 + B₂ / 4) * Real.exp ((3 / 2 - z.re) * Real.log 2) * ‖cP z‖
        ≤ (2 * (B₁ / 2 + B₂ / 4) * 4) * (20 * (1 + |t|) ^ 2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hexp_le h2M) hPle (norm_nonneg _)
            (by positivity)
      _ = 160 * (B₁ / 2 + B₂ / 4) * (1 + |t|) ^ 2 := by ring
      _ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  have hWup : ‖cW B₁ B₂ z‖ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ (10 : ℕ) := by
    refine le_trans hWup2 ?_
    have hpow : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ (10 : ℕ) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
    exact mul_le_mul_of_nonneg_left hpow (by linarith)
  calc ‖f z‖ ≤ ‖cW B₁ B₂ z‖ := hfW
    _ ≤ 80 * (B₁ + B₂) * (1 + |t|) ^ (10 : ℕ) := hWup

/-- The `L`-continuation has polynomial growth on the half-strip `3/8 ≤ re s ≤ 1`, with a fixed
power of `d`, uniformly in `χ` and `Lam`: this is the standard "partial sums with a power saving
continue the Dirichlet series past `re s = 1`" bound (Pólya–Vinogradov for the disc sums of a
mean-zero strict character).  It is the weak companion of the sharp strip bound, and supplies value
bounds below `re s = 1/2`, where the sharp form is not available. -/
theorem LvalStripContAux :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 1 →
          ‖Work.FIArea6Hecke.Lval d 0 Lam z‖
            ≤ C * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) := by
  obtain ⟨Cpl, hCplpos, hPL⟩ := two_lines_PL
  obtain ⟨K₂, hK₂pos, hK₂⟩ := heckeLval_negHalf_bound'
  set A : ℝ := Work.FIArea5.S16Hecke.heckeLMajorant + K₂ with hA
  have hApos : 0 < A := by
    rw [hA]; exact add_pos Work.FIArea5.S16Hecke.heckeLMajorant_pos hK₂pos
  refine ⟨max 1 (Cpl * A + 1), lt_max_of_lt_left one_pos, ?_⟩
  intro d hd chi hchi hnontriv Lam hAn hagr z hz1 hz2
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  -- the twist: same `L`-series, but with non-zero unit sum and vanishing `0`-th Gauss sum
  set psi : GaussianInt → ℂ := Work.FIArea5.S16Hecke.twist chi 0 with hpsi
  have hpsiStrict : Work.FIArea5.S16Hecke.IsCharMod4dStrict d psi := by
    rw [hpsi]; exact Work.FIArea5.S16Hecke.twist_isCharMod4dStrict d hd chi 0 hchi
  have hUb : ∀ z : GaussianInt, ‖psi z‖ ≤ 1 := hpsiStrict.1.2.2.1
  have hU : Work.FIArea5.S16Hecke.unitSum psi 0 ≠ 0 := by
    rw [hpsi, Work.FIArea5.S16Hecke.twist_unitSum d hd chi 0 hchi.1]; norm_num
  have h0 : Work.FIArea5.S16Hecke.gaussSum d psi 0 = 0 := by
    refine gaussSum_zero_of_nontrivial hd hpsiStrict ?_
    obtain ⟨z₀, hz₀p, hz₀u, hz₀ne⟩ := hnontriv
    exact ⟨z₀, hz₀p, hz₀u, by
      rw [hpsi, Work.FIArea5.S16Hecke.twist_eq_of_isPrimary chi 0 hz₀p]; exact hz₀ne⟩
  have hser : Work.FIArea5.S16Hecke.heckeLSeries psi 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi 0 := by
    rw [hpsi]; exact Work.FIArea6Hecke.heckeLSeries_twist chi 0
  have hagr' : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries psi 0 s := by
    intro s hs; rw [hser]; exact hagr s hs
  -- `Lval d 0 Lam` is entire (it is `Lcont d Lam 0`)
  have hLval_an : AnalyticOn ℂ (Work.FIArea6Hecke.Lval d 0 Lam) Set.univ := by
    have hdiff : Differentiable ℂ (Work.FIArea5.S16Hecke.Lcont d Lam 0) :=
      Work.FIArea5.S16Hecke.differentiable_Lcont hd
        (differentiableOn_univ.mp hAn.differentiableOn) 0
    have hfe : Work.FIArea6Hecke.Lval d 0 Lam = Work.FIArea5.S16Hecke.Lcont d Lam 0 := by
      funext w
      simp only [Work.FIArea6Hecke.Lval, Work.FIArea5.S16Hecke.Lcont,
        Work.FIArea5.S16Hecke.completeDenom, Work.FITop4.Bridge.heckeArch]
      norm_num
    rw [hfe]
    exact DifferentiableOn.analyticOn (Differentiable.differentiableOn hdiff) isOpen_univ
  set f : ℂ → ℂ := Work.FIArea6Hecke.Lval d 0 Lam with hf
  -- growth of `f` on the strip
  obtain ⟨K, hK0, hKgrow⟩ :=
    Work.FIArea6Hecke.R.heckeLval_strip_growth' d hd psi hpsiStrict hUb hU h0 Lam hAn hagr'
  -- the two boundary constants
  set B₁ : ℝ := Work.FIArea5.S16Hecke.heckeLMajorant with hB₁
  have hB₁pos : 0 < B₁ := by rw [hB₁]; exact Work.FIArea5.S16Hecke.heckeLMajorant_pos
  set B₂ : ℝ := K₂ * (d : ℝ) ^ (3 : ℕ) with hB₂
  have hB₂pos : 0 < B₂ := by rw [hB₂]; positivity
  -- bound on the line `re = 3/2` (absolutely convergent Dirichlet series)
  have h1 : ∀ t : ℝ, ‖f (((3 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B₁ := by
    intro t
    set s : ℂ := ((3 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I with hs
    have hsre : s.re = 3 / 2 := by simp [hs]
    have hne : Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 :=
      Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 (by rw [hsre]; norm_num)
    have hval : f s = Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
      simp only [f, Work.FIArea6Hecke.Lval]
      rw [hagr s (by rw [hsre]; norm_num)]
      exact mul_div_cancel_left₀ _ hne
    rw [hval, hB₁]
    exact Work.FIArea5.S16Hecke.heckeLSeries_norm_le_re_ge_three_halves chi 0 hb (by rw [hsre])
  -- bound on the line `re = -1/2` (the dual-side theta estimate)
  have h2 : ∀ t : ℝ, ‖f (((-1 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ B₂ * (1 + |t|) ^ (2 : ℕ) := by
    intro t
    have h := hK₂ d hd psi hpsiStrict hUb hU h0 Lam hAn hagr' t
    have harg : (((-1 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)
        = (((-1 / 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [harg]
    simpa only [f, hB₂] using h
  -- Phragmén–Lindelöf on `-1/2 ≤ re ≤ 3/2`
  have hPLz := hPL f hLval_an B₁ B₂ hB₁pos hB₂pos h1 h2 ⟨K, hK0, hKgrow⟩ z.re z.im hz1 hz2
  have hzeq : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by
    apply Complex.ext <;> simp
  rw [hzeq] at hPLz
  -- absorb the constants
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd3 : (d : ℝ) ^ (3 : ℕ) ≤ (d : ℝ) ^ (10 : ℕ) :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hBsum : B₁ + B₂ ≤ A * (d : ℝ) ^ (3 : ℕ) := by
    rw [hB₁, hB₂, hA]
    have h3 : (1 : ℝ) ≤ (d : ℝ) ^ (3 : ℕ) := one_le_pow₀ hd1
    nlinarith [Work.FIArea5.S16Hecke.heckeLMajorant_pos, hK₂pos]
  have hz10 : (0 : ℝ) ≤ (1 + |z.im|) ^ (10 : ℕ) := by positivity
  have hd10nn : (0 : ℝ) ≤ (d : ℝ) ^ (10 : ℕ) := by positivity
  have hCplnn : 0 ≤ Cpl := hCplpos.le
  refine hPLz.trans ?_
  calc Cpl * (B₁ + B₂) * (1 + |z.im|) ^ (10 : ℕ)
      ≤ Cpl * (A * (d : ℝ) ^ (3 : ℕ)) * (1 + |z.im|) ^ (10 : ℕ) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBsum hCplnn) hz10
    _ ≤ max 1 (Cpl * A + 1) * (d : ℝ) ^ (10 : ℕ) * (1 + |z.im|) ^ (10 : ℕ) := by
        have h1' : Cpl * (A * (d : ℝ) ^ (3 : ℕ))
            ≤ max 1 (Cpl * A + 1) * (d : ℝ) ^ (10 : ℕ) := by
          have hCA : Cpl * A ≤ max 1 (Cpl * A + 1) := by
            linarith [le_max_right (1:ℝ) (Cpl * A + 1)]
          have hnn : 0 ≤ Cpl * A := by positivity
          calc Cpl * (A * (d : ℝ) ^ (3 : ℕ)) = (Cpl * A) * (d : ℝ) ^ (3 : ℕ) := by ring
            _ ≤ (Cpl * A) * (d : ℝ) ^ (10 : ℕ) :=
                mul_le_mul_of_nonneg_left hd3 hnn
            _ ≤ max 1 (Cpl * A + 1) * (d : ℝ) ^ (10 : ℕ) :=
                mul_le_mul_of_nonneg_right hCA hd10nn
        exact mul_le_mul_of_nonneg_right h1' hz10

end

end Work.FIArea6Hecke.R
