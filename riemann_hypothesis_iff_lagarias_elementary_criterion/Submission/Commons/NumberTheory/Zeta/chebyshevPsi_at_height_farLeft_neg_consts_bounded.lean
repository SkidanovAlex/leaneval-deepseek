import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_fe_expanded
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.Zeta.vonMangoldt_rpow_five_fourths_tsum_le
import Submission.Commons.NumberTheory.Zeta.riemannZeta_eq_zero_iff_trivial_of_re_nonpos
import Submission.Commons.NumberTheory.Zeta.zeta_ne_zero_of_rh_gt_half
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.NumberTheory.Zeta.zeta_strip_glue
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
import Submission.Commons.NumberTheory.Zeta.completedRiemannZeta_zero_re_eq_half
import Submission.Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le
import Submission.Commons.NumberTheory.Zeta.divisor_riemannZeta1_eq_completedRiemannZeta_ball
import Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le
import Submission.Commons.NumberTheory.Zeta.zeta1_exists_good_radius
import Submission.Commons.NumberTheory.Zeta.mangoldtPerronError_bound_2472
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.perronOne_bound
import Submission.Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open Complex Filter Set MeasureTheory Metric intervalIntegral
open scoped Real Topology BigOperators
open Filter Finset
open Real
open ArithmeticFunction hiding log id

noncomputable section

namespace Commons.NumberTheory.Zeta


private lemma norm_nat_cpow_neg_sg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(((n : ℕ) : ℂ) ^ (-s))‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)]
  rw [Complex.neg_re]

private lemma norm_head_le_sg (N : ℕ) (s : ℂ) :
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
  calc
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact norm_nat_cpow_neg_sg hn1 s

private lemma norm_add_mul_I_le_sg (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ σ + |t| := by
  calc
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ ‖(σ : ℂ)‖ + ‖(Complex.I * (t : ℂ))‖ := norm_add_le _ _
    _ = σ + |t| := by
      have h1 : ‖(σ : ℂ)‖ = |σ| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(Complex.I * (t : ℂ))‖ = |t| := by
        rw [norm_mul, Complex.norm_I]
        rw [Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [h1, h2]
      rw [abs_of_nonneg hσ0]

private lemma pole_norm_le_sg (s : ℂ) (ht : 1 ≤ |s.im|) (N : ℕ) (hN : 1 ≤ N) :
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN0
  have hcast : ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) := by norm_num
  have hnormN : ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ = ((N : ℕ) : ℝ) ^ (1 - s.re) := by
    rw [hcast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0 (1 - s)]
    simp
  have hsne : s - 1 ≠ 0 := by
    intro h
    have hre : (s - 1).im = 0 := congrArg Complex.im h
    have hsi : s.im = 0 := by simpa using hre
    have hcontra : |s.im| = 0 := by
      rw [hsi]
      simp
    linarith
  have hnorm_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hsne
  have hden : 1 ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).im| ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
    have h2 : |(s - 1).im| = |s.im| := by simp
    linarith
  have hpow_nonneg : 0 ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := Real.rpow_nonneg hN0le _
  calc
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ = ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ / ‖s - 1‖ := by rw [norm_div]
    _ = ((N : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by rw [hnormN]
    _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [div_le_iff₀ hnorm_pos]
      calc
        ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) * 1 := by ring
        _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) * ‖s - 1‖ := mul_le_mul_of_nonneg_left hden hpow_nonneg

private lemma em_tail_norm_le_sg (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ ≤
      (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := by
  have htel := emTerm_tsum_le N hN s hs0 hs1
  have hnormS : Summable (fun m : ℕ =>
      ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖) := by
    exact htel.1.norm
  calc
    ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
        ≤ ∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
          norm_tsum_le_tsum_norm hnormS
    _ ≤ (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := htel.2

/-- Main reduction: `‖ζ(σ+I t)‖ ≤ A(N) + (1 + 1/σ)·N^{1-σ}`. -/
private lemma zeta_bound_emN_sg {σ t : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (ht : 1 ≤ |t|)
    (N : ℕ) (hN : 1 ≤ N) (hNt : |t| + 3 ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let H : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))
  let M : ℂ := ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
  let T : ℂ := ∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))
  let A0 : ℝ := ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)
  let P : ℝ := ((N : ℕ) : ℝ) ^ (1 - σ)
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have ht' : 1 ≤ |s.im| := by simpa [hsim] using ht
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s ≠ 1 := by
    intro h
    have hsi : s.im = 0 := by simpa using congrArg Complex.im h
    have ht0 : t = 0 := by simpa [hsim] using hsi
    have habs : |t| = 0 := by rw [ht0]; simp
    have hpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN0
  have hNnorm : ‖s‖ ≤ (N : ℝ) := by
    have h1 : ‖s‖ ≤ σ + |t| := by
      simpa [s] using norm_add_mul_I_le_sg σ t (le_of_lt hσ0)
    have h2 : σ + |t| ≤ (N : ℝ) := by
      have : |t| + 3 ≤ (N : ℝ) := hNt
      linarith
    linarith
  have hmul' : ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by
    calc
      ((N : ℕ) : ℝ) ^ (1 - s.re)
          = ((N : ℕ) : ℝ) ^ (1 + -s.re) := by rw [sub_eq_add_neg]
      _ = ((N : ℕ) : ℝ) ^ (1 : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by rw [Real.rpow_add hN0]
      _ = ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by rw [Real.rpow_one]
  have hmul : ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) := hmul'.symm
  have htailT : ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) := by
    have h := em_tail_norm_le_sg s hs0 hs1 N hN
    simpa [T] using h
  have hC2 : (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) ≤ (1 / σ) * P := by
    have hrpow : 0 ≤ ((N : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg hN0le (-s.re)
    calc
      (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re)
          = (‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re)) / s.re := by field_simp [ne_of_gt hs0]
      _ ≤ (((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re)) / s.re := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNnorm hrpow) (le_of_lt hs0)
      _ = ((N : ℕ) : ℝ) ^ (1 - s.re) / s.re := by rw [hmul]
      _ = (1 / s.re) * ((N : ℕ) : ℝ) ^ (1 - s.re) := by ring
      _ = (1 / σ) * P := by rw [hsre]
  have htailP : ‖T‖ ≤ P / σ := by
    calc
      ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) := htailT
      _ ≤ (1 / σ) * P := hC2
      _ = P / σ := by
        rw [one_div, div_eq_mul_inv]
        ring
  have hpoleM : ‖M‖ ≤ P := by
    have h := pole_norm_le_sg s ht' N hN
    dsimp [M, P]
    rw [hsre] at h
    exact h
  have hAhead : ‖H‖ ≤ A0 := by
    have h := norm_head_le_sg N s
    dsimp [H, A0]
    rw [hsre] at h
    exact h
  have htri : ‖H + M + T‖ ≤ ‖H‖ + ‖M‖ + ‖T‖ := by
    have h1 : ‖H + M + T‖ ≤ ‖H + M‖ + ‖T‖ := norm_add_le (H + M) T
    have h2 : ‖H + M‖ ≤ ‖H‖ + ‖M‖ := norm_add_le H M
    linarith
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ = ‖riemannZeta s‖ := by simp [s]
    _ = ‖H + M + T‖ := by
      congr 1
      have hid := zeta_eq_emN (s := s) hs0 hs1 N hN
      simpa [H, M, T] using hid
    _ ≤ ‖H‖ + ‖M‖ + ‖T‖ := htri
    _ ≤ A0 + P + P / σ := by
      exact add_le_add (add_le_add hAhead hpoleM) htailP
    _ = A0 + (1 + 1 / σ) * P := by
      field_simp [ne_of_gt hσ0]
      ring
    _ = (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := by
      simp [A0, P]



theorem zeta_strip_growth_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1000000 ∧ ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (1 + 1 / δ) * (|t| + 3) ^ (1 / 2 - δ / 2) := by
  refine ⟨1000000, by norm_num, by norm_num, ?_⟩
  intro δ σ t hδ0 hδ1 hσlo hσhi ht
  have hσ0 : 0 < σ := by linarith
  let N : ℕ := Nat.floor |t| + 4
  have hNge : |t| + 3 ≤ (N : ℝ) := by
    dsimp [N]
    rw [Nat.cast_add]
    have hlt : |t| < ((Nat.floor |t| : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one |t|
    norm_num
    linarith
  have hNle : (N : ℝ) ≤ |t| + 4 := by
    dsimp [N]
    rw [Nat.cast_add]
    norm_num
    have hfl : ((Nat.floor |t| : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    linarith
  have hN1 : 1 ≤ N := by
    have hfl1 : (1 : ℕ) ≤ Nat.floor |t| := by
      exact Nat.le_floor (by exact_mod_cast ht : ((1 : ℕ) : ℝ) ≤ |t|)
    dsimp [N]
    omega
  have hb := zeta_bound_emN_sg (σ := σ) (t := t) hσ0 hσhi ht N hN1 hNge
  have hg := zeta_strip_glue δ σ t N hδ0 hδ1 hσlo hσhi ht hNge hNle
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := hb
    _ ≤ 1000000 * (1 + 1 / δ) * (|t| + 3) ^ (1 / 2 - δ / 2) := hg



-- ############ R2: emN machinery (copied from commons pattern) ############

private lemma norm_nat_cpow_neg_pg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(((n : ℕ) : ℂ) ^ (-s))‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)]
  rw [Complex.neg_re]

private lemma norm_head_le_pg (N : ℕ) (s : ℂ) :
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
  calc
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact norm_nat_cpow_neg_pg hn1 s

private lemma norm_add_mul_I_le_pg (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ σ + |t| := by
  calc
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ ‖(σ : ℂ)‖ + ‖(Complex.I * (t : ℂ))‖ := norm_add_le _ _
    _ = σ + |t| := by
      have h1 : ‖(σ : ℂ)‖ = |σ| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(Complex.I * (t : ℂ))‖ = |t| := by
        rw [norm_mul, Complex.norm_I]
        rw [Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [h1, h2]
      rw [abs_of_nonneg hσ0]

private lemma pole_norm_le_pg (s : ℂ) (ht : 1 ≤ |s.im|) (N : ℕ) (hN : 1 ≤ N) :
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN0
  have hcast : ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) := by norm_num
  have hnormN : ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ = ((N : ℕ) : ℝ) ^ (1 - s.re) := by
    rw [hcast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0 (1 - s)]
    simp
  have hsne : s - 1 ≠ 0 := by
    intro h
    have hre : (s - 1).im = 0 := congrArg Complex.im h
    have hsi : s.im = 0 := by simpa using hre
    have hcontra : |s.im| = 0 := by
      rw [hsi]
      simp
    linarith
  have hnorm_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hsne
  have hden : 1 ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).im| ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
    have h2 : |(s - 1).im| = |s.im| := by simp
    linarith
  have hpow_nonneg : 0 ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := Real.rpow_nonneg hN0le _
  calc
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ = ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ / ‖s - 1‖ := by rw [norm_div]
    _ = ((N : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by rw [hnormN]
    _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [div_le_iff₀ hnorm_pos]
      calc
        ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) * 1 := by ring
        _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) * ‖s - 1‖ := mul_le_mul_of_nonneg_left hden hpow_nonneg

private lemma em_tail_norm_le_pg (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ ≤
      (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := by
  have htel := emTerm_tsum_le N hN s hs0 hs1
  have hnormS : Summable (fun m : ℕ =>
      ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖) := by
    exact htel.1.norm
  calc
    ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
        ≤ ∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
          norm_tsum_le_tsum_norm hnormS
    _ ≤ (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := htel.2

/-- Euler-Maclaurin decomposition bound, valid for all `0 < σ ≤ 3`. -/
private lemma zeta_bound_emN3_pg {σ t : ℝ} (hσ0 : 0 < σ) (hσ3 : σ ≤ 3) (ht : 1 ≤ |t|)
    (N : ℕ) (hN : 1 ≤ N) (hNt : |t| + 3 ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let H : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))
  let M : ℂ := ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
  let T : ℂ := ∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))
  let A0 : ℝ := ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)
  let P : ℝ := ((N : ℕ) : ℝ) ^ (1 - σ)
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have ht' : 1 ≤ |s.im| := by simpa [hsim] using ht
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s ≠ 1 := by
    intro h
    have hsi : s.im = 0 := by simpa using congrArg Complex.im h
    have ht0 : t = 0 := by simpa [hsim] using hsi
    have habs : |t| = 0 := by rw [ht0]; simp
    have hpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN0
  have hNnorm : ‖s‖ ≤ (N : ℝ) := by
    have h1 : ‖s‖ ≤ σ + |t| := by
      simpa [s] using norm_add_mul_I_le_pg σ t (le_of_lt hσ0)
    have h2 : σ + |t| ≤ (N : ℝ) := by
      have : |t| + 3 ≤ (N : ℝ) := hNt
      linarith
    linarith
  have hmul' : ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by
    calc
      ((N : ℕ) : ℝ) ^ (1 - s.re)
          = ((N : ℕ) : ℝ) ^ (1 + -s.re) := by rw [sub_eq_add_neg]
      _ = ((N : ℕ) : ℝ) ^ (1 : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by rw [Real.rpow_add hN0]
      _ = ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by rw [Real.rpow_one]
  have hmul : ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) := hmul'.symm
  have htailT : ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) := by
    have h := em_tail_norm_le_pg s hs0 hs1 N hN
    simpa [T] using h
  have hC2 : (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) ≤ (1 / σ) * P := by
    have hrpow : 0 ≤ ((N : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg hN0le (-s.re)
    calc
      (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re)
          = (‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re)) / s.re := by field_simp [ne_of_gt hs0]
      _ ≤ (((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re)) / s.re := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNnorm hrpow) (le_of_lt hs0)
      _ = ((N : ℕ) : ℝ) ^ (1 - s.re) / s.re := by rw [hmul]
      _ = (1 / s.re) * ((N : ℕ) : ℝ) ^ (1 - s.re) := by ring
      _ = (1 / σ) * P := by rw [hsre]
  have htailP : ‖T‖ ≤ P / σ := by
    calc
      ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) := htailT
      _ ≤ (1 / σ) * P := hC2
      _ = P / σ := by
        rw [one_div, div_eq_mul_inv]
        ring
  have hpoleM : ‖M‖ ≤ P := by
    have h := pole_norm_le_pg s ht' N hN
    dsimp [M, P]
    rw [hsre] at h
    exact h
  have hAhead : ‖H‖ ≤ A0 := by
    have h := norm_head_le_pg N s
    dsimp [H, A0]
    rw [hsre] at h
    exact h
  have htri : ‖H + M + T‖ ≤ ‖H‖ + ‖M‖ + ‖T‖ := by
    have h1 : ‖H + M + T‖ ≤ ‖H + M‖ + ‖T‖ := norm_add_le (H + M) T
    have h2 : ‖H + M‖ ≤ ‖H‖ + ‖M‖ := norm_add_le H M
    linarith
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ = ‖riemannZeta s‖ := by simp [s]
    _ = ‖H + M + T‖ := by
      congr 1
      have hid := zeta_eq_emN (s := s) hs0 hs1 N hN
      simpa [H, M, T] using hid
    _ ≤ ‖H‖ + ‖M‖ + ‖T‖ := htri
    _ ≤ A0 + P + P / σ := by
      exact add_le_add (add_le_add hAhead hpoleM) htailP
    _ = A0 + (1 + 1 / σ) * P := by
      field_simp [ne_of_gt hσ0]
      ring
    _ = (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := by
      simp [A0, P]

/-- Region lemma 2: `1/4 ≤ σ ≤ 3`, polynomial bound of degree 1. -/
private theorem zeta_re_quarter_three_poly_pg :
    ∃ C : ℝ, 0 < C ∧ C ≤ 12 ∧ ∀ (σ t : ℝ), (1 / 4 : ℝ) ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4 := by
  refine ⟨12, by norm_num, by norm_num, ?_⟩
  intro σ t hσlo hσhi ht
  have hσ0 : 0 < σ := by linarith
  have hσn0 : 0 ≤ σ := le_of_lt hσ0
  let N : ℕ := Nat.floor |t| + 4
  have hNge : |t| + 3 ≤ (N : ℝ) := by
    dsimp [N]
    rw [Nat.cast_add]
    have hlt : |t| < ((Nat.floor |t| : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one |t|
    norm_num
    linarith
  have hNle : (N : ℝ) ≤ |t| + 4 := by
    dsimp [N]
    rw [Nat.cast_add]
    norm_num
    have hfl : ((Nat.floor |t| : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    linarith
  have hN1 : 1 ≤ N := by
    have hfl1 : (1 : ℕ) ≤ Nat.floor |t| := by
      exact Nat.le_floor (by exact_mod_cast ht : ((1 : ℕ) : ℝ) ≤ |t|)
    dsimp [N]
    omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hb := zeta_bound_emN3_pg (σ := σ) (t := t) hσ0 hσhi ht N hN1 hNge
  have hA0 : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ (N : ℝ) := by
    have hle : ∀ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) ≤ (1 : ℝ) := by
      intro n hn
      have hn1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1n
      calc
        ((n : ℕ) : ℝ) ^ (-σ) ≤ ((n : ℕ) : ℝ) ^ (0 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le hx (by linarith : -σ ≤ 0)
        _ = 1 := by rw [Real.rpow_zero]
    calc
      (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        exact Finset.sum_le_sum hle
      _ = (N : ℝ) := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc 1 N).card = N := by
          rw [Nat.card_Icc]
          omega
        rw [hcard]
        simp
  have hinv : σ⁻¹ ≤ 4 := by
    have h4s : (1 : ℝ) ≤ 4 * σ := by nlinarith
    simpa using (div_le_iff₀ hσ0).mpr h4s
  have h15 : (1 + 1 / σ : ℝ) ≤ 5 := by
    have : (1 / σ : ℝ) ≤ 4 := by simpa [one_div] using hinv
    linarith
  have hP : ((N : ℕ) : ℝ) ^ (1 - σ) ≤ (N : ℝ) := by
    calc
      ((N : ℕ) : ℝ) ^ (1 - σ) ≤ ((N : ℕ) : ℝ) ^ (1 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith : 1 - σ ≤ 1)
      _ = (N : ℝ) := by rw [Real.rpow_one]
  have hPnonneg : 0 ≤ ((N : ℕ) : ℝ) ^ (1 - σ) := Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ N)) _
  have hNnonneg : 0 ≤ (N : ℝ) := by exact_mod_cast (by omega : 0 ≤ N)
  have h2term : (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) ≤ 5 * (N : ℝ) := by
    calc
      (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) ≤ 5 * ((N : ℕ) : ℝ) ^ (1 - σ) := by
        exact mul_le_mul_of_nonneg_right h15 hPnonneg
      _ ≤ 5 * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 5)
  have hmain : ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ 6 * (N : ℝ) := by
    calc
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
          (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := hb
      _ ≤ (N : ℝ) + 5 * (N : ℝ) := add_le_add hA0 h2term
      _ = 6 * (N : ℝ) := by ring
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ 6 * (N : ℝ) := hmain
    _ ≤ 6 * (|t| + 4) := by
      exact mul_le_mul_of_nonneg_left hNle (by norm_num : (0 : ℝ) ≤ 6)
    _ ≤ 12 * (|t| + 3) := by
      have ht13 : (|t| + 4 : ℝ) ≤ 2 * (|t| + 3) := by nlinarith [ht]
      nlinarith
    _ ≤ 12 * (|t| + 3) ^ 4 := by
      have hx : 1 ≤ |t| + 3 := by nlinarith [ht]
      have hpow : (|t| + 3 : ℝ) ≤ (|t| + 3) ^ 4 := by
        have h1 : (|t| + 3 : ℝ) ^ (1 : ℕ) ≤ (|t| + 3) ^ 4 := pow_le_pow_right₀ hx (by norm_num : (1:ℕ) ≤ 4)
        simpa using h1
      exact mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 12)
    _ = (12 : ℝ) * (|t| + 3) ^ 4 := by norm_num


-- ############ R1: functional-equation machinery ############

/-- Gamma upper bound on the strip `3/4 ≤ x ≤ 2` with polynomial degree 2. -/
private lemma gamma_strip_poly2_pg {x t : ℝ} (hxlo : (3 / 4 : ℝ) ≤ x) (hx2 : x ≤ 2) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((x : ℂ) + I * (t : ℂ))‖ ≤
      (Commons.Analysis.Complex.Mbig * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) *
        (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
  have hx1' : x ≤ 1 ∨ 1 ≤ x := le_total x 1
  rcases hx1' with hx1 | hx1
  · -- x < 1 side (using ≤ to keep it simple: x ≤ 1)
    have hz_im : (((x : ℂ) + I * (t : ℂ)).im) = t := by simp
    have hle := Commons.Analysis.Complex.norm_Gamma_le_shift_nat ((x : ℂ) + I * (t : ℂ)) (k := 1)
      (by simpa [hz_im] using ht)
    have harg : (x : ℂ) + I * (t : ℂ) + (1 : ℂ) = ((x + 1 : ℝ) : ℂ) + I * (t : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    have hmain := Commons.Analysis.Complex.gamma_upper_main (hL11 := (by norm_num : (2 : ℝ) ≤ 11))
      (h1 := (show (1 : ℝ) ≤ x + 1 by linarith)) (hσL := (show x + 1 ≤ 2 by linarith)) t
    calc
      ‖Complex.Gamma ((x : ℂ) + I * (t : ℂ))‖ ≤
          ‖Complex.Gamma ((x : ℂ) + I * (t : ℂ) + (1 : ℂ))‖ := by simpa using hle
      _ = ‖Complex.Gamma (((x + 1 : ℝ) : ℂ) + I * (t : ℂ))‖ := by rw [harg]
      _ ≤ (Commons.Analysis.Complex.Mbig * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) *
            (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
            simpa [Real.rpow_natCast] using hmain
  · -- x ≥ 1
    have hmain := Commons.Analysis.Complex.gamma_upper_main (hL11 := (by norm_num : (2 : ℝ) ≤ 11))
      (h1 := hx1) (hσL := hx2) t
    simpa [Real.rpow_natCast] using hmain

/-- `‖cos (↑π * w / 2)‖ ≤ exp (π / 2 * |t|)` for `w = 1 - (σ + I*t)`. -/
private lemma cos_pi_two_bound_pg {σ t : ℝ} (w : ℂ) (hw : w = 1 - ((σ : ℂ) + I * (t : ℂ))) :
    ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
  have hcos : Complex.cos (↑Real.pi * w / 2) = Complex.sin (↑Real.pi * ((σ : ℂ) + I * (t : ℂ)) / 2) := by
    have h := Complex.sin_pi_div_two_sub (↑Real.pi * w / 2)
    -- h : sin (↑π / 2 - ↑π * w / 2) = cos (↑π * w / 2)
    rw [← h]
    congr 1
    -- need : ↑π / 2 - ↑π * w / 2 = ↑π * ((σ : ℂ) + I * (t : ℂ)) / 2
    rw [hw]
    ring
  rw [hcos]
  have hpi := Commons.Analysis.Complex.norm_sin_pi_le (((σ : ℂ) + I * (t : ℂ)) / 2)
  -- hpi : ‖sin (↑π * (((σ : ℂ) + I*t) / 2))‖ ≤ exp (π * |((σ : ℂ) + I*t) / 2).im|
  have hsimp : ‖Complex.sin (↑Real.pi * (((σ : ℂ) + I * (t : ℂ)) / 2))‖ =
      ‖Complex.sin (↑Real.pi * ((σ : ℂ) + I * (t : ℂ)) / 2)‖ := by
    congr 1
    ring
  have him : |((((σ : ℂ) + I * (t : ℂ)) / 2).im)| = |t| / 2 := by
    have h1 : ((((σ : ℂ) + I * (t : ℂ)) / 2).im) = t / 2 := by simp
    rw [h1]
    rw [abs_div]
    simp
  rw [← hsimp]
  calc
    ‖Complex.sin (↑Real.pi * (((σ : ℂ) + I * (t : ℂ)) / 2))‖ ≤
        Real.exp (Real.pi * |(((σ : ℂ) + I * (t : ℂ)) / 2).im|) := by simpa using hpi
    _ = Real.exp ((Real.pi / 2) * |t|) := by
      rw [him]
      congr 1
      ring

/-- zeta growth on `3/4 ≤ Re ≤ 2`, degree 1. -/
private theorem zeta_strip_threeQuarter_two_pg :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10000000 ∧ ∀ (u t : ℝ), (3 / 4 : ℝ) ≤ u → u ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((u : ℂ) + I * (t : ℂ))‖ ≤ C * (|t| + 3) := by
  rcases zeta_strip_growth_b with ⟨C0, hC0, hC0le, hC0spec⟩
  refine ⟨5 * C0, mul_pos (by norm_num) hC0, by linarith, ?_⟩
  intro u t hu h2 ht
  have hb := hC0spec (1 / 4) u t (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) (by linarith : (1 / 2 + 1 / 4 : ℝ) ≤ u) h2 ht
  -- hb : ‖ζ(u+it)‖ ≤ C0 * (1 + 1 / (1/4)) * (|t| + 3) ^ (1/2 - (1/4)/2)
  have hpow : (|t| + 3) ^ ((1 / 2 - (1 / 4) / 2 : ℝ)) ≤ |t| + 3 := by
    have hx : 1 ≤ |t| + 3 := by nlinarith [ht]
    have hle : ((1 / 2 - (1 / 4) / 2 : ℝ) ≤ 1) := by norm_num
    calc
      (|t| + 3) ^ ((1 / 2 - (1 / 4) / 2 : ℝ)) ≤ (|t| + 3) ^ (1 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hx hle
      _ = |t| + 3 := by rw [Real.rpow_one]
  have hb' : ‖riemannZeta ((u : ℂ) + I * (t : ℂ))‖ ≤ C0 * (1 + 1 / (1 / 4)) * (|t| + 3) := by
    calc
      ‖riemannZeta ((u : ℂ) + I * (t : ℂ))‖ ≤ C0 * (1 + 1 / (1 / 4)) * (|t| + 3) ^ ((1 / 2 - (1 / 4) / 2 : ℝ)) := hb
      _ ≤ C0 * (1 + 1 / (1 / 4)) * (|t| + 3) := by
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_of_lt hC0) (by norm_num : (0 : ℝ) ≤ 1 + 1 / (1 / 4)))
  calc
    ‖riemannZeta ((u : ℂ) + I * (t : ℂ))‖ ≤ C0 * (1 + 1 / (1 / 4)) * (|t| + 3) := hb'
    _ ≤ (5 * C0) * (|t| + 3) := by
      have hf : C0 * (1 + 1 / (1 / 4)) ≤ 5 * C0 := by
        have : (1 + 1 / (1 / 4) : ℝ) = 5 := by norm_num
        nlinarith
      have hx0 : 0 ≤ |t| + 3 := by positivity
      nlinarith


/-- Region lemma 1 (`-1 ≤ σ ≤ 1/4`): functional equation + Gamma bounds. -/
private theorem zeta_left_poly_pg :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 20 ∧ ∀ (σ t : ℝ), -1 ≤ σ → σ ≤ 1 / 4 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4 := by
  rcases zeta_strip_threeQuarter_two_pg with ⟨C34, hC34pos, hC34le, hC34spec⟩
  let G2 : ℝ := Commons.Analysis.Complex.Mbig * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)
  have hM : 0 < Commons.Analysis.Complex.Mbig := by
    dsimp [Commons.Analysis.Complex.Mbig]
    positivity
  have hG2pos : 0 < G2 := by
    dsimp [G2]
    exact mul_pos (mul_pos hM (Real.exp_pos 1))
      (Real.rpow_pos_of_pos (by positivity : 0 < Real.pi / 2) (2 : ℝ))
  refine ⟨2 * G2 * C34, by positivity, ?_, ?_⟩
  · have hMbig : Commons.Analysis.Complex.Mbig = (10 : ℝ) ^ 11 := rfl
    have hexp : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have hpi2 : (Real.pi / 2) ^ (2 : ℝ) ≤ 4 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h : Real.pi / 2 ≤ 2 := by have := Real.pi_lt_four; linarith
      calc (Real.pi / 2) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) h 2
        _ = 4 := by norm_num
    have h1 : Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ) ≤ 12 := by
      have h2 : Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ) ≤ 3 * 4 :=
        mul_le_mul hexp hpi2 (Real.rpow_nonneg (by positivity) _) (by norm_num)
      linarith
    have hG2le : G2 ≤ 1.3 * 10 ^ 12 := by
      dsimp only [G2]
      rw [hMbig]
      calc (10 : ℝ) ^ 11 * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)
          = (10 : ℝ) ^ 11 * (Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) := by ring
        _ ≤ 10 ^ 11 * 12 := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ 1.3 * 10 ^ 12 := by norm_num
    nlinarith [hG2le, hC34le]
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let u : ℝ := 1 - σ
  let w : ℂ := 1 - s
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  have hu_ge : (3 / 4 : ℝ) ≤ u := by dsimp [u]; linarith
  have hu_le : u ≤ 2 := by dsimp [u]; linarith
  have hwim : w.im = -t := by dsimp [w, s]; simp
  have hw_ne : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have him := congrArg Complex.im hn
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    norm_num at ht
  have hw1 : w ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    norm_num at ht
  have hFE0 := riemannZeta_one_sub (s := w) hw_ne hw1
  have hsw : s = 1 - w := by dsimp [w, s]; ring
  have hFE : riemannZeta s =
      2 * (2 * ↑Real.pi) ^ (-w) * Complex.Gamma w * Complex.cos (↑Real.pi * w / 2) * riemannZeta w := by
    simpa [hsw] using hFE0
  have htwon : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hwform : w = (u : ℂ) + I * ((-t : ℝ) : ℂ) := by
    dsimp [w, s, u]
    apply Complex.ext <;> simp <;> ring
  -- factor: (2π)^{-w}
  have hb2π : ((2 * Real.pi : ℝ) : ℂ) = (2 : ℂ) * ↑Real.pi := by
    rw [Complex.ofReal_mul]
    norm_num
  have hre : (-w).re = σ - 1 := by
    dsimp [w, s]
    simp
  have hpow2 : ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ = (2 * Real.pi : ℝ) ^ (σ - 1) := by
    rw [← hb2π]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (2 * Real.pi : ℝ)) (-w)]
    rw [hre]
  have hpow2le : ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ ≤ 1 := by
    rw [hpow2]
    have hx : 1 ≤ 2 * Real.pi := by
      have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      nlinarith
    have hle : σ - 1 ≤ 0 := by linarith
    calc
      (2 * Real.pi : ℝ) ^ (σ - 1) ≤ (2 * Real.pi : ℝ) ^ (0 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hx hle
      _ = 1 := by rw [Real.rpow_zero]
  -- factor: Gamma
  have hGn0 : ‖Complex.Gamma w‖ ≤
      G2 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
    have h := gamma_strip_poly2_pg (x := u) (t := -t) hu_ge hu_le (by simpa using ht)
    rw [hwform]
    simpa [G2] using h
  -- factor: cos
  have hcos : ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
    exact cos_pi_two_bound_pg w (by dsimp [w, s])
  -- factor: zeta at w
  have hzw0 : ‖riemannZeta w‖ ≤ C34 * (|t| + 3) := by
    have h := hC34spec u (-t) hu_ge hu_le (by simpa using ht)
    rw [hwform]
    simpa using h
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  let F : ℝ := Real.exp ((Real.pi / 2) * |t|)
  have hEe : E * F = 1 := by
    dsimp [E, F]
    rw [← Real.exp_add]
    rw [show (-(Real.pi / 2)) * |t| + (Real.pi / 2) * |t| = 0 by ring]
    rw [Real.exp_zero]
  have hGn : ‖Complex.Gamma w‖ ≤ G2 * (1 + |t|) ^ 2 * E := by simpa [E] using hGn0
  have hzw : ‖riemannZeta w‖ ≤ C34 * (|t| + 3) := hzw0
  have hmain : ‖riemannZeta s‖ ≤ 2 * G2 * C34 * (1 + |t|) ^ 2 * (|t| + 3) := by
    have hsplit : ‖riemannZeta s‖ =
        ‖(2 : ℂ)‖ * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
          ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := by
      rw [hFE]
      simp only [norm_mul]
    calc
      ‖riemannZeta s‖ = ‖(2 : ℂ)‖ * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
          ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := hsplit
      _ = 2 * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
          ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := by rw [htwon]
      _ ≤ 2 * 1 * (G2 * (1 + |t|) ^ 2 * E) * F * (C34 * (|t| + 3)) := by
        gcongr
      _ = 2 * G2 * C34 * (1 + |t|) ^ 2 * (|t| + 3) * (E * F) := by
        ring
      _ = 2 * G2 * C34 * (1 + |t|) ^ 2 * (|t| + 3) := by
        rw [hEe]
        ring
  have hconst0 : 0 ≤ 2 * G2 * C34 := by positivity
  have hmain3 : ‖riemannZeta s‖ ≤ 2 * G2 * C34 * (|t| + 3) ^ 3 := by
    have hq1 : (1 + |t|) ^ 2 ≤ (|t| + 3) ^ 2 := by
      have hx01 : 0 ≤ 1 + |t| := by positivity
      have hx1 : 1 + |t| ≤ |t| + 3 := by nlinarith
      exact pow_le_pow_left₀ hx01 hx1 2
    calc
      ‖riemannZeta s‖ ≤ 2 * G2 * C34 * (1 + |t|) ^ 2 * (|t| + 3) := hmain
      _ = 2 * G2 * C34 * ((1 + |t|) ^ 2 * (|t| + 3)) := by ring
      _ ≤ 2 * G2 * C34 * ((|t| + 3) ^ 2 * (|t| + 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hq1 (by positivity : 0 ≤ |t| + 3)) hconst0
      _ = 2 * G2 * C34 * (|t| + 3) ^ 3 := by ring_nf
  calc
    ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ = ‖riemannZeta s‖ := by simp [s]
    _ ≤ 2 * G2 * C34 * (|t| + 3) ^ 3 := hmain3
    _ ≤ (2 * G2 * C34) * (|t| + 3) ^ 4 := by
      have hx : 1 ≤ |t| + 3 := by nlinarith [ht]
      have hp : (|t| + 3) ^ 3 ≤ (|t| + 3) ^ 4 := pow_le_pow_right₀ hx (by norm_num : (3 : ℕ) ≤ 4)
      exact mul_le_mul_of_nonneg_left hp hconst0

/-- The requested theorem: uniform quartic growth on the strip `-1 ≤ σ ≤ 3`, `|t| ≥ 1`. -/
theorem zeta_strip_polyGrowth_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 25 ∧
      ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4 := by
  rcases zeta_left_poly_pg with ⟨C1, hC1, hC1le, hC1spec⟩
  rcases zeta_re_quarter_three_poly_pg with ⟨C2, hC2, hC2le, hC2spec⟩
  refine ⟨C1 + C2, add_pos hC1 hC2, by linarith, ?_⟩
  intro σ t hσlo hσhi ht
  by_cases hσ : σ ≤ 1 / 4
  · have hb := hC1spec σ t hσlo hσ ht
    calc
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C1 * (|t| + 3) ^ 4 := hb
      _ ≤ (C1 + C2) * (|t| + 3) ^ 4 := by
        have hx0 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        nlinarith
  · have hσ2 : (1 / 4 : ℝ) ≤ σ := by linarith
    have hb := hC2spec σ t hσ2 hσhi ht
    calc
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C2 * (|t| + 3) ^ 4 := hb
      _ ≤ (C1 + C2) * (|t| + 3) ^ 4 := by
        have hx0 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        nlinarith




/-- `‖cos (π * w / 2)‖ ≤ exp (π / 2 * |t|)` for `w = 1 - (σ + I*t)`. -/
private lemma cos_pi_two_bound_neg_pgn {σ t : ℝ} (w : ℂ) (hw : w = 1 - ((σ : ℂ) + I * (t : ℂ))) :
    ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
  have hcos : Complex.cos (↑Real.pi * w / 2) =
      Complex.sin (↑Real.pi * ((σ : ℂ) + I * (t : ℂ)) / 2) := by
    have h := Complex.sin_pi_div_two_sub (↑Real.pi * w / 2)
    rw [← h]
    congr 1
    rw [hw]
    ring
  rw [hcos]
  have hpi := Commons.Analysis.Complex.norm_sin_pi_le (((σ : ℂ) + I * (t : ℂ)) / 2)
  have hsimp : ‖Complex.sin (↑Real.pi * (((σ : ℂ) + I * (t : ℂ)) / 2))‖ =
      ‖Complex.sin (↑Real.pi * ((σ : ℂ) + I * (t : ℂ)) / 2)‖ := by
    congr 1
    ring
  have him : |((((σ : ℂ) + I * (t : ℂ)) / 2).im)| = |t| / 2 := by
    have h1 : ((((σ : ℂ) + I * (t : ℂ)) / 2).im) = t / 2 := by simp
    rw [h1]
    rw [abs_div]
    simp
  rw [← hsimp]
  calc
    ‖Complex.sin (↑Real.pi * (((σ : ℂ) + I * (t : ℂ)) / 2))‖ ≤
        Real.exp (Real.pi * |((((σ : ℂ) + I * (t : ℂ)) / 2)).im|) := by simpa using hpi
    _ = Real.exp ((Real.pi / 2) * |t|) := by
      rw [him]
      congr 1
      ring

/-- Zeta growth on the strip `-2 ≤ Re s ≤ -1`, `|t| ≥ 1`, polynomial bound of degree 12. -/
theorem zeta_strip_polyGrowth_neg_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 40 ∧
      ∀ σ t : ℝ, -2 ≤ σ → σ ≤ -1 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 12 := by
  rcases zeta_strip_polyGrowth_b with ⟨Cps, hCps, hCpsle, hCpsSpec⟩
  let K6 : ℝ := Commons.Analysis.Complex.K6
  have hK6 : 0 < K6 := by simpa [K6] using Commons.Analysis.Complex.K6_pos
  have hC : 0 < 2 * K6 * Cps := by positivity
  refine ⟨2 * K6 * Cps, hC, ?_, ?_⟩
  · have hMbig : Commons.Analysis.Complex.Mbig = (10 : ℝ) ^ 11 := rfl
    have hexp : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have hpi6 : (Real.pi / 2) ^ (6 : ℝ) ≤ 64 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h : Real.pi / 2 ≤ 2 := by have := Real.pi_lt_four; linarith
      calc (Real.pi / 2) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by positivity) h 6
        _ = 64 := by norm_num
    have hK6le : K6 ≤ 2 * 10 ^ 13 := by
      dsimp only [K6]
      have h1 : Real.exp 1 * (Real.pi / 2) ^ (6 : ℝ) ≤ 3 * 64 :=
        mul_le_mul hexp hpi6 (Real.rpow_nonneg (by positivity) _) (by norm_num)
      calc (10 : ℝ) ^ 11 * Real.exp 1 * (Real.pi / 2) ^ (6 : ℝ)
          = (10 : ℝ) ^ 11 * (Real.exp 1 * (Real.pi / 2) ^ (6 : ℝ)) := by ring
        _ ≤ 10 ^ 11 * 192 := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        _ ≤ 2 * 10 ^ 13 := by norm_num
    nlinarith [hK6le, hCpsle]
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let u : ℝ := 1 - σ
  let w : ℂ := 1 - s
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hu6 : u ≤ 6 := by dsimp [u]; linarith
  have hu_lo : -1 ≤ u := by dsimp [u]; linarith
  have hu_le3 : u ≤ 3 := by dsimp [u]; linarith
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  have hwim : w.im = -t := by dsimp [w, s]; simp
  have hw_ne : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have him := congrArg Complex.im hn
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    norm_num at ht
  have hw1 : w ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    norm_num at ht
  have hFE0 := riemannZeta_one_sub (s := w) hw_ne hw1
  have hsw : s = 1 - w := by dsimp [w, s]; ring
  have hFE : riemannZeta s =
      2 * (2 * ↑Real.pi) ^ (-w) * Complex.Gamma w * Complex.cos (↑Real.pi * w / 2) *
        riemannZeta w := by
    simpa [hsw] using hFE0
  have htwon : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hwform : w = (u : ℂ) + I * ((-t : ℝ) : ℂ) := by
    dsimp [w, s, u]
    apply Complex.ext <;> simp <;> ring
  -- factor: (2π)^{-w}
  have hb2π : ((2 * Real.pi : ℝ) : ℂ) = (2 : ℂ) * ↑Real.pi := by
    rw [Complex.ofReal_mul]
    norm_num
  have hre : (-w).re = σ - 1 := by dsimp [w, s]; simp
  have hpow2 : ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ = (2 * Real.pi : ℝ) ^ (σ - 1) := by
    rw [← hb2π]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (2 * Real.pi : ℝ)) (-w)]
    rw [hre]
  have hpow2le : ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ ≤ 1 := by
    rw [hpow2]
    have hx : 1 ≤ 2 * Real.pi := by
      have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      nlinarith
    have hle : σ - 1 ≤ 0 := by linarith
    calc
      (2 * Real.pi : ℝ) ^ (σ - 1) ≤ (2 * Real.pi : ℝ) ^ (0 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hx hle
      _ = 1 := by rw [Real.rpow_zero]
  -- factor: Gamma
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  let F : ℝ := Real.exp ((Real.pi / 2) * |t|)
  have hEe : E * F = 1 := by
    dsimp [E, F]
    rw [← Real.exp_add]
    rw [show (-(Real.pi / 2)) * |t| + (Real.pi / 2) * |t| = 0 by ring]
    rw [Real.exp_zero]
  have hGn : ‖Complex.Gamma w‖ ≤ K6 * (1 + |t|) ^ (6 : ℝ) * E := by
    have h := Commons.Analysis.Complex.gamma_strip_upper u (-t) hu_pos hu6 (by simpa using ht)
    rw [hwform]
    simpa [E] using h
  -- factor: cos
  have hcos : ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ F := by
    have hb := cos_pi_two_bound_neg_pgn w (by dsimp [w, s])
    simpa [F] using hb
  -- factor: zeta at w
  have hzw : ‖riemannZeta w‖ ≤ Cps * (|t| + 3) ^ 4 := by
    have h := hCpsSpec u (-t) hu_lo hu_le3 (by simpa using ht)
    rw [hwform]
    simpa using h
  have hmain : ‖riemannZeta s‖ ≤ 2 * K6 * Cps * (1 + |t|) ^ (6 : ℝ) * (|t| + 3) ^ 4 := by
    have hsplit : ‖riemannZeta s‖ =
        ‖(2 : ℂ)‖ * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
          ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := by
      rw [hFE]
      simp only [norm_mul]
    calc
      ‖riemannZeta s‖ =
          ‖(2 : ℂ)‖ * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
            ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := hsplit
      _ = 2 * ‖((2 : ℂ) * ↑Real.pi) ^ (-w)‖ * ‖Complex.Gamma w‖ *
            ‖Complex.cos (↑Real.pi * w / 2)‖ * ‖riemannZeta w‖ := by rw [htwon]
      _ ≤ 2 * 1 * (K6 * (1 + |t|) ^ (6 : ℝ) * E) * F * (Cps * (|t| + 3) ^ 4) := by
        gcongr
      _ = 2 * K6 * Cps * (1 + |t|) ^ (6 : ℝ) * (|t| + 3) ^ 4 * (E * F) := by
        ring
      _ = 2 * K6 * Cps * (1 + |t|) ^ (6 : ℝ) * (|t| + 3) ^ 4 := by
        rw [hEe]
        ring
  have hconst0 : 0 ≤ 2 * K6 * Cps := le_of_lt hC
  have hmain' : ‖riemannZeta s‖ ≤ 2 * K6 * Cps * (1 + |t|) ^ 6 * (|t| + 3) ^ 4 := by
    simpa [Real.rpow_natCast] using hmain
  have hmain10 : ‖riemannZeta s‖ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 10 := by
    calc
      ‖riemannZeta s‖ ≤ 2 * K6 * Cps * (1 + |t|) ^ 6 * (|t| + 3) ^ 4 := hmain'
      _ = 2 * K6 * Cps * ((1 + |t|) ^ 6 * (|t| + 3) ^ 4) := by ring
      _ ≤ 2 * K6 * Cps * ((|t| + 3) ^ 6 * (|t| + 3) ^ 4) := by
        have hq : (1 + |t|) ^ 6 ≤ (|t| + 3) ^ 6 := by
          exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t|)
            (by nlinarith : 1 + |t| ≤ |t| + 3) 6
        have hq4 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hq4) hconst0
      _ = (2 * K6 * Cps) * (|t| + 3) ^ 10 := by
        rw [← pow_add]
  have ht13 : 1 ≤ |t| + 3 := by nlinarith [ht]
  have hfin : ‖riemannZeta s‖ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 12 := by
    calc
      ‖riemannZeta s‖ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 10 := hmain10
      _ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 12 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht13 (by norm_num : (10 : ℕ) ≤ 12)) hconst0
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ = ‖riemannZeta s‖ := by simp [s]
    _ ≤ (2 * K6 * Cps) * (|t| + 3) ^ 12 := hfin





/-- The `n`th term of the Dirichlet series for `ζ(s)` (shifted to start at `1`) has norm
`(n+1) ^ (-s.re)`. -/
private lemma norm_one_div_nat_add_one_cpow_nc (n : ℕ) (s : ℂ) :
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcast : (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by norm_num
  calc
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ‖(((n + 1 : ℕ) : ℂ) ^ s)⁻¹‖ := by simp [one_div]
    _ = ‖(((n + 1 : ℕ) : ℂ) ^ s)‖⁻¹ := by rw [norm_inv]
    _ = (((n + 1 : ℕ) : ℝ) ^ s.re)⁻¹ := by
      rw [hcast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 s]
    _ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
      rw [Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]

/-- Termwise bound: for `3 ≤ s.re`, the norm of the `n`th Dirichlet-series summand of `ζ(s)`
is at most `(n+1) ^ (-3)`. -/
private lemma zeta_term_norm_le_nc (s : ℂ) (hs : 3 ≤ s.re) (n : ℕ) :
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
  have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hneg : -s.re ≤ -3 := by linarith
  calc
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      norm_one_div_nat_add_one_cpow_nc n s
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hneg

/-- The real `p`-series `∑' n, (n+1) ^ (-3)` converges. -/
private lemma summable_nat_add_one_rpow_neg_three_nc :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hh : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) 1).mpr hnat
  exact hh

/-- Dirichlet-series bound: for `3 ≤ s.re` the series value `ζ(s)` is bounded by the
convergent real `p`-series `∑' n, (n+1) ^ (-3)`. -/
private lemma zeta_norm_le_tsum_nc (s : ℂ) (hs : 3 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
  have hs1 : 1 < s.re := by linarith
  let f : ℕ → ℂ := fun n => 1 / (((n + 1 : ℕ) : ℂ) ^ s)
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)
  have hzeta : riemannZeta s = ∑' n : ℕ, f n := by
    simpa [f] using zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hsum_g : Summable g := by
    simpa [g] using summable_nat_add_one_rpow_neg_three_nc
  have hterm : ∀ n : ℕ, ‖f n‖ ≤ g n := by
    intro n
    simpa [f, g] using zeta_term_norm_le_nc s hs n
  have hsum_norm : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum_g
  calc
    ‖riemannZeta s‖ = ‖∑' n : ℕ, f n‖ := by rw [hzeta]
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hsum_norm hsum_g

/-- The Riemann zeta function is bounded on the half-plane of real part at least `3`. -/
private lemma tsum_cube_le_two_nc : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) ≤ 2 := by
  have hS : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) :=
    summable_nat_add_one_rpow_neg_three_nc
  have hsplit := hS.tsum_eq_zero_add
  rw [hsplit]
  have hf0 : ((0 + 1 : ℕ) : ℝ) ^ (-3 : ℝ) = 1 := by norm_num
  rw [hf0]
  have htail : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) ≤ 1 / 2 := by
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-3 : ℝ)) (Set.Ici ((1 : ℕ) : ℝ)) := by
      intro a ha b _ hab
      have ha1 : (1 : ℝ) ≤ a := by simpa using Set.mem_Ici.mp ha
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by norm_num)
    have hint : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Set.Ioi ((1 : ℕ) : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3:ℝ)) < -1) (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
    have hnn : ∀ t ∈ Set.Ioi (((1 : ℕ)) : ℝ), 0 ≤ t ^ (-3 : ℝ) :=
      fun t ht => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _
    have hb := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-3 : ℝ)) 1 hanti hint hnn
    have hiv : ∫ x in Set.Ioi (((1 : ℕ)) : ℝ), x ^ (-3 : ℝ) = 1 / 2 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3:ℝ)) < -1) (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))]
      norm_num
    rw [hiv] at hb
    simpa only [Nat.cast_add, Nat.cast_one] using hb
  linarith

theorem zeta_norm_le_const_three_le_re_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ∧ ∀ s : ℂ, 3 ≤ s.re → ‖riemannZeta s‖ ≤ C := by
  let C : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)
  refine ⟨C, ?_, ?_, ?_⟩
  · show 0 < C
    unfold C
    have hsum_g : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) :=
      summable_nat_add_one_rpow_neg_three_nc
    have hts := Summable.tsum_eq_zero_add (f := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ))
      hsum_g
    have hg0 : ((0 + 1 : ℕ) : ℝ) ^ (-3 : ℝ) = 1 := by norm_num
    have hnonneg : 0 ≤ ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
      apply tsum_nonneg
      intro n
      have hb : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by positivity
      exact le_of_lt (Real.rpow_pos_of_pos hb _)
    rw [hts, hg0]
    linarith
  · exact tsum_cube_le_two_nc
  · intro s hs
    show ‖riemannZeta s‖ ≤ C
    simpa [C] using zeta_norm_le_tsum_nc s hs




/-- For `w ≠ 1`, `‖riemannZeta₁ w‖ = ‖w - 1‖ · ‖riemannZeta w‖`. -/
private lemma zeta1_norm_eq_mul_d4_gd (w : ℂ) (hw : w ≠ 1) :
    ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
  have h1 : (w - 1) * riemannZeta w = riemannZeta₁ w := by
    calc
      (w - 1) * riemannZeta w = (w - 1) * ((w - 1)⁻¹ * riemannZeta₁ w) := by
        rw [riemannZeta_eq_inv_sub_mul hw]
      _ = riemannZeta₁ w := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hw)]
        simp
  calc
    ‖riemannZeta₁ w‖ = ‖(w - 1) * riemannZeta w‖ := by rw [← h1]
    _ = ‖w - 1‖ * ‖riemannZeta w‖ := by rw [norm_mul]

/-- Polynomial growth of `riemannZeta₁` on the closed disk of radius `4` about `2 + I*t`,
for `|t| ≥ 5`. The disk has real part in `[-2,6]` and imaginary part within `4` of `t`,
so it is covered by the left strip bounds on `ζ` and the half-plane `re ≥ 3`. -/
theorem zeta1_growth_disk4_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 40 ∧ ∀ t : ℝ, 5 ≤ |t| → ∀ w : ℂ,
      ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ 4 → ‖riemannZeta₁ w‖ ≤ C * (|t| + 7) ^ 15 := by
  rcases zeta_strip_polyGrowth_b with ⟨Cpg, hCpg0, hCpgle, hCpg⟩
  rcases zeta_strip_polyGrowth_neg_b with ⟨Cng, hCng0, hCngle, hCng⟩
  rcases zeta_norm_le_const_three_le_re_b with ⟨C3, hC30, hC3le, hC3⟩
  refine ⟨max Cpg (max Cng C3), lt_max_of_lt_left hCpg0, ?_, ?_⟩
  · exact max_le (le_trans hCpgle (by norm_num)) (max_le hCngle (by linarith))
  intro t ht w hball
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hball' : ‖w - c‖ ≤ 4 := hball
  have hσdist : |w.re - 2| ≤ ‖w - c‖ := by
    have h := Complex.abs_re_le_norm (w - c)
    simpa [c] using h
  have hτdist : |w.im - t| ≤ ‖w - c‖ := by
    have h := Complex.abs_im_le_norm (w - c)
    simpa [c] using h
  have hσ4 : |w.re - 2| ≤ 4 := le_trans hσdist hball'
  have hτ4 : |w.im - t| ≤ 4 := le_trans hτdist hball'
  have hσlo : -2 ≤ w.re := by have h := (abs_le.mp hσ4).1; linarith
  have hτge : 1 ≤ |w.im| := by
    have h2 : |t| ≤ |w.im| + |w.im - t| := by
      calc |t| = |w.im + (t - w.im)| := by congr 1; ring
        _ ≤ |w.im| + |t - w.im| := abs_add_le _ _
        _ = |w.im| + |w.im - t| := by rw [abs_sub_comm]
    linarith
  have hτhi : |w.im| ≤ |t| + 4 := by
    have h2 : |w.im| ≤ |w.im - t| + |t| := by
      calc |w.im| = |(w.im - t) + t| := by congr 1; ring
        _ ≤ |w.im - t| + |t| := abs_add_le _ _
    linarith
  have hw_ne1 : w ≠ 1 := by
    intro hw1
    have hle : ‖(1 : ℂ) - c‖ ≤ 4 := by
      have h' : ‖w - c‖ ≤ 4 := hball'
      rw [hw1] at h'
      exact h'
    have him : |t| ≤ ‖(1 : ℂ) - c‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - c)
      have hval : ((1 : ℂ) - c).im = -t := by simp only [c]; simp
      rw [hval, abs_neg] at h
      exact h
    linarith
  have hζ : ‖riemannZeta w‖ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 := by
    have hwform : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
      apply Complex.ext <;> simp
    have hbase : (1 : ℝ) ≤ |w.im| + 3 := by linarith [abs_nonneg w.im]
    have hEqZeta : riemannZeta w = riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ)) :=
      congrArg riemannZeta hwform
    by_cases hσ3 : w.re ≤ 3
    · by_cases hσm1 : -1 ≤ w.re
      · have h := hCpg w.re w.im hσm1 hσ3 hτge
        have hpow : (|w.im| + 3) ^ 4 ≤ (|w.im| + 3) ^ 12 :=
          pow_le_pow_right₀ hbase (by norm_num)
        calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ := by
              rw [hEqZeta]
          _ ≤ Cpg * (|w.im| + 3) ^ 4 := h
          _ ≤ Cpg * (|w.im| + 3) ^ 12 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCpg0)
          _ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · have hσm1' : w.re ≤ -1 := le_of_lt (lt_of_not_ge hσm1)
        have h := hCng w.re w.im hσlo hσm1' hτge
        have hCng_le : Cng ≤ max Cpg (max Cng C3) :=
          le_trans (le_max_left Cng C3) (le_max_right Cpg (max Cng C3))
        calc ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ))‖ := by
              rw [hEqZeta]
          _ ≤ Cng * (|w.im| + 3) ^ 12 := h
          _ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 :=
              mul_le_mul_of_nonneg_right hCng_le (by positivity)
    · have hσ3' : 3 ≤ w.re := le_of_lt (lt_of_not_ge hσ3)
      have h := hC3 w hσ3'
      have hC3_le : C3 ≤ max Cpg (max Cng C3) :=
        le_trans (le_max_right Cng C3) (le_max_right Cpg (max Cng C3))
      have hge1 : (1 : ℝ) ≤ (|w.im| + 3) ^ 12 := one_le_pow₀ hbase
      calc ‖riemannZeta w‖ ≤ C3 := h
        _ = C3 * 1 := by ring
        _ ≤ C3 * (|w.im| + 3) ^ 12 := mul_le_mul_of_nonneg_left hge1 (le_of_lt hC30)
        _ ≤ max Cpg (max Cng C3) * (|w.im| + 3) ^ 12 :=
            mul_le_mul_of_nonneg_right hC3_le (by positivity)
  have hc1 : ‖c - 1‖ ≤ 1 + |t| := by
    have hrew : c - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by
      simp only [c]; ring
    rw [hrew]
    calc ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
          norm_add_le _ _
      _ = 1 + |t| := by
        rw [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        ring
  have hw1le : ‖w - 1‖ ≤ |t| + 6 := by
    have hsum : (w - c) + (c - 1) = w - 1 := by ring
    calc ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by rw [← hsum]
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 4 + (1 + |t|) := by linarith
      _ ≤ |t| + 6 := by linarith
  have hCz0 : 0 < max Cpg (max Cng C3) := lt_max_of_lt_left hCpg0
  have hτ_le : |w.im| + 3 ≤ |t| + 7 := by linarith
  have hpow : (|w.im| + 3) ^ 12 ≤ (|t| + 7) ^ 12 :=
    pow_le_pow_left₀ (by positivity) hτ_le 12
  have ht7nn : 0 ≤ |t| + 7 := by linarith [abs_nonneg t]
  calc ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := zeta1_norm_eq_mul_d4_gd w hw_ne1
    _ ≤ (|t| + 6) * (max Cpg (max Cng C3) * (|w.im| + 3) ^ 12) :=
        mul_le_mul hw1le hζ (by positivity) (by positivity)
    _ ≤ (|t| + 7) * (max Cpg (max Cng C3) * (|w.im| + 3) ^ 12) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) (by positivity)
    _ ≤ (|t| + 7) * (max Cpg (max Cng C3) * (|t| + 7) ^ 12) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hCz0)) (by linarith [abs_nonneg t])
    _ = max Cpg (max Cng C3) * (|t| + 7) ^ 13 := by ring
    _ ≤ max Cpg (max Cng C3) * (|t| + 7) ^ 15 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hCz0)
        exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)




/-- `1/(m+2) - 1/(m+3) = 1/((m+2)(m+3))`. -/
private lemma telescoping_term_eq_lr (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) = 1 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
  field_simp
  ring_nf

/-- The telescoping differences are nonnegative. -/
private lemma telescoping_term_nonneg_lr (m : ℕ) :
    0 ≤ (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) := by
  rw [telescoping_term_eq_lr]
  exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 2) (by positivity : 0 ≤ (m : ℝ) + 3))

/-- `1/((m+2)(m+3)) ≤ 1/(m+2)^2`. -/
private lemma telescoping_term_le_lr (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) ≤ 1 / ((m : ℝ) + 2) ^ 2 := by
  rw [telescoping_term_eq_lr]
  have hle : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 2) * ((m : ℝ) + 3) := by nlinarith
  exact one_div_le_one_div_of_le (by positivity : 0 < ((m : ℝ) + 2) ^ 2) hle

/-- Summability of the telescoping differences. -/
private lemma summable_telescoping_lr :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3)) := by
  have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hps2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 2) ^ 2) := by
    have hs : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 2)) :=
      (summable_nat_add_iff 2).mpr hps
    simpa [Nat.cast_add] using hs
  exact Summable.of_nonneg_of_le (fun m => telescoping_term_nonneg_lr m) (fun m => telescoping_term_le_lr m) hps2

/-- `∑' m, (1/(m+2) - 1/(m+3)) = 1/2`, by telescoping. -/
private lemma tsum_telescoping_lr :
    (∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3))) = 1 / 2 := by
  let a : ℕ → ℝ := fun i => 1 / ((i + 2 : ℕ) : ℝ)
  have ha (i : ℕ) : a i - a (i + 1) = (1 : ℝ) / ((i : ℝ) + 2) - 1 / ((i : ℝ) + 3) := by
    unfold a
    have h₁ : (i + 1 + 2 : ℕ) = i + 3 := by omega
    rw [h₁]
    norm_num [Nat.cast_add]
  have hsum : Summable (fun i : ℕ => a i - a (i + 1)) := by
    exact summable_telescoping_lr.congr (fun i => (ha i).symm)
  have htend : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (a i - a (i + 1))) atTop (𝓝 (1 / 2)) := by
    have htelesc : ∀ N : ℕ, (∑ i ∈ Finset.range N, (a i - a (i + 1))) = a 0 - a N :=
      Finset.sum_range_sub' a
    have hN0 : Tendsto (fun N : ℕ => a N) atTop (𝓝 0) := by
      unfold a
      have hc : Tendsto (fun N : ℕ => (((N + 2 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
        (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2))
      simpa [one_div] using hc
    have hconst : Tendsto (fun _ : ℕ => a 0) atTop (𝓝 (a 0)) := tendsto_const_nhds
    have hsub : Tendsto (fun N : ℕ => a 0 - a N) atTop (𝓝 (a 0 - 0)) := hconst.sub hN0
    have hcong : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (a i - a (i + 1))) atTop (𝓝 (a 0 - 0)) :=
      hsub.congr' (Filter.Eventually.of_forall (fun N => (htelesc N).symm))
    simpa [a] using hcong
  have h := (Summable.hasSum_iff_tendsto_nat hsum).2 htend
  have hEqFun : (fun i : ℕ => a i - a (i + 1)) =
      fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) := by
    funext i
    exact ha i
  have h' : HasSum (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3)) (1 / 2) := by
    simpa [hEqFun] using h
  exact h'.tsum_eq

/-- `1/((m+3)^2) ≤ 1/((m+2)(m+3))`, the termwise comparison. -/
private lemma sq_tail_term_le_lr (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 3) ^ 2 ≤ 1 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
  have hle : ((m : ℝ) + 2) * ((m : ℝ) + 3) ≤ ((m : ℝ) + 3) ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (by positivity : 0 < ((m : ℝ) + 2) * ((m : ℝ) + 3)) hle

/-- `∑' m, 1 / (m+3)^2 ≤ 1 / 2`. -/
private lemma tsum_sq_tail_le_half_lr :
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2) ≤ 1 / 2 := by
  have hterm : ∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2 ≤
      (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) := by
    intro m
    rw [telescoping_term_eq_lr m]
    exact sq_tail_term_le_lr m
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 3) ^ 2) := by
    have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have hs : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 3)) :=
      (summable_nat_add_iff 3).mpr hps
    simpa [Nat.cast_add, add_assoc] using hs
  calc
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2)
        ≤ ∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3)) :=
          Summable.tsum_le_tsum hterm hsum summable_telescoping_lr
    _ = 1 / 2 := tsum_telescoping_lr

/-- `∑' m, 1 / (m+2)^2 ≤ 3 / 4`. -/
private lemma tsum_inv_sq_shift_le_three_quarters_lr :
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2) ≤ 3 / 4 := by
  have hsplit : (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2) =
      (1 : ℝ) / 4 + ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2 := by
    let g : ℕ → ℝ := fun m => (1 : ℝ) / ((m : ℝ) + 2) ^ 2
    have hsumg : Summable g := by
      have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      have hs : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 2)) :=
        (summable_nat_add_iff 2).mpr hps
      refine hs.congr ?_
      intro n
      have h₁ : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by norm_num
      simp [g, h₁]
    have hsplit := Summable.tsum_eq_zero_add hsumg
    change (∑' m : ℕ, g m) = (1 : ℝ) / 4 + ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2
    rw [hsplit]
    congr 1
    · norm_num [g]
    · apply tsum_congr
      intro m
      have h₁ : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
      simp [g, h₁]
      ring_nf
  calc
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2) = (1 : ℝ) / 4 + ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2 := hsplit
    _ ≤ (1 : ℝ) / 4 + 1 / 2 := by
      have ht := tsum_sq_tail_le_half_lr
      linarith
    _ = 3 / 4 := by norm_num

/-- `riemannZeta s = 1 + ∑' m, (m+2)^(-s)` for `1 < s.re`. -/
private lemma zeta_eq_one_add_tail_lr {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (1 : ℂ) + ∑' m : ℕ, 1 / (((m + 2 : ℕ) : ℂ) ^ s) := by
  let f : ℕ → ℂ := fun n => 1 / (((n + 1 : ℕ) : ℂ) ^ s)
  have hbase : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow).mpr hs
  have hsumf : Summable f := by
    have hshift : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℂ) ^ s) (n + 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    exact hshift.congr (fun n => rfl)
  calc
    riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
      zeta_eq_tsum_one_div_nat_add_one_cpow hs
    _ = ∑' n : ℕ, f n := by
      apply tsum_congr
      intro n
      have hb : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) := by norm_num
      rw [hb]
    _ = f 0 + ∑' m : ℕ, f (m + 1) := Summable.tsum_eq_zero_add hsumf
    _ = (1 : ℂ) + ∑' m : ℕ, 1 / (((m + 2 : ℕ) : ℂ) ^ s) := by
      congr 1
      · simp [f, Complex.one_cpow]

/-- Norm of the shifted terms on the line `re s = 2`. -/
private lemma norm_sq_term_lr {s : ℂ} (hsre : s.re = 2) (m : ℕ) :
    ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ = (1 : ℝ) / ((m : ℝ) + 2) ^ 2 := by
  have hpos : 0 < (m + 2 : ℕ) := by omega
  rw [norm_div, norm_one]
  rw [Complex.norm_natCast_cpow_of_pos hpos]
  rw [hsre]
  rw [Real.rpow_two]
  norm_num [Nat.cast_add]

/-- On the line `re s = 2` the shifted tail has norm at most `3/4`. -/
private lemma tail_norm_le_three_quarters_lr {s : ℂ} (hsre : s.re = 2) :
    (∑' m : ℕ, ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖) ≤ 3 / 4 := by
  calc
    (∑' m : ℕ, ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖)
        = ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2 := by
          apply tsum_congr
          intro m
          exact norm_sq_term_lr hsre m
    _ ≤ 3 / 4 := tsum_inv_sq_shift_le_three_quarters_lr


/-- On the vertical line `re s = 2`, the zeta function has norm at least `1/4`. -/
private theorem zeta_norm_re_two_lower_quarter_lr (T : ℝ) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hsre : s.re = 2 := by simp [s]
  have hs1 : 1 < s.re := by rw [hsre]; norm_num
  have htail_le : ‖∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ ≤ 3 / 4 := by
    calc
      ‖∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖
          ≤ ∑' m : ℕ, ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ := by
            apply norm_tsum_le_tsum_norm
            -- Summable (fun m => ‖(1:ℂ)/(((m+2:ℕ):ℂ)^s)‖)
            have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
              (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
            have hs2 : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 2)) :=
              (summable_nat_add_iff 2).mpr hps
            have hfeq : (fun m : ℕ => ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖) =
                fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) ^ 2 := by
              funext m
              exact norm_sq_term_lr hsre m
            rw [hfeq]
            simpa [Nat.cast_add] using hs2
      _ ≤ 3 / 4 := tail_norm_le_three_quarters_lr hsre
  have hzeta : riemannZeta s = (1 : ℂ) + ∑' m : ℕ, 1 / (((m + 2 : ℕ) : ℂ) ^ s) :=
    zeta_eq_one_add_tail_lr hs1
  have htri : (1 : ℝ) - ‖∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ ≤
      ‖(1 : ℂ) + ∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ := by
    let z : ℂ := ∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)
    have hz : (1 : ℝ) ≤ ‖(1 : ℂ) + z‖ + ‖z‖ := by
      have hh := norm_sub_le ((1 : ℂ) + z) z
      simpa using hh
    dsimp [z] at hz
    linarith
  have hfinal : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := by
    rw [hzeta]
    have h1 : (1 : ℝ) / 4 ≤ ‖(1 : ℂ) + ∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ := by
      linarith
    simpa using h1
  simpa [s] using hfinal

/-- `riemannZeta₁` is bounded away from zero on the vertical line `re s = 2`:
`‖ζ₁ (2 + i t)‖ ≥ 1/4` for every real `t`. -/
theorem zeta1_re_two_lower_lr (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta₁ ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  set s : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hsdef
  have hsre : s.re = 2 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = (1 : ℂ).re := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  have hrel : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    calc
      riemannZeta₁ s = (s - 1) * ((s - 1)⁻¹ * riemannZeta₁ s) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
      _ = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hs1]
  have hsm1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre1 : (s - 1).re = 1 := by dsimp [s]; norm_num
    have hle : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
    rw [hre1] at hle
    have : |(1 : ℝ)| = (1 : ℝ) := by norm_num
    rwa [this] at hle
  have hz : (1 / 4 : ℝ) ≤ ‖riemannZeta s‖ := by
    simpa [s] using (zeta_norm_re_two_lower_quarter_lr t)
  have hnorm : ‖riemannZeta₁ s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by
    rw [hrel, norm_mul]
  simpa [s] using
    (calc
      (1 / 4 : ℝ) ≤ ‖riemannZeta s‖ := hz
      _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := le_mul_of_one_le_left (norm_nonneg _) hsm1
      _ = ‖riemannZeta₁ s‖ := hnorm.symm)

theorem zeta_lower_re_two_b :
    ∃ c : ℝ, 1 / 8 ≤ c ∧ c ≤ (1 : ℝ) / 4 ∧ ∀ T : ℝ,
      c ≤ ‖riemannZeta ((2 : ℂ) + Complex.I * (T : ℂ))‖ :=
  ⟨1 / 4, by norm_num, by norm_num, fun T => zeta_norm_re_two_lower_quarter_lr T⟩




/-- A point of the circle of radius 4 centred at `c = 2 + i·t` has real part in `[-2, 6]`,
imaginary part at least `1` in absolute value, and `|im| ≤ |t| + 4`. -/
private lemma sphere4_re_im_bd {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.sphere ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    -2 ≤ z.re ∧ z.re ≤ 6 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ |t| + 4 := by
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  change z ∈ Metric.sphere c 4 at hz
  have hd : dist z c = (4 : ℝ) := by simpa using (Metric.mem_sphere.mp hz)
  have hnorm : ‖z - c‖ = (4 : ℝ) := by simpa [dist_eq_norm] using hd
  have hre_abs : |z.re - 2| ≤ 4 := by
    calc
      |z.re - 2| = |(z - c).re| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
      _ = 4 := hnorm
  have him_abs : |z.im - t| ≤ 4 := by
    calc
      |z.im - t| = |(z - c).im| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_im_le_norm (z - c)
      _ = 4 := hnorm
  have habs := abs_le.mp hre_abs
  have him_bounds := abs_le.mp him_abs
  have hzge : t - 4 ≤ z.im := by linarith
  have hzle : z.im ≤ t + 4 := by linarith
  have ht_im_lo : 1 ≤ |z.im| := by
    by_cases ht0 : 0 ≤ t
    · have ht5 : 5 ≤ t := by
        have htn : |t| = t := abs_of_nonneg ht0
        rwa [htn] at ht
      have htz : 0 ≤ z.im := by linarith
      rw [abs_of_nonneg htz]
      linarith
    · have htneg : t < 0 := lt_of_not_ge ht0
      have htn : |t| = -t := abs_of_neg htneg
      have ht5 : t ≤ -5 := by
        rw [htn] at ht
        linarith
      have hzn : z.im ≤ 0 := by linarith
      rw [abs_of_nonpos hzn]
      linarith
  have ht_im_up : |z.im| ≤ |t| + 4 := by
    calc
      |z.im| = |(z.im - t) + t| := by congr 1; ring
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 4 := by linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact ht_im_lo
  · exact ht_im_up

/-- Uniform growth of `ζ` on the circle of radius 4 centred at `2 + i·t` (`|t| ≥ 5`):
`‖ζ z‖ ≤ B · (|t| + 7)^12` for all `z` on the circle.  Obtained by splitting the circle into
the three regions `re ≤ -1` (use `zeta_strip_polyGrowth_neg`), `-1 ≤ re ≤ 3`
(`zeta_strip_polyGrowth`) and `re ≥ 3` (`zeta_norm_le_const_of_three_le_re`). -/
private lemma zeta_sphere4_bound_bd :
    ∃ B : ℝ, 1 ≤ B ∧ B ≤ 10 ^ 41 ∧ ∀ (t : ℝ), 5 ≤ |t| → ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) →
      ‖riemannZeta z‖ ≤ B * (|t| + 7) ^ 12 := by
  rcases zeta_strip_polyGrowth_b with ⟨Cpos, hCpos, hCposle, hCposS⟩
  rcases zeta_strip_polyGrowth_neg_b with ⟨Cneg, hCneg, hCnegle, hCnegS⟩
  rcases zeta_norm_le_const_three_le_re_b with ⟨C3, hC3, hC3le, hC3S⟩
  let C : ℝ := Cpos + Cneg + C3
  let B : ℝ := max C 1
  have hB1 : 1 ≤ B := le_max_right C 1
  have hCpos0 : 0 ≤ Cpos := le_of_lt hCpos
  have hCneg0 : 0 ≤ Cneg := le_of_lt hCneg
  have hC30 : 0 ≤ C3 := le_of_lt hC3
  have hCneg_le_B : Cneg ≤ B := by
    calc Cneg ≤ Cpos + Cneg + C3 := by nlinarith
    _ ≤ B := le_max_left C 1
  have hCpos_le_B : Cpos ≤ B := by
    calc Cpos ≤ Cpos + Cneg + C3 := by nlinarith
    _ ≤ B := le_max_left C 1
  have hC3_le_B : C3 ≤ B := by
    calc C3 ≤ Cpos + Cneg + C3 := by nlinarith
    _ ≤ B := le_max_left C 1
  refine ⟨B, hB1, ?_, ?_⟩
  · dsimp only [B]
    refine max_le ?_ (by norm_num)
    nlinarith [hCposle, hCnegle, hC3le]
  intro t ht z hz
  obtain ⟨hσ_lo, _hσ_hi, htim1, htimup⟩ := sphere4_re_im_bd (t := t) ht hz
  have hbase1 : 1 ≤ |z.im| + 3 := by linarith
  have hle7 : |z.im| + 3 ≤ |t| + 7 := by linarith
  have hpow12le : (|z.im| + 3) ^ 12 ≤ (|t| + 7) ^ 12 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ |z.im| + 3) hle7 12
  have hpownn : 0 ≤ (|t| + 7) ^ 12 := by positivity
  have hzexp : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z := by
    calc
      (z.re : ℂ) + Complex.I * (z.im : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by ring
      _ = z := Complex.re_add_im z
  by_cases hneg : z.re ≤ -1
  · -- region re ∈ [-2, -1]
    have hb := hCnegS z.re z.im hσ_lo hneg htim1
    have hb0 : ‖riemannZeta z‖ ≤ Cneg * (|z.im| + 3) ^ 12 := by
      simpa [hzexp] using hb
    calc
      ‖riemannZeta z‖ ≤ Cneg * (|z.im| + 3) ^ 12 := hb0
      _ ≤ Cneg * (|t| + 7) ^ 12 := by
        exact mul_le_mul_of_nonneg_left hpow12le hCneg0
      _ ≤ B * (|t| + 7) ^ 12 := by
        exact mul_le_mul_of_nonneg_right hCneg_le_B hpownn
  · by_cases hle3 : z.re ≤ 3
    · -- region re ∈ (-1, 3]
      have hσ_ge : -1 ≤ z.re := by linarith
      have hb := hCposS z.re z.im hσ_ge hle3 htim1
      have hb0 : ‖riemannZeta z‖ ≤ Cpos * (|z.im| + 3) ^ 4 := by
        simpa [hzexp] using hb
      have hpow4 : (|z.im| + 3) ^ 4 ≤ (|z.im| + 3) ^ 12 :=
        pow_le_pow_right₀ hbase1 (by norm_num : (4 : ℕ) ≤ 12)
      calc
        ‖riemannZeta z‖ ≤ Cpos * (|z.im| + 3) ^ 4 := hb0
        _ ≤ Cpos * (|z.im| + 3) ^ 12 := by
          exact mul_le_mul_of_nonneg_left hpow4 hCpos0
        _ ≤ Cpos * (|t| + 7) ^ 12 := by
          exact mul_le_mul_of_nonneg_left hpow12le hCpos0
        _ ≤ B * (|t| + 7) ^ 12 := by
          exact mul_le_mul_of_nonneg_right hCpos_le_B hpownn
    · -- region re > 3
      have hσ3 : 3 ≤ z.re := by linarith
      have hb := hC3S z hσ3
      have hpow1 : 1 ≤ (|t| + 7) ^ 12 := by
        apply one_le_pow₀
        linarith
      calc
        ‖riemannZeta z‖ ≤ C3 := hb
        _ ≤ C3 * (|t| + 7) ^ 12 := by
          exact le_mul_of_one_le_right hC30 hpow1
        _ ≤ B * (|t| + 7) ^ 12 := by
          exact mul_le_mul_of_nonneg_right hC3_le_B hpownn

/-- **Lagarias–Jensen bound for the divisor of the Riemann zeta function on a disk of radius 3**
centred on the line `re s = 2` with `|t| ≥ 5`: the (integer, multiplicity-weighted) divisor sum
is `O(log |t|)`. -/
theorem zeta_ball3_divisor_le_log_b :
    ∃ K : ℝ, 0 < K ∧ K ≤ 10 ^ 4 ∧ ∀ t : ℝ, 5 ≤ |t| →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) ≤
        K * (Real.log (|t| + 6) + 1) := by
  classical
  rcases zeta_sphere4_bound_bd with ⟨B, hB1, hBle, hBspec⟩
  rcases zeta_lower_re_two_b with ⟨c0, hc0ge, hc0le, hc0spec⟩
  have hc0 : 0 < c0 := by linarith
  let d : ℝ := Real.log ((4 : ℝ) / (3 : ℝ))
  have hd : 0 < d := by
    dsimp [d]
    exact Real.log_pos (by norm_num : (1 : ℝ) < (4 : ℝ) / (3 : ℝ))
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  let A : ℝ := Real.log B + 12 * Real.log 2 - Real.log c0
  let K : ℝ := (12 + |A|) / d
  have hK : 0 < K := by
    dsimp [K, d]
    positivity
  refine ⟨K, hK, ?_, ?_⟩
  · have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
    have hd4 : (1 / 4 : ℝ) ≤ d := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (3 : ℝ) / 4 by norm_num)
      rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)] at h
      dsimp only [d]
      rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
      linarith
    have hlogB : Real.log B ≤ 370 := by
      have h := Real.log_le_log hB0 hBle
      have h2 : Real.log ((10 : ℝ) ^ 41) = 41 * Real.log 10 := by rw [Real.log_pow]; norm_num
      have h3 : Real.log (10 : ℝ) ≤ 9 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
      rw [h2] at h; nlinarith
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
    have hlogc0lo : -Real.log c0 ≤ 3 := by
      have h := Real.log_le_log (show (0 : ℝ) < (1 : ℝ) / 8 by norm_num) hc0ge
      have h1 : Real.log ((1 : ℝ) / 8) = -Real.log 8 := by
        rw [show ((1 : ℝ) / 8) = (8 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [h1] at h
      have h2 : Real.log (8 : ℝ) ≤ 3 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        have h3 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        push_cast; nlinarith
      linarith
    have hlogc0up : Real.log c0 ≤ 0 := Real.log_nonpos hc0.le (by linarith)
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hA : |Real.log B + 12 * Real.log 2 - Real.log c0| ≤ 400 := by
      rw [abs_le]; constructor <;> linarith
    dsimp only [K]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < d)]
    nlinarith [hd4, hA]
  intro t ht
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let M : ℝ := B * (|t| + 7) ^ 12
  have hpow1 : 1 ≤ (|t| + 7) ^ 12 := by
    apply one_le_pow₀
    linarith
  have hM1 : 1 ≤ M := by
    dsimp [M]
    calc 1 ≤ B := hB1
    _ ≤ B * (|t| + 7) ^ 12 := le_mul_of_one_le_right (by positivity) hpow1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hX1 : 1 ≤ |t| + 6 := by linarith
  have hlogX_nonneg : 0 ≤ Real.log (|t| + 6) := Real.log_nonneg hX1
  -- ζ is analytic on the closed ball of radius 4 (it avoids the pole at 1)
  have hdist1 : (4 : ℝ) < ‖(1 : ℂ) - c‖ := by
    have him := Complex.abs_im_le_norm ((1 : ℂ) - c)
    have hre : ((1 : ℂ) - c).im = -t := by simp [c]
    rw [hre] at him
    rw [abs_neg] at him
    linarith
  have hnot1 : (1 : ℂ) ∉ Metric.closedBall c (4 : ℝ) := by
    intro h1
    have hd' : ‖(1 : ℂ) - c‖ ≤ (4 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using h1
    linarith
  have hζan : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c (4 : ℝ)) := by
    refine analyticOn_riemannZeta.mono ?_
    intro z hz hz1
    have hd' : ‖(1 : ℂ) - c‖ ≤ (4 : ℝ) := by
      rw [← hz1]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    linarith
  have hζan4 : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c |(4 : ℝ)|) := by
    simpa using hζan
  -- ζ (2 + i t) ≠ 0, with the uniform lower bound
  have hfc : riemannZeta c ≠ 0 := by
    intro h0
    have hnorm0 : ‖riemannZeta c‖ = 0 := by simp [h0]
    have hlb : c0 ≤ ‖riemannZeta c‖ := by
      simpa [c] using hc0spec t
    linarith
  have hnormc : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hfc
  have hlogc_lower : Real.log c0 ≤ Real.log ‖riemannZeta c‖ := by
    exact Real.log_le_log hc0 (by simpa [c] using hc0spec t)
  -- bound ζ on the circle of radius 4 by M
  have f_bound : ∀ z : ℂ, z ∈ Metric.sphere c |(4 : ℝ)| → ‖riemannZeta z‖ ≤ M := by
    intro z hz
    have hb := hBspec t ht z (by simpa [c] using hz)
    simpa [M] using hb
  -- Jensen inequality on the closed ball of radius 4, counting zeros in the ball of radius 3
  have hjs := AnalyticOnNhd.sum_divisor_le (c := c) (r := (3 : ℝ)) (R := (4 : ℝ))
      (M := M) (f := riemannZeta) (r_pos := by norm_num) (r_lt_R := by norm_num)
      (hM := hM1) (h₁f := hζan4) (h₂f := hfc) (f_bound := f_bound)
  have hEq3 : Metric.closedBall c (3 : ℝ) = Metric.closedBall c |(3 : ℝ)| := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hfinZ3 : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)).finiteSupport
        (isCompact_closedBall c |(3 : ℝ)|))
  have hEqSum3 : ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ)) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) := by
    simpa using ((Int.castRingHom ℝ).map_finsum hfinZ3)
  have hsumSet : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c (3 : ℝ))) u : ℤ) : ℝ)) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) := by
    apply finsum_congr
    intro u
    rw [hEq3]
  have hsum : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) ≤
      Real.log (M / ‖riemannZeta c‖) / d := by
    simpa [d] using (le_of_eq hEqSum3.symm).trans hjs
  -- arithmetic: log (M / ‖ζ c‖) ≤ (12 + |A|) * (log (|t|+6) + 1)
  have hlog7 : Real.log (|t| + 7) ≤ Real.log (|t| + 6) + Real.log 2 := by
    have hle : |t| + 7 ≤ 2 * (|t| + 6) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < |t| + 7)
      (le_trans hle (by nlinarith : 2 * (|t| + 6) ≤ 2 * (|t| + 6)))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : |t| + 6 ≠ 0)] at hlog
    linarith
  have hlogM : Real.log M = Real.log B + 12 * Real.log (|t| + 7) := by
    dsimp [M]
    have hBne : B ≠ 0 := ne_of_gt hB0
    have hpne : (|t| + 7) ^ 12 ≠ 0 := by positivity
    rw [Real.log_mul hBne hpne, Real.log_pow]
    norm_num
  have hdivlog : Real.log (M / ‖riemannZeta c‖) = Real.log M - Real.log ‖riemannZeta c‖ := by
    exact Real.log_div (ne_of_gt hM0) (ne_of_gt hnormc)
  have hmain_upper : Real.log (M / ‖riemannZeta c‖) ≤ 12 * Real.log (|t| + 6) + A := by
    have hstep : Real.log M - Real.log c0 ≤ 12 * Real.log (|t| + 6) + A := by
      dsimp [A]
      rw [hlogM]
      have hlt : 12 * Real.log (|t| + 7) ≤ 12 * (Real.log (|t| + 6) + Real.log 2) :=
        mul_le_mul_of_nonneg_left hlog7 (by norm_num : (0 : ℝ) ≤ 12)
      linarith
    calc
      Real.log (M / ‖riemannZeta c‖) = Real.log M - Real.log ‖riemannZeta c‖ := hdivlog
      _ ≤ Real.log M - Real.log c0 := by linarith
      _ ≤ 12 * Real.log (|t| + 6) + A := hstep
  let X : ℝ := Real.log (|t| + 6) + 1
  have hXge1 : 1 ≤ X := by dsimp [X]; linarith
  have hA1 : |A| ≤ |A| * X := le_mul_of_one_le_right (abs_nonneg A) hXge1
  have hA2 : A ≤ |A| := le_abs_self A
  have hXlog : 12 * Real.log (|t| + 6) ≤ 12 * X := by
    dsimp [X]
    nlinarith
  have hfinal_upper : Real.log (M / ‖riemannZeta c‖) ≤ (12 + |A|) * X := by
    calc
      Real.log (M / ‖riemannZeta c‖) ≤ 12 * Real.log (|t| + 6) + A := hmain_upper
      _ ≤ (12 + |A|) * X := by nlinarith
  have hratio : Real.log (M / ‖riemannZeta c‖) / d ≤ K * X := by
    calc
      Real.log (M / ‖riemannZeta c‖) / d ≤ ((12 + |A|) * X) / d :=
        div_le_div_of_nonneg_right hfinal_upper (le_of_lt hd)
      _ = K * X := by
        dsimp [K]
        ring
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ))
        = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c (3 : ℝ))) u : ℤ) : ℝ)) := by
            dsimp [c]
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta (Metric.closedBall c |(3 : ℝ)|)) u : ℤ) : ℝ)) := hsumSet
    _ ≤ Real.log (M / ‖riemannZeta c‖) / d := hsum
    _ ≤ K * X := hratio
    _ = K * (Real.log (|t| + 6) + 1) := by
      dsimp [X]





/-- For `|t| ≥ 5`, the point `2 + i t` is at distance at least `5` from `1`. -/
private lemma norm_one_sub_center_ge_rd {t : ℝ} (ht : 5 ≤ |t|) :
    5 ≤ ‖(1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  have h := Complex.abs_im_le_norm ((1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ)))
  have hval : ((1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))).im = -t := by simp
  rw [hval, abs_neg] at h
  linarith

/-- Every point of the open ball of radius `4` about `2 + i t` (`|t| ≥ 5`) differs from `1`. -/
private lemma ne_one_of_ball_four_rd {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) : z ≠ 1 := by
  intro hz1
  have hzd : ‖z - ((2 : ℂ) + Complex.I * (t : ℂ))‖ < (4 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  rw [hz1] at hzd
  have hge := norm_one_sub_center_ge_rd (t := t) ht
  linarith

/-- On the open ball of radius `4` about `2 + i t` (`|t| ≥ 5`), the entire function
`riemannZeta₁ = (s-1)·ζ(s) + O((s-1)²)` agrees with `(s-1)·ζ(s)`. -/
private lemma riemannZeta₁_eq_mul_sub_ball_four_rd {t : ℝ} (ht : 5 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  have hz1 : z ≠ 1 := ne_one_of_ball_four_rd ht hz
  rw [riemannZeta_eq_inv_sub_mul hz1, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz1)]

/-- On the open ball of radius `4` about `2 + i t` (`|t| ≥ 5`) the meromorphic order of
`riemannZeta₁` coincides with that of `ζ` (multiplication by the analytic, non-vanishing
factor `s - 1` does not change the order). -/
private lemma meromorphicOrderAt_riemannZeta₁_eq_riemannZeta_ball_four_rd {t : ℝ} (ht : 5 ≤ |t|)
    {u : ℂ} (hu : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ)) :
    meromorphicOrderAt riemannZeta₁ u = meromorphicOrderAt riemannZeta u := by
  have hball : Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) ∈ 𝓝 u :=
    Metric.isOpen_ball.mem_nhds hu
  have hev : riemannZeta₁ =ᶠ[𝓝[≠] u] ((fun z : ℂ => z - 1) * riemannZeta) := by
    filter_upwards [nhdsWithin_le_nhds hball] with z hz
    exact riemannZeta₁_eq_mul_sub_ball_four_rd ht hz
  have hg : AnalyticAt ℂ (fun z : ℂ => z - 1) u := by fun_prop
  have hg0 : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_ball_four_rd ht hu)
  calc meromorphicOrderAt riemannZeta₁ u
      = meromorphicOrderAt ((fun z : ℂ => z - 1) * riemannZeta) u :=
        meromorphicOrderAt_congr hev
    _ = meromorphicOrderAt riemannZeta u := meromorphicOrderAt_mul_of_ne_zero hg hg0

/-- `ζ` is analytic on the closed ball of radius `3` about `2 + i t` (`|t| ≥ 5`), which avoids
the pole at `1`. -/
private lemma analyticOn_riemannZeta_closedBall_three_rd {t : ℝ} (ht : 5 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) := by
  refine analyticOn_riemannZeta.mono ?_
  intro z hz hz1
  rw [Set.mem_singleton_iff] at hz1
  rw [hz1] at hz
  have hd : ‖(1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ (3 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hge := norm_one_sub_center_ge_rd (t := t) ht
  linarith

/-- **Lagarias–Jensen bound for the divisor of `riemannZeta₁` on a disk centred on `re s = 2`.**

For every real ordinate `t` with `|t| ≥ 5` and every radius `R` with `0 < R ≤ 4`, the
(multiplicity-weighted) divisor sum of the entire function `riemannZeta₁` on the closed disk of
radius `R/2` about `2 + i t` is `O(log |t|)`.  The disk of radius `R/2 ≤ 2` is contained in the
disk of radius `3`, where `riemannZeta₁` has the same divisor as `ζ`; monotonicity of the
divisor sum together with the Lagarias–Jensen bound `zeta_ball3_divisor_le_log` for `ζ` gives
the claim. -/
theorem riemannZeta1_ball_divisor_le_log_b :
    ∃ K : ℝ, 0 < K ∧ K ≤ 10 ^ 4 ∧ ∀ t : ℝ, 5 ≤ |t| → ∀ R : ℝ, 0 < R → R ≤ 4 →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u : ℤ) : ℝ)) ≤
        K * (Real.log (|t| + 6) + 1) := by
  classical
  rcases zeta_ball3_divisor_le_log_b with ⟨K, hKpos, hKle, hK⟩
  refine ⟨K, hKpos, hKle, ?_⟩
  intro t ht R hR hR4
  -- analyticity of ζ and ζ₁ on the relevant disks
  have hζan : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) :=
    analyticOn_riemannZeta_closedBall_three_rd ht
  have hζ1an : AnalyticOnNhd ℂ riemannZeta₁
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  -- pointwise comparison of the two divisors
  have hpoint : ∀ u : ℂ,
      (MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u ≤
        (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)
    · have hu4 : u ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) (4 : ℝ) := by
        simp only [Metric.mem_closedBall] at hu
        simp only [Metric.mem_ball]
        linarith
      have hu3 : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ) := by
        simp only [Metric.mem_closedBall] at hu ⊢
        linarith
      have hord : meromorphicOrderAt riemannZeta₁ u = meromorphicOrderAt riemannZeta u :=
        meromorphicOrderAt_riemannZeta₁_eq_riemannZeta_ball_four_rd ht hu4
      rw [MeromorphicOn.divisor_apply hζ1an.meromorphicOn hu,
        MeromorphicOn.divisor_apply hζan.meromorphicOn hu3, hord]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζan u
  -- finiteness of both divisors
  have hfin1 : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))).finiteSupport
        (isCompact_closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2)))
  have hfin3 : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))).finiteSupport
        (isCompact_closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)))
  -- integer-level monotonicity and its cast to ℝ
  have hZle : (∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) ≤
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) :=
    finsum_le_finsum' hfin1 hfin3 hpoint
  have hmap1 : (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) : ℝ) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u : ℤ) : ℝ)) :=
    map_finsum (Int.castRingHom ℝ) hfin1
  have hmap3 : (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) : ℝ) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) :=
    map_finsum (Int.castRingHom ℝ) hfin3
  have hcast : (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) : ℝ) ≤
      (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) : ℝ) :=
    Int.cast_le.mpr hZle
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u : ℤ) : ℝ))
        = (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (R / 2))) u) : ℝ) := hmap1.symm
    _ ≤ (↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u) : ℝ) := hcast
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℝ)) := hmap3
    _ ≤ K * (Real.log (|t| + 6) + 1) := hK t ht

/-- Growth of `riemannZeta₁` on balls of radius `< 3/2 - δ/2` about `2 + I*t`
(`|t| ≥ 5`), with an explicit constant. -/
theorem zeta1_growth_ball_5_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 26 ∧ ∀ δ t : ℝ, 0 < δ → δ ≤ 1 → 5 ≤ |t| →
      ∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ < 3 / 2 - δ / 2 →
        ‖riemannZeta₁ w‖ ≤ C * (1 + 1 / δ) * (|t| + 6) ^ 5 := by
  rcases zeta_strip_polyGrowth_b with ⟨Cpg, hCpg0, hCpgle, hCpgSpec⟩
  rcases zeta_norm_le_const_three_le_re_b with ⟨C3, hC30, hC3le, hC3Spec⟩
  refine ⟨max Cpg C3, lt_max_of_lt_left hCpg0, ?_, ?_⟩
  · exact max_le (le_trans hCpgle (by norm_num)) (by linarith)
  intro δ t hδ0 hδ1 ht w hball
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let R : ℝ := 3 / 2 - δ / 2
  have hR : R ≤ 3 / 2 := by dsimp [R]; linarith
  have hwc : ‖w - c‖ < 3 / 2 := lt_of_lt_of_le hball hR
  have hσdist : |w.re - 2| ≤ ‖w - c‖ := by
    simpa [c] using (Complex.abs_re_le_norm (w - c))
  have hτdist : |w.im - t| ≤ ‖w - c‖ := by
    simpa [c] using (Complex.abs_im_le_norm (w - c))
  have hσlo : (1 / 2 : ℝ) ≤ w.re := by
    have h1 : -(‖w - c‖) ≤ w.re - 2 := by
      have h := neg_le_abs (w.re - 2); linarith
    linarith
  have hσhi : w.re ≤ 7 / 2 := by
    have h1 : w.re - 2 ≤ ‖w - c‖ := le_trans (le_abs_self _) hσdist
    linarith
  have hτge : (1 : ℝ) ≤ |w.im| := by
    have h2 : |t| ≤ |w.im| + |w.im - t| := by
      calc |t| = |w.im + (t - w.im)| := by congr 1; ring
        _ ≤ |w.im| + |t - w.im| := abs_add_le _ _
        _ = |w.im| + |w.im - t| := by rw [abs_sub_comm]
    linarith
  have hτhi : |w.im| ≤ |t| + 3 / 2 := by
    have h2 : |w.im| ≤ |w.im - t| + |t| := by
      calc |w.im| = |(w.im - t) + t| := by congr 1; ring
        _ ≤ |w.im - t| + |t| := abs_add_le _ _
    linarith
  have hw_ne1 : w ≠ 1 := by
    intro hw1
    have hle : ‖(1 : ℂ) - c‖ < 3 / 2 := by
      rw [hw1] at hwc; exact hwc
    have him : |t| ≤ ‖(1 : ℂ) - c‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - c)
      have hval : ((1 : ℂ) - c).im = -t := by simp only [c]; simp
      rw [hval, abs_neg] at h
      exact h
    linarith
  have hc1 : ‖c - 1‖ ≤ 1 + |t| := by
    have hrew : c - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by simp only [c]; ring
    rw [hrew]
    calc ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
      _ = 1 + |t| := by
        rw [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        ring
  have hw1le : ‖w - 1‖ ≤ |t| + 6 := by
    have hsum : (w - c) + (c - 1) = w - 1 := by ring
    calc ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by rw [← hsum]
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 3 / 2 + (1 + |t|) := by linarith [le_of_lt hwc]
      _ ≤ |t| + 6 := by linarith
  have hX1 : (1 : ℝ) ≤ (|t| + 6) ^ 5 :=
    one_le_pow₀ (by linarith [abs_nonneg t] : (1 : ℝ) ≤ |t| + 6)
  have hne0 : riemannZeta₁ w = (w - 1) * riemannZeta w := by
    rw [riemannZeta_eq_inv_sub_mul hw_ne1, mul_inv_cancel_left₀ (sub_ne_zero.mpr hw_ne1)]
  have hmain : ‖riemannZeta₁ w‖ ≤ max Cpg C3 * (1 + 1 / δ) * (|t| + 6) ^ 5 := by
    have hδge : (1 : ℝ) ≤ 1 + 1 / δ := by
      have : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδ0); linarith
    by_cases hσ3 : w.re ≤ 3
    · have hζle : ‖riemannZeta w‖ ≤ Cpg * (|w.im| + 3) ^ 4 := by
        have hform : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
          apply Complex.ext <;> simp
        have hEqZeta : riemannZeta w = riemannZeta ((w.re : ℂ) + Complex.I * (w.im : ℂ)) :=
          congrArg riemannZeta hform
        rw [hEqZeta]
        exact hCpgSpec w.re w.im (by linarith) hσ3 hτge
      have hτ36 : |w.im| + 3 ≤ |t| + 6 := by linarith
      have hpow46 : (|w.im| + 3) ^ 4 ≤ (|t| + 6) ^ 4 :=
        pow_le_pow_left₀ (by positivity : 0 ≤ |w.im| + 3) hτ36 4
      have hstep : ‖riemannZeta₁ w‖ ≤ Cpg * (|t| + 6) ^ 5 := by
        rw [hne0, norm_mul]
        calc ‖w - 1‖ * ‖riemannZeta w‖ ≤ (|t| + 6) * ‖riemannZeta w‖ :=
              mul_le_mul_of_nonneg_right hw1le (norm_nonneg _)
          _ ≤ (|t| + 6) * (Cpg * (|w.im| + 3) ^ 4) :=
              mul_le_mul_of_nonneg_left hζle (by positivity)
          _ ≤ (|t| + 6) * (Cpg * (|t| + 6) ^ 4) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpow46 (le_of_lt hCpg0)) (by positivity)
          _ = Cpg * (|t| + 6) ^ 5 := by ring
      calc ‖riemannZeta₁ w‖ ≤ Cpg * (|t| + 6) ^ 5 := hstep
        _ ≤ max Cpg C3 * (|t| + 6) ^ 5 :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max Cpg C3 * (1 + 1 / δ) * (|t| + 6) ^ 5 := by
              have : Cpg * (|t|+6)^5 ≤ Cpg * ((1+1/δ) * (|t|+6)^5) :=
                mul_le_mul_of_nonneg_left
                  (le_mul_of_one_le_left (by positivity) hδge) (le_of_lt hCpg0)
              nlinarith [this, le_max_left Cpg C3, le_max_right Cpg C3, hX1, hCpg0,
                show (0:ℝ) ≤ C3 from le_of_lt hC30, hδge]
    · have hσ3re : 3 ≤ w.re := by linarith
      have hζle : ‖riemannZeta w‖ ≤ C3 := hC3Spec w hσ3re
      have hstep : ‖riemannZeta₁ w‖ ≤ C3 * (|t| + 6) ^ 5 := by
        rw [hne0, norm_mul]
        calc ‖w - 1‖ * ‖riemannZeta w‖ ≤ (|t| + 6) * ‖riemannZeta w‖ :=
              mul_le_mul_of_nonneg_right hw1le (norm_nonneg _)
          _ ≤ (|t| + 6) * C3 := mul_le_mul_of_nonneg_left hζle (by positivity)
          _ = C3 * (|t| + 6) := by ring
          _ ≤ C3 * (|t| + 6) ^ 5 := by
              have hx : (|t| + 6 : ℝ) ≤ (|t| + 6) ^ 5 := by
                simpa using pow_le_pow_right₀ (by linarith [abs_nonneg t] : (1:ℝ) ≤ |t| + 6)
                  (by norm_num : (1:ℕ) ≤ 5)
              exact mul_le_mul_of_nonneg_left hx (le_of_lt hC30)
      calc ‖riemannZeta₁ w‖ ≤ C3 * (|t| + 6) ^ 5 := hstep
        _ ≤ max Cpg C3 * (|t| + 6) ^ 5 :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ max Cpg C3 * (1 + 1 / δ) * (|t| + 6) ^ 5 := by
              have : C3 * (|t|+6)^5 ≤ C3 * ((1+1/δ) * (|t|+6)^5) :=
                mul_le_mul_of_nonneg_left
                  (le_mul_of_one_le_left (by positivity) hδge) (le_of_lt hC30)
              nlinarith [this, le_max_left Cpg C3, le_max_right Cpg C3, hX1, hCpg0,
                show (0:ℝ) ≤ C3 from le_of_lt hC30, hδge]
  exact hmain

set_option maxHeartbeats 0


/-! zeta₁ has no zeros on Re > 1/2 under RH -/
lemma zeta1_ne_zero_of_rh_gt_half_rh (h : RiemannHypothesis) {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · intro hz
    have hzζ : riemannZeta s = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hs1, hz]
      simp
    exact zeta_ne_zero_of_rh_gt_half h hs hzζ

/-! ‖ζ'/ζ (s)‖ ≤ ‖ζ₁'/ζ₁ (s)‖ + 1/‖s−1‖ -/
lemma zeta_logDeriv_norm_le_rh (s : ℂ) (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by
  have hid : deriv riemannZeta s / riemannZeta s =
      - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hs, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs]
    field_simp [hz1, sub_ne_zero.mpr hs]
  rw [hid]
  calc
    ‖- (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
        ‖- (s - 1)⁻¹‖ + ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ := norm_add_le _ _
    _ = ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by
      have hnorm : ‖- (s - 1)⁻¹‖ = 1 / ‖s - 1‖ := by
        simp [norm_inv]
      simp [hnorm, add_comm]

/-! ===== real arithmetic helpers ===== -/
lemma one_le_one_add_inv_rhpub (δ : ℝ) (hδ0 : 0 < δ) : (1 : ℝ) ≤ 1 + 1 / δ := by
  have h : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδ0)
  linarith
lemma inv_le_one_add_inv_rhpub (δ : ℝ) (hδ0 : 0 < δ) : (1 / δ : ℝ) ≤ 1 + 1 / δ := by linarith
lemma invsq_le_inv_rhpub (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : (1 : ℝ) ≤ 1 / δ := by
  exact (one_le_div hδ0).2 hδ1
lemma invsq_le_pow3_rhpub (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := by
  calc
    (1 / δ) ^ 2 ≤ (1 / δ) ^ 3 := by
      have h1 : (1 : ℝ) ≤ 1 / δ := invsq_le_inv_rhpub δ hδ0 hδ1
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (1 / δ))
      simpa [pow_succ, pow_two, mul_assoc] using h2
    _ ≤ (1 + 1 / δ) ^ 3 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / δ) (inv_le_one_add_inv_rhpub δ hδ0) 3
lemma log_lepoly_rhpub (δ : ℝ) (hδ0 : 0 < δ) : Real.log (1 + 1 / δ) ≤ 1 + 1 / δ := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / δ)
  linarith
lemma log1p_div_sq_le_rhpub (δ : ℝ) (hδ0 : 0 < δ) :
    Real.log (1 + 1 / δ) / δ ^ 2 ≤ (1 + 1 / δ) ^ 3 := by
  calc
    Real.log (1 + 1 / δ) / δ ^ 2 = Real.log (1 + 1 / δ) * (1 / δ) ^ 2 := by
      field_simp [hδ0.ne']
    _ ≤ (1 + 1 / δ) * (1 / δ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (log_lepoly_rhpub δ hδ0) (sq_nonneg _)
    _ ≤ (1 + 1 / δ) * (1 + 1 / δ) ^ 2 := by
      have hsq : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 / δ) (inv_le_one_add_inv_rhpub δ hδ0) 2
      exact mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 1 + 1 / δ)
    _ = (1 + 1 / δ) ^ 3 := by ring
lemma logxadd6_le_rhpub (t : ℝ) : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
  have h : |t| + 6 ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
  have h1 : Real.log (|t| + 6) ≤ Real.log ((|t| + 3) ^ 2) := Real.log_le_log (by nlinarith [abs_nonneg t]) h
  calc
    Real.log (|t| + 6) ≤ Real.log ((|t| + 3) ^ 2) := h1
    _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; ring
lemma LL_ge_one_rhpub (t : ℝ) : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
  have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by nlinarith [abs_nonneg t])
  linarith
lemma logx6_div_sq_le_two_rhpub (δ t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (|t| + 6) / δ ^ 2 ≤
      2 * ((1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3) := by
  let L : ℝ := Real.log (|t| + 3) + 1
  have hL1 : (1 : ℝ) ≤ L := LL_ge_one_rhpub t
  have hLpos : 0 ≤ L := by linarith
  have hlg2 : Real.log (|t| + 6) ≤ 2 * L := by
    have h := logxadd6_le_rhpub t
    dsimp [L]
    nlinarith
  have hD : L * (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := by
    have hs : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := invsq_le_pow3_rhpub δ hδ0 hδ1
    have h1 : L * (1 / δ) ^ 2 ≤ L * (1 + 1 / δ) ^ 3 := mul_le_mul_of_nonneg_left hs hLpos
    have hLpow : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0)
    have h2 : L * (1 + 1 / δ) ^ 3 ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hLpow (by positivity : 0 ≤ (1 + 1 / δ) ^ 3)
    exact le_trans h1 h2
  calc
    Real.log (|t| + 6) / δ ^ 2 = Real.log (|t| + 6) * (1 / δ) ^ 2 := by
      field_simp [hδ0.ne']
    _ ≤ (2 * L) * (1 / δ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hlg2 (sq_nonneg _)
    _ = 2 * (L * (1 / δ) ^ 2) := by ring
    _ ≤ 2 * ((1 + 1 / δ) ^ 3 * L ^ 3) := mul_le_mul_of_nonneg_left hD (by norm_num)
    _ = 2 * ((1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3) := by dsimp [L]
lemma final_arith_rhpub {C1 : ℝ} (hC1 : 0 ≤ C1) {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 + 4 ≤
      (48 * (Real.log 8 + C1 + 1) + 480 + 4) * (1 + 1 / δ) ^ 3 *
        (Real.log (|t| + 3) + 1) ^ 3 := by
  let L : ℝ := Real.log (|t| + 3) + 1
  let D : ℝ := (1 + 1 / δ) ^ 3 * L ^ 3
  have hL1 : (1 : ℝ) ≤ L := LL_ge_one_rhpub t
  have qinv : (1 / δ) ^ 2 ≤ D := by
    have hs : (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := invsq_le_pow3_rhpub δ hδ0 hδ1
    have hL3 : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 (le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0))
    have hb : 0 ≤ (1 + 1 / δ) ^ 3 := by positivity
    calc
      (1 / δ) ^ 2 ≤ (1 + 1 / δ) ^ 3 := hs
      _ ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := le_mul_of_one_le_right hb hL3
      _ = D := by rfl
  have qlog1p : Real.log (1 + 1 / δ) / δ ^ 2 ≤ D := by
    have h := log1p_div_sq_le_rhpub δ hδ0
    have hL3 : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 (le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0))
    have hb : 0 ≤ (1 + 1 / δ) ^ 3 := by positivity
    calc
      Real.log (1 + 1 / δ) / δ ^ 2 ≤ (1 + 1 / δ) ^ 3 := h
      _ ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := le_mul_of_one_le_right hb hL3
      _ = D := by rfl
  have qlogx6 : Real.log (|t| + 6) / δ ^ 2 ≤ 2 * D := by
    have h := logx6_div_sq_le_two_rhpub δ t hδ0 hδ1
    simpa [D] using h
  have hDge1 : (1 : ℝ) ≤ D := by
    have h1a : (1 : ℝ) ≤ (1 + 1 / δ) ^ 3 :=
      le_trans (one_le_one_add_inv_rhpub δ hδ0) (le_self_pow₀ (one_le_one_add_inv_rhpub δ hδ0) (by norm_num : (3 : ℕ) ≠ 0))
    have h1b : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 (le_self_pow₀ hL1 (by norm_num : (3 : ℕ) ≠ 0))
    have hstep : (1 + 1 / δ) ^ 3 ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := by
      exact le_mul_of_one_le_right (by positivity : 0 ≤ (1 + 1 / δ) ^ 3) h1b
    calc
      (1 : ℝ) ≤ (1 + 1 / δ) ^ 3 := h1a
      _ ≤ (1 + 1 / δ) ^ 3 * L ^ 3 := hstep
      _ = D := by rfl
  have B1 : 48 * Real.log 8 * (1 / δ) ^ 2 ≤ 48 * Real.log 8 * D := by
    exact mul_le_mul_of_nonneg_left qinv (by positivity : 0 ≤ 48 * Real.log 8)
  have B2 : 48 * C1 * (1 / δ) ^ 2 ≤ 48 * C1 * D := by
    exact mul_le_mul_of_nonneg_left qinv (mul_nonneg (by norm_num) hC1)
  have B3 : 48 * (Real.log (1 + 1 / δ) / δ ^ 2) ≤ 48 * D := by
    exact mul_le_mul_of_nonneg_left qlog1p (by norm_num : (0 : ℝ) ≤ 48)
  have B4 : 240 * (Real.log (|t| + 6) / δ ^ 2) ≤ 480 * D := by
    have h := mul_le_mul_of_nonneg_left qlogx6 (by norm_num : (0 : ℝ) ≤ 240)
    linarith
  have B5 : (4 : ℝ) ≤ 4 * D := by nlinarith
  calc
    48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 + 4
        = 48 * Real.log 8 * (1 / δ) ^ 2 + 48 * C1 * (1 / δ) ^ 2 +
            48 * (Real.log (1 + 1 / δ) / δ ^ 2) + 240 * (Real.log (|t| + 6) / δ ^ 2) + 4 := by
          have hδsq : δ ^ 2 ≠ 0 := by positivity
          field_simp [hδsq]
          ring
    _ ≤ 48 * Real.log 8 * D + 48 * C1 * D + 48 * D + 480 * D + 4 * D := by
          nlinarith
    _ = (48 * (Real.log 8 + C1 + 1) + 480 + 4) * D := by ring
    _ = (48 * (Real.log 8 + C1 + 1) + 480 + 4) * (1 + 1 / δ) ^ 3 *
        (Real.log (|t| + 3) + 1) ^ 3 := by
          simp [D, L]
          ring


theorem zeta_logDeriv_strip_bound_rh_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 5 ∧ ∀ (h : RiemannHypothesis) (δ σ t : ℝ),
      0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 → 5 ≤ |t| →
        (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by
  rcases zeta1_growth_ball_5_b with ⟨Cg, hCg0, hCgle, hCg⟩
  let C1 : ℝ := Real.log (max Cg 1)
  let C : ℝ := (48 * (Real.log 8 + C1 + 1) + 480 + 4)
  refine ⟨C, ?_, ?_, ?_⟩
  · have hC1ge0 : 0 ≤ C1 := Real.log_nonneg (le_max_right Cg 1)
    have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num : (1 : ℝ) < 8)
    dsimp [C]
    nlinarith
  · have hC1le : C1 ≤ 234 := by
      dsimp only [C1]
      have hmax : max Cg 1 ≤ 10 ^ 26 := max_le (le_trans hCgle (by norm_num)) (by norm_num)
      have h := Real.log_le_log (by positivity : (0 : ℝ) < max Cg 1) hmax
      have h2 : Real.log ((10 : ℝ) ^ 26) = 26 * Real.log 10 := by rw [Real.log_pow]; norm_num
      have h3 : Real.log (10 : ℝ) ≤ 9 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
      rw [h2] at h; nlinarith
    have hlog8le : Real.log 8 ≤ 7 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num); linarith
    dsimp only [C]
    nlinarith
  · intro h δ σ t hδ0 hδ1 hσlo hσhi ht5 hdist
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
    let R : ℝ := 3 / 2 - δ / 2
    let d : ℝ := ‖s - c‖
    let M : ℝ := Cg * (1 + 1 / δ) * (|t| + 6) ^ 5
    let A : ℝ := Real.log (2 * M) - Real.log (1 / 4)
    have hCgpos : 0 < Cg := hCg0
    have hC1ge0 : 0 ≤ C1 := Real.log_nonneg (le_max_right Cg 1)
    have hg : Differentiable ℂ riemannZeta₁ := by fun_prop
    -- geometry
    have hRpos : 0 < R := by
      dsimp [R]
      linarith
    have hdnorm : ‖s - c‖ = |σ - 2| := by
      dsimp [s, c]
      have h : ((σ : ℂ) + Complex.I * (t : ℂ)) - ((2 : ℂ) + Complex.I * (t : ℂ)) = ((σ - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [h]
      simpa [Real.norm_eq_abs] using (Complex.norm_real (σ - 2))
    have hσ2 : σ - 2 ≤ 0 := by linarith
    have hd_eq : d = 2 - σ := by
      dsimp [d]
      rw [hdnorm]
      have ha : |σ - 2| = 2 - σ := by
        rw [abs_of_nonpos hσ2]
        ring
      rw [ha]
    have hds : ‖s - c‖ < R := by
      change d < R
      rw [hd_eq]
      dsimp [R]
      have h1 : 2 - σ ≤ 3 / 2 - δ := by linarith
      have h2 : 3 / 2 - δ < 3 / 2 - δ / 2 := by linarith
      linarith
    have hs_ball : s ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hds
    -- nonzero on the ball under RH
    have hgne : ∀ w : ℂ, w ∈ Metric.ball c R → riemannZeta₁ w ≠ 0 := by
      intro w hw
      have hw1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hwre : (1 / 2 : ℝ) < w.re := by
        have hre2 : |(w - c).re| ≤ ‖w - c‖ := Complex.abs_re_le_norm (w - c)
        have hre2' : |w.re - 2| ≤ ‖w - c‖ := by simpa [c] using hre2
        have hneg : -(‖w - c‖) ≤ w.re - 2 := by
          have h0 : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs (w.re - 2)
          linarith
        dsimp [R] at hw1
        linarith
      exact zeta1_ne_zero_of_rh_gt_half_rh h hwre
    -- upper growth bound on the ball
    have hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖riemannZeta₁ w‖ ≤ M := by
      intro w hw
      have hw1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hb := hCg δ t hδ0 hδ1 ht5 w (by simpa [c, R] using hw1)
      dsimp [M]
      exact hb
    -- lower bound at the centre c
    have hgm : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
      dsimp [c]
      exact zeta1_re_two_lower t
    have hMm : (1 / 4 : ℝ) ≤ M := by
      have hc_in : c ∈ Metric.ball c R := mem_ball_self hRpos
      exact le_trans hgm (hgM c hc_in)
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hMm
    -- apply the core lemma at s with radius δ/4
    have hρ0 : 0 < δ / 4 := by positivity
    have hρ_lt : δ / 4 < R - d := by
      dsimp [R]
      rw [hd_eq]
      linarith
    have hgcore : ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
        2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) := by
      have hh := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound hg (c := c) (R := R) (m := 1 / 4) (M := M)
        hRpos (by norm_num) hMm hgne hgM hgm (z₀ := s) hs_ball (ρ := δ / 4) hρ0 hρ_lt
      dsimp [A] at hh ⊢
      simpa [d] using hh
    -- relate to ζ'/ζ
    have hs_ne1 : s ≠ 1 := by
      intro h1
      have : ‖s - 1‖ = 0 := by simp [h1]
      linarith
    have hz1s : riemannZeta₁ s ≠ 0 := hgne s hs_ball
    have hlogd := zeta_logDeriv_norm_le_rh s hs_ne1 hz1s
    have hdist4 : 1 / ‖s - 1‖ ≤ 4 := by
      have hs1pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne1)
      rw [div_le_iff₀ hs1pos]
      nlinarith
    -- bound on A
    have hA0 : 0 ≤ A := by
      dsimp [A]
      have h2M : (1 / 4 : ℝ) ≤ 2 * M := by nlinarith
      have h1 : Real.log (1 / 4) ≤ Real.log (2 * M) := Real.log_le_log (by norm_num) h2M
      linarith
    have hMlog : Real.log M = Real.log Cg + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6) := by
      have hpos1 : 0 < Cg := hCg0
      have hpos2 : 0 < 1 + 1 / δ := by positivity
      have hpos3 : 0 < (|t| + 6) ^ 5 := by positivity
      calc
        Real.log M = Real.log (Cg * ((1 + 1 / δ) * (|t| + 6) ^ 5)) := by
          congr 1
          dsimp [M]
          ring
        _ = Real.log Cg + Real.log ((1 + 1 / δ) * (|t| + 6) ^ 5) := by
          rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt (mul_pos hpos2 hpos3))]
        _ = Real.log Cg + (Real.log (1 + 1 / δ) + Real.log ((|t| + 6) ^ 5)) := by
          rw [Real.log_mul (ne_of_gt hpos2) (ne_of_gt hpos3)]
        _ = Real.log Cg + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6) := by
          rw [Real.log_pow]
          ring
    have hlogCg : Real.log Cg ≤ C1 := by
      dsimp [C1]
      exact Real.log_le_log (by positivity : 0 < Cg) (le_max_left Cg 1)
    have hA_le : A ≤ Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6) := by
      dsimp [A]
      have hlog : Real.log (2 * M) - Real.log (1 / 4) =
          Real.log 8 + Real.log M := by
        have h1 : Real.log (2 * M) - Real.log (1 / 4) = Real.log ((2 * M) / (1 / 4)) := by
          rw [Real.log_div (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hMpos)) (by norm_num)]
        have h2 : (2 * M) / (1 / 4) = 8 * M := by ring
        rw [h1, h2, Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hMpos)]
      rw [hlog, hMlog]
      nlinarith
    -- geometric bound: 2A(d+δ/4)/((R-d-δ/4)*(δ/4)) ≤ 48A/δ²
    have hgeom : 2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) ≤ 48 * A / δ ^ 2 := by
      have hd2pos : 0 < (R - d - δ / 4) * (δ / 4) := by
        have h1 : 0 < R - d - δ / 4 := by
          dsimp [R]
          rw [hd_eq]
          linarith
        positivity
      have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδ0
      have hcross : (d + δ / 4) * δ ^ 2 ≤ 24 * ((R - d - δ / 4) * (δ / 4)) := by
        dsimp [R]
        rw [hd_eq]
        have hδsq : 0 ≤ δ ^ 2 := sq_nonneg δ
        have h1 : (2 - σ + δ / 4) ≤ 3 / 2 := by nlinarith
        have h2 : (3 / 2 : ℝ) * δ ^ 2 ≤ 24 * ((3 / 2 - δ / 2 - (2 - σ) - δ / 4) * (δ / 4)) := by
          have hR : (3 / 2 - δ / 2 - (2 - σ) - δ / 4) = σ - 1 / 2 - 3 * δ / 4 := by ring
          rw [hR]
          have hsub : (1 / 4 : ℝ) * δ ≤ σ - 1 / 2 - 3 * δ / 4 := by nlinarith
          nlinarith
        calc
          (2 - σ + δ / 4) * δ ^ 2 ≤ (3 / 2) * δ ^ 2 := by
            exact mul_le_mul_of_nonneg_right h1 hδsq
          _ ≤ 24 * ((3 / 2 - δ / 2 - (2 - σ) - δ / 4) * (δ / 4)) := h2
      have hdiv : (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) ≤ 24 / δ ^ 2 := by
        rw [div_le_div_iff₀ hd2pos hδ2pos]
        exact hcross
      calc
        2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4))
            = 2 * A * ((d + δ / 4) / ((R - d - δ / 4) * (δ / 4))) := by ring
        _ ≤ 2 * A * (24 / δ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 * A)
        _ = 48 * A / δ ^ 2 := by ring
    -- final assembly
    have hB := final_arith_rhpub (C1 := C1) hC1ge0 (δ := δ) (t := t) hδ0 hδ1
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by simpa [s] using hlogd
      _ ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + 4 := by linarith
      _ ≤ 2 * A * (d + δ / 4) / ((R - d - δ / 4) * (δ / 4)) + 4 := by linarith
      _ ≤ 48 * A / δ ^ 2 + 4 := by linarith
      _ ≤ 48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 + 4 := by
        have hδ2pos : 0 < δ ^ 2 := sq_pos_of_pos hδ0
        have hmul : 48 * A ≤ 48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) := by
          nlinarith
        have hdiv : 48 * A / δ ^ 2 ≤
            48 * (Real.log 8 + C1 + Real.log (1 + 1 / δ) + 5 * Real.log (|t| + 6)) / δ ^ 2 :=
          div_le_div_of_nonneg_right hmul (le_of_lt hδ2pos)
        linarith
      _ ≤ (48 * (Real.log 8 + C1 + 1) + 480 + 4) * (1 + 1 / δ) ^ 3 *
          (Real.log (|t| + 3) + 1) ^ 3 := hB
      _ = C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by rfl

set_option maxHeartbeats 1000000




/-- The norm of a `finsum` is at most the `finsum` of the norms. -/
private lemma norm_finsum_le_finsum_norm_la' {α : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (f : α → E) (hf : Function.HasFiniteSupport f) :
    ‖∑ᶠ i, f i‖ ≤ ∑ᶠ i, ‖f i‖ := by
  classical
  have hf' : (Function.support f).Finite := hf
  have hg : Function.HasFiniteSupport (fun i => ‖f i‖) := by
    rw [Function.HasFiniteSupport]
    refine hf'.subset ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hfx
    exact hx (by rw [hfx, norm_zero])
  rw [finsum_eq_finsetSum_of_support_subset f (s := hf'.toFinset)
      (by intro x hx; exact (Set.Finite.mem_toFinset hf').mpr hx)]
  rw [finsum_eq_finsetSum_of_support_subset (fun i => ‖f i‖) (s := hf'.toFinset)
      (by
        intro x hx
        rw [Function.mem_support] at hx
        exact (Set.Finite.mem_toFinset hf').mpr (by
          rw [Function.mem_support]
          intro hfx
          exact hx (by rw [hfx, norm_zero])))]
  exact norm_sum_le _ _

/-- If `‖f i‖ ≤ g i` pointwise with `g` of finite support, then `‖∑ᶠ f‖ ≤ ∑ᶠ g`. -/
private lemma norm_finsum_le_of_norm_le_la' {α : Type*} {f : α → ℂ} {g : α → ℝ}
    (hg : Function.HasFiniteSupport g) (hfg : ∀ u, ‖f u‖ ≤ g u) :
    ‖∑ᶠ u, f u‖ ≤ ∑ᶠ u, g u := by
  classical
  have hsupp : Function.HasFiniteSupport f := by
    rw [Function.HasFiniteSupport]
    refine hg.subset ?_
    rw [Function.support_subset_iff]
    intro u hu hgu
    apply hu
    have hz : ‖f u‖ ≤ 0 := by have h := hfg u; rw [hgu] at h; exact h
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
  have h1 : ‖∑ᶠ u, f u‖ ≤ ∑ᶠ u, ‖f u‖ := norm_finsum_le_finsum_norm_la' f hsupp
  have h2 : ∑ᶠ u, ‖f u‖ ≤ ∑ᶠ u, g u := by
    have hsupp' : Function.HasFiniteSupport (fun u => ‖f u‖) := by
      rw [Function.HasFiniteSupport]
      have : Function.support (fun u => ‖f u‖) = Function.support f := by
        ext x
        rw [Function.mem_support, Function.mem_support]
        constructor
        · intro h hfx; exact h (by rw [hfx, norm_zero])
        · intro h hnx; exact h (norm_eq_zero.mp hnx)
      rw [this]; exact hsupp
    exact finsum_le_finsum' hsupp' hg (fun u => hfg u)
  linarith only [h1, h2]

theorem zeta_logDeriv_local_approx_ne_b :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 6 ∧ ∀ t : ℝ, 5 ≤ |t| → ∀ σ : ℝ, (3 / 8 : ℝ) ≤ σ → σ ≤ (5 / 8 : ℝ) →
      riemannZeta₁ (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 →
      ‖logDeriv riemannZeta₁ (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) -
        (∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor completedRiemannZeta
              (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))) u : ℤ) : ℂ) *
            (if ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - u‖ ≤ (1 / 8 : ℝ) then
              ((((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - u)⁻¹ else 0)))‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 := by
  classical
  obtain ⟨Cg, hCgpos, hCgle, hCgb⟩ := zeta1_growth_disk4_b
  obtain ⟨K, hKpos, hKle, hKb⟩ := riemannZeta1_ball_divisor_le_log_b
  refine ⟨224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ Real.log (4 * Cg + 1) := Real.log_nonneg (by linarith)
    linarith
  · have hCg41 : 4 * Cg + 1 ≤ (10 : ℝ) ^ 42 := by
      have h1 : Cg ≤ 10 ^ 40 := hCgle
      norm_num at h1 ⊢
      linarith
    have hlog : Real.log (4 * Cg + 1) ≤ 378 := by
      have h := Real.log_le_log (by linarith) hCg41
      have h2 : Real.log ((10 : ℝ) ^ 42) = 42 * Real.log 10 := by rw [Real.log_pow]; norm_num
      have h3 : Real.log (10 : ℝ) ≤ 9 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
      rw [h2] at h; nlinarith
    nlinarith [hlog, hKle]
  intro t ht σ hσlo hσhi hfs
  obtain ⟨R, hR72, hR4, hcircR, hcircR2⟩ := zeta1_exists_good_radius t ht
  have hRpos : 0 < R := by linarith only [hR72]
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hsdef
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2)) u
    with hd
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall c (3 : ℝ)) u
    with hD
  set S : ℂ := ∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * (1 / (s - u))) with hS
  set T : ℂ := ∑ᶠ u : ℂ, (((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0))
    with hT
  set x : ℝ := Real.log (|t| + 3) + 1 with hx
  -- basic facts
  have hd_fin : Function.HasFiniteSupport d := by
    have hsupp := (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2))).finiteSupport
      (isCompact_closedBall c (R / 2))
    simpa [Function.HasFiniteSupport, hd] using hsupp
  have hCgnn : (0 : ℝ) ≤ Cg * (|t| + 7) ^ 15 :=
    mul_nonneg (le_of_lt hCgpos) (pow_nonneg (by linarith only [abs_nonneg t]) 15)
  have hX0 : (0 : ℝ) ≤ 4 * Cg * (|t| + 7) ^ 15 := by nlinarith only [hCgnn]
  set A : ℝ := 4 * Cg * (|t| + 7) ^ 15 + 1 with hA
  have hA1 : (1 : ℝ) ≤ A := by rw [hA]; linarith only [hX0]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hs_norm : ‖s - c‖ = 2 - σ := by
    have hsc : s - c = ((σ - 2 : ℝ) : ℂ) := by
      simp only [hsdef, hc]; push_cast; ring
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    ring
  have hs13 : ‖s - c‖ ≤ 13 / 8 := by
    rw [hs_norm]; linarith only [hσlo]
  have hs_le : ‖s - c‖ ≤ (13 / 28 : ℝ) * R := by
    rw [hs_norm]
    have h2 : (13 / 8 : ℝ) ≤ 13 / 28 * R := by nlinarith only [hR72]
    linarith only [h2, hσlo]
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hx]
    have : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
    linarith only [this]
  have hx3x : x ≤ x ^ 3 := by
    have h := pow_le_pow_right₀ hx1 (by norm_num : (1 : ℕ) ≤ 3)
    simpa using h
  have hx31 : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ hx1
  have hlog2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have ht7 : Real.log (|t| + 7) ≤ x := by
    have hpos : (0 : ℝ) < |t| + 3 := by linarith only [abs_nonneg t]
    have hle : (|t| + 7 : ℝ) ≤ 2 * (|t| + 3) := by linarith only [ht]
    calc Real.log (|t| + 7) ≤ Real.log (2 * (|t| + 3)) :=
          Real.log_le_log (by linarith only [abs_nonneg t]) hle
      _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (ne_of_gt hpos)
      _ ≤ 1 + Real.log (|t| + 3) := by linarith only [hlog2]
      _ = x := by rw [hx]; ring
  have ht6 : Real.log (|t| + 6) ≤ x := by
    have hpos : (0 : ℝ) < |t| + 3 := by linarith only [abs_nonneg t]
    have hle : (|t| + 6 : ℝ) ≤ 2 * (|t| + 3) := by linarith only [abs_nonneg t]
    calc Real.log (|t| + 6) ≤ Real.log (2 * (|t| + 3)) :=
          Real.log_le_log (by linarith only [abs_nonneg t]) hle
      _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (ne_of_gt hpos)
      _ ≤ 1 + Real.log (|t| + 3) := by linarith only [hlog2]
      _ = x := by rw [hx]; ring
  have hlogA : Real.log A ≤ Real.log (4 * Cg + 1) + 15 * Real.log (|t| + 7) := by
    have h7 : (1 : ℝ) ≤ (|t| + 7) ^ 15 := one_le_pow₀ (by linarith only [abs_nonneg t])
    have hle : A ≤ (4 * Cg + 1) * (|t| + 7) ^ 15 := by
      rw [hA]; nlinarith only [h7]
    calc Real.log A ≤ Real.log ((4 * Cg + 1) * (|t| + 7) ^ 15) :=
          Real.log_le_log hApos hle
      _ = Real.log (4 * Cg + 1) + Real.log ((|t| + 7) ^ 15) :=
          Real.log_mul (by linarith only [hCgpos]) (by positivity)
      _ = Real.log (4 * Cg + 1) + 15 * Real.log (|t| + 7) := by
          rw [Real.log_pow]; ring
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hclb : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
    simpa only [hc] using zeta1_re_two_lower t
  have hfc : riemannZeta₁ c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hclb
    norm_num at hclb
  have hAb : ∀ w : ℂ, ‖w - c‖ = R → ‖riemannZeta₁ w‖ ≤ A * ‖riemannZeta₁ c‖ := by
    intro w hw
    have hle4 : ‖w - c‖ ≤ 4 := by rw [hw]; exact hR4
    have hgw : ‖riemannZeta₁ w‖ ≤ Cg * (|t| + 7) ^ 15 := hCgb t ht w (by simpa only [hc] using hle4)
    calc ‖riemannZeta₁ w‖ ≤ Cg * (|t| + 7) ^ 15 := hgw
      _ = 4 * Cg * (|t| + 7) ^ 15 * (1 / 4) := by ring
      _ ≤ 4 * Cg * (|t| + 7) ^ 15 * ‖riemannZeta₁ c‖ :=
          mul_le_mul_of_nonneg_left hclb hX0
      _ ≤ (4 * Cg * (|t| + 7) ^ 15 + 1) * ‖riemannZeta₁ c‖ :=
          mul_le_mul_of_nonneg_right (by linarith only [hApos]) (norm_nonneg _)
      _ = A * ‖riemannZeta₁ c‖ := by rw [hA]
  have hmain : ‖logDeriv riemannZeta₁ s - S‖ ≤ 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2) :=
    Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := riemannZeta₁) (c := c) (R := R)
      (A := A) (α := (13 / 28 : ℝ))
      hRpos hA1 (by norm_num) (by norm_num)
      (fun z _ => differentiable_riemannZeta₁.analyticAt z) hfc
      (fun w hw => hcircR w (by simpa only [hc] using hw))
      (fun w hw => hcircR2 w (by simpa only [hc] using hw))
      hAb hs_le hfs
  -- Step 1: rewrite T in terms of d
  have hTeq : T = ∑ᶠ u : ℂ,
      (((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (1 / (s - u)) else 0)) := by
    rw [hT]
    apply finsum_congr
    intro u
    by_cases h : ‖s - u‖ ≤ (1 / 8 : ℝ)
    · have hu : u ∈ Metric.closedBall c (R / 2) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : ‖u - c‖ ≤ ‖u - s‖ + ‖s - c‖ := by
          calc ‖u - c‖ = ‖(u - s) + (s - c)‖ := by congr 1; ring
            _ ≤ ‖u - s‖ + ‖s - c‖ := norm_add_le _ _
        have h2 : ‖u - s‖ = ‖s - u‖ := norm_sub_rev _ _
        linarith only [h1, h2, h, hs13, hR72]
      have hDd : D u = d u :=
        (divisor_riemannZeta1_eq_completedRiemannZeta_ball (t := t) (R := R) ht hRpos hR4 hu).symm
      rw [if_pos h, if_pos h, hDd, one_div]
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  -- Step 2: S - T as a finsum
  have hAfin : Function.HasFiniteSupport (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s - u))) := by
    refine hd_fin.subset ?_
    rw [Function.support_subset_iff]
    intro u hu hdu
    exact hu (by rw [hdu]; simp)
  have hBfin : Function.HasFiniteSupport
      (fun u : ℂ => ((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (1 / (s - u)) else 0)) := by
    refine hd_fin.subset ?_
    rw [Function.support_subset_iff]
    intro u hu hdu
    exact hu (by rw [hdu]; simp)
  have hST : S - T = ∑ᶠ u : ℂ,
      (((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then 0 else (s - u)⁻¹)) := by
    rw [hS, hTeq]
    rw [← finsum_sub_distrib hAfin hBfin]
    apply finsum_congr
    intro u
    by_cases h : ‖s - u‖ ≤ (1 / 8 : ℝ)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero, sub_zero, one_div]
  -- Step 3: bound
  have hST_bound : ‖S - T‖ ≤ 8 * ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
    rw [hST]
    have hg : Function.HasFiniteSupport (fun u : ℂ => 8 * ((d u : ℤ) : ℝ)) := by
      refine hd_fin.subset ?_
      rw [Function.support_subset_iff]
      intro u hu hdu
      exact hu (by rw [hdu]; simp)
    have hbound := norm_finsum_le_of_norm_le_la' (f := fun u : ℂ =>
        ((d u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then 0 else (s - u)⁻¹))
      (g := fun u : ℂ => 8 * ((d u : ℤ) : ℝ)) hg (by
        intro u
        have hdnn : (0 : ℤ) ≤ d u :=
          (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁)
            (U := Metric.closedBall c (R / 2))
            (fun z _ => differentiable_riemannZeta₁.analyticAt z)) u
        have hdu : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := Int.cast_nonneg hdnn
        by_cases h : ‖s - u‖ ≤ (1 / 8 : ℝ)
        · rw [if_pos h, mul_zero, norm_zero]
          exact mul_nonneg (by norm_num) hdu
        · rw [if_neg h]
          have hnorm : ‖((d u : ℤ) : ℂ) * (s - u)⁻¹‖ = ((d u : ℤ) : ℝ) * ‖s - u‖⁻¹ := by
            rw [norm_mul, norm_inv, Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg hdnn)]
          rw [hnorm]
          have hgt : (1 / 8 : ℝ) < ‖s - u‖ := lt_of_not_ge h
          have hle : ‖s - u‖⁻¹ ≤ 8 := by
            rw [← one_div]
            simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 8) (le_of_lt hgt)
          calc ((d u : ℤ) : ℝ) * ‖s - u‖⁻¹ ≤ ((d u : ℤ) : ℝ) * 8 :=
                mul_le_mul_of_nonneg_left hle hdu
            _ = 8 * ((d u : ℤ) : ℝ) := by ring)
    have hmul : (∑ᶠ u : ℂ, 8 * ((d u : ℤ) : ℝ)) = 8 * ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) :=
      (mul_finsum (fun u : ℂ => ((d u : ℤ) : ℝ)) 8).symm
    rw [hmul] at hbound
    exact hbound
  have hdivle : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) ≤ K * (Real.log (|t| + 6) + 1) :=
    hKb t ht R hRpos hR4
  -- Step 4: the log arithmetic
  have hbound1 : 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2) ≤ 224 * Real.log A := by
    have hdsq : (1 - 2 * (13 / 28 : ℝ)) ^ 2 = 1 / 196 := by norm_num
    rw [hdsq, div_le_iff₀ (mul_pos hRpos (by norm_num : (0 : ℝ) < 1 / 196))]
    have hkey : (4 : ℝ) ≤ 224 * R * (1 / 196) := by nlinarith only [hR72]
    have hh := mul_le_mul_of_nonneg_right hkey hlogA0
    nlinarith only [hh]
  have hb1 : 224 * Real.log A ≤ 224 * (Real.log (4 * Cg + 1) + 15 * x) := by
    have hmid : Real.log A ≤ Real.log (4 * Cg + 1) + 15 * x := by linarith only [hlogA, ht7]
    exact mul_le_mul_of_nonneg_left hmid (by norm_num)
  have hb2 : 8 * (K * (Real.log (|t| + 6) + 1)) ≤ 16 * K * x ^ 3 := by
    have h1 : Real.log (|t| + 6) + 1 ≤ 2 * x := by linarith only [ht6, hx1]
    have hK0 : (0 : ℝ) ≤ 8 * K := mul_nonneg (by norm_num) (le_of_lt hKpos)
    have h2 : 8 * K * (Real.log (|t| + 6) + 1) ≤ 8 * K * (2 * x) :=
      mul_le_mul_of_nonneg_left h1 hK0
    have h3 : 8 * K * (2 * x) ≤ 16 * K * x ^ 3 := by
      have hK1 : (0 : ℝ) ≤ 16 * K := mul_nonneg (by norm_num) (le_of_lt hKpos)
      have hh := mul_le_mul_of_nonneg_left hx3x hK1
      nlinarith only [hh]
    linarith only [h2, h3]
  have hfin : 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2)
        + 8 * (K * (Real.log (|t| + 6) + 1))
      ≤ (224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1) * x ^ 3 := by
    have h3 : 224 * (Real.log (4 * Cg + 1) + 15 * x) + 16 * K * x ^ 3
        ≤ (224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1) * x ^ 3 := by
      have hlogC0 : 0 ≤ Real.log (4 * Cg + 1) := Real.log_nonneg (by linarith only [hCgpos])
      have ha : 224 * Real.log (4 * Cg + 1) ≤ 224 * Real.log (4 * Cg + 1) * x ^ 3 := by
        have hh := mul_nonneg hlogC0 (by linarith only [hx31] : (0 : ℝ) ≤ x ^ 3 - 1)
        nlinarith only [hh]
      have hb : 3360 * x ≤ 3361 * x ^ 3 := by
        have hh := mul_le_mul_of_nonneg_left hx3x (by norm_num : (0 : ℝ) ≤ 3360)
        nlinarith only [hh, hx31]
      nlinarith only [ha, hb]
    linarith only [hbound1, hb1, hb2, h3]
  calc ‖logDeriv riemannZeta₁ s - T‖
      ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S - T‖ := by
        simpa [dist_eq_norm] using dist_triangle (logDeriv riemannZeta₁ s) S T
    _ ≤ 4 * Real.log A / (R * (1 - 2 * (13 / 28 : ℝ)) ^ 2) + 8 * (K * (Real.log (|t| + 6) + 1)) := by
        linarith only [hmain, hST_bound, hdivle]
    _ ≤ (224 * (Real.log (4 * Cg + 1) + 15) + 16 * K + 1) * (Real.log (|t| + 3) + 1) ^ 3 := hfin




set_option maxHeartbeats 1000000


theorem zeta1_logDeriv_goodHeight_delta_b (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 10 ^ 7 ∧ ∀ T δ : ℝ, 5 ≤ T → 0 < δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1/2 : ℝ) ≤ σ → σ ≤ (5/8 : ℝ) →
        ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * ((Real.log (T + 3) + 1) ^ 3 + (Real.log (T + 3) + 1) ^ 2 / δ) := by
  obtain ⟨C₁, hC₁pos, hC₁le, hC₁⟩ := zeta_logDeriv_local_approx_ne_b
  obtain ⟨K, hKpos, hKle, hK⟩ := riemannZeta1_ball_divisor_le_log_b
  refine ⟨C₁ + 2 * K + 1, by linarith, by linarith, ?_⟩
  intro T δ hT hδ0 hgood σ hσlo hσhi
  -- basic set-up
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  set c : ℂ := (2 : ℂ) + Complex.I * (T : ℂ) with hc
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c ((13 : ℝ) / 8)) u with hd
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall c (3 : ℝ)) u with hD
  set S : ℂ := ∑ᶠ u : ℂ,
    (((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0)) with hS
  have hTabs : 5 ≤ |T| := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]; exact hT
  have hTpos : 0 < T := by linarith
  have hs_im : s.im = T := by rw [hs]; simp
  have hs_re : s.re = σ := by rw [hs]; simp
  -- ζ₁ is nonzero at s, because s itself would be a zero too close to the height T
  have hs_ne : riemannZeta₁ s ≠ 0 := by
    intro h0
    have h1 := hgood s h0
    rw [hs_im] at h1
    simp at h1
    linarith
  -- the local approximation of the logarithmic derivative
  have hloc : ‖logDeriv riemannZeta₁ s - S‖ ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 := by
    have h0 := hC₁ T hTabs σ (by linarith) hσhi (by simpa [hs] using hs_ne)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] at h0
    simpa [hs, hc, hd, hD, hS] using h0
  -- analyticity of ζ₁ on the ball of radius 13/8
  have hζ1an : AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall c ((13 : ℝ) / 8)) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hdnn : ∀ u : ℂ, (0 : ℤ) ≤ d u := by
    intro u
    have hh := MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁) hζ1an
    simpa [hd] using hh u
  have hd_fin : Function.HasFiniteSupport d := by
    have hsupp := (MeromorphicOn.divisor riemannZeta₁
      (Metric.closedBall c ((13 : ℝ) / 8))).finiteSupport (isCompact_closedBall c ((13 : ℝ) / 8))
    simpa [Function.HasFiniteSupport, hd] using hsupp
  -- pointwise bound for the summand
  have hbound : ∀ u : ℂ,
      ‖((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0)‖ ≤ (d u : ℝ) / δ := by
    intro u
    have hdu0 : (0 : ℝ) ≤ (d u : ℝ) := Int.cast_nonneg (hdnn u)
    by_cases h1 : ‖s - u‖ ≤ (1 / 8 : ℝ)
    · rw [if_pos h1]
      -- u lies in the ball of radius 13/8 around c
      have hu_mem : u ∈ Metric.closedBall c ((13 : ℝ) / 8) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsc : ‖s - c‖ = 2 - σ := by
          have h1' : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
          rw [h1', Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          ring
        have h2 : ‖u - c‖ ≤ ‖u - s‖ + ‖s - c‖ := by
          calc ‖u - c‖ = ‖(u - s) + (s - c)‖ := by congr 1; ring
            _ ≤ ‖u - s‖ + ‖s - c‖ := norm_add_le _ _
        rw [norm_sub_rev u s] at h2
        linarith [h2, h1, hsc, hσlo]
      -- identify the divisors
      have hDd : D u = d u := by
        have hR2 : (13 : ℝ) / 4 / 2 = 13 / 8 := by norm_num
        have huR : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (T : ℂ)) ((13 : ℝ) / 4 / 2) := by
          simpa [hR2, hc] using hu_mem
        have h := divisor_riemannZeta1_eq_completedRiemannZeta_ball (t := T) (R := (13 : ℝ) / 4)
            hTabs (by norm_num) (by norm_num) (u := u) huR
        rw [hR2] at h
        simpa [hd, hD, hc] using h.symm
      rw [hDd]
      by_cases hdu : d u = 0
      · rw [hdu]; simp
      · have hdu' : 0 < d u := lt_of_le_of_ne (hdnn u) (Ne.symm hdu)
        -- ζ₁ vanishes at u, so u is far from the height T
        have hz : riemannZeta₁ u = 0 := by
          by_contra hz0
          have hord : analyticOrderAt riemannZeta₁ u = 0 :=
            ((differentiable_riemannZeta₁.analyticAt u).analyticOrderAt_eq_zero).mpr hz0
          have hzero : d u = 0 := by
            have hh : MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c ((13 : ℝ) / 8)) u = 0 := by
              rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζ1an hu_mem, hord]
              simp
            simpa [hd] using hh
          exact hdu hzero
        have hfar : δ ≤ |u.im - T| := hgood u hz
        have hdist : δ ≤ ‖s - u‖ := by
          have him : (s - u).im = T - u.im := by rw [Complex.sub_im, hs_im]
          calc δ ≤ |u.im - T| := hfar
            _ = |T - u.im| := by rw [abs_sub_comm]
            _ = |(s - u).im| := by rw [him]
            _ ≤ ‖s - u‖ := Complex.abs_im_le_norm _
        have hinv : ‖s - u‖⁻¹ ≤ δ⁻¹ := by
          have hpos : 0 < ‖s - u‖ := lt_of_lt_of_le hδ0 hdist
          exact (inv_le_inv₀ hpos hδ0).mpr hdist
        calc ‖((d u : ℤ) : ℂ) * (s - u)⁻¹‖
            = (d u : ℝ) * ‖s - u‖⁻¹ := by
              rw [norm_mul, norm_inv, Complex.norm_intCast, abs_of_nonneg hdu0]
          _ ≤ (d u : ℝ) * δ⁻¹ := mul_le_mul_of_nonneg_left hinv hdu0
          _ = (d u : ℝ) / δ := by rw [div_eq_mul_inv]
    · rw [if_neg h1]
      simp only [mul_zero, norm_zero]
      exact div_nonneg hdu0 (le_of_lt hδ0)
  -- the divisor bound
  have hdivsum : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) ≤ K * (Real.log (T + 6) + 1) := by
    have hKb := hK T hTabs ((13 : ℝ) / 4) (by norm_num) (by norm_num)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] at hKb
    have hR2 : (13 : ℝ) / 4 / 2 = 13 / 8 := by norm_num
    rw [hR2] at hKb
    simpa [hd, hc] using hKb
  -- bound ‖S‖
  have hS_bound : ‖S‖ ≤ (1 / δ) * (K * (Real.log (T + 6) + 1)) := by
    have hgfin : Function.HasFiniteSupport (fun u : ℂ => (d u : ℝ) / δ) := by
      refine hd_fin.subset ?_
      rw [Function.support_subset_iff]
      intro u hu
      rw [Function.mem_support]
      intro hu0
      exact hu (by rw [hu0]; simp)
    have hbn := Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le
      (f := fun u : ℂ => ((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0))
      (g := fun u : ℂ => (d u : ℝ) / δ) hgfin hbound
    rw [hS]
    refine le_trans hbn ?_
    have hsum_eq : (∑ᶠ u : ℂ, (d u : ℝ) / δ) = (1 / δ) * ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
      rw [mul_finsum]
      apply finsum_congr
      intro u
      rw [div_eq_mul_inv, one_div]
      ring
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hdivsum (le_of_lt (one_div_pos.mpr hδ0))
  -- arithmetic
  let L : ℝ := Real.log (T + 3) + 1
  have hL1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlogT6 : Real.log (T + 6) + 1 ≤ 2 * L := by
    have hle : T + 6 ≤ (T + 3) ^ 2 := by nlinarith
    have hmono : Real.log (T + 6) ≤ Real.log ((T + 3) ^ 2) :=
      Real.log_le_log (by linarith) hle
    rw [Real.log_pow] at hmono
    push_cast at hmono
    dsimp [L]
    linarith
  -- here we keep the `1/δ` factor instead of assuming `1 ≤ L * δ`
  have hSb : ‖S‖ ≤ 2 * K * L ^ 2 / δ := by
    have hstep1 : (1 / δ) * (K * (Real.log (T + 6) + 1)) ≤ (1 / δ) * (K * (2 * L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogT6 (le_of_lt hKpos))
        (by positivity)
    have hLle : L ≤ L ^ 2 := by
      simpa using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 2)
    have hstep2 : (1 / δ) * (K * (2 * L)) ≤ (1 / δ) * (K * (2 * L ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hKpos)) (by positivity)
    calc ‖S‖ ≤ (1 / δ) * (K * (Real.log (T + 6) + 1)) := hS_bound
      _ ≤ (1 / δ) * (K * (2 * L)) := hstep1
      _ ≤ (1 / δ) * (K * (2 * L ^ 2)) := hstep2
      _ = 2 * K * L ^ 2 / δ := by rw [div_eq_mul_inv]; ring
  -- assemble
  have hfinal : ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ ≤
      (C₁ + 2 * K + 1) * (L ^ 3 + L ^ 2 / δ) := by
    have h1 : ‖logDeriv riemannZeta₁ s - S‖ ≤ C₁ * L ^ 3 := by simpa [L] using hloc
    have h2 : ‖S‖ ≤ 2 * K * (L ^ 2 / δ) := by
      have h := hSb
      rwa [mul_div_assoc] at h
    have h3 : (0 : ℝ) ≤ L ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ L ^ 2 / δ := by positivity
    have hprod1 : (0 : ℝ) ≤ (2 * K + 1) * L ^ 3 := mul_nonneg (by linarith) h3
    have hprod2 : (0 : ℝ) ≤ (C₁ + 1) * (L ^ 2 / δ) := mul_nonneg (by linarith) h4
    have key : C₁ * L ^ 3 + 2 * K * (L ^ 2 / δ) ≤ (C₁ + 2 * K + 1) * (L ^ 3 + L ^ 2 / δ) := by
      nlinarith [hprod1, hprod2, h3, h4]
    linarith [h1, h2, key]
  have htri : ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ := by
    have := norm_add_le (logDeriv riemannZeta₁ s - S) S
    simpa using this
  calc ‖logDeriv riemannZeta₁ (((σ : ℂ) + Complex.I * (T : ℂ)) : ℂ)‖
      = ‖logDeriv riemannZeta₁ s‖ := by rw [hs]
    _ ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ := htri
    _ ≤ (C₁ + 2 * K + 1) * (L ^ 3 + L ^ 2 / δ) := hfinal
    _ = (C₁ + 2 * K + 1) *
          ((Real.log (T + 3) + 1) ^ 3 + (Real.log (T + 3) + 1) ^ 2 / δ) := rfl


set_option maxHeartbeats 1000000


/-!
# Bounding `logDeriv ζ₁` on the negative strip `−3/2 ≤ Re s ≤ −1/2`

For `s = σ + i t` with `−3/2 ≤ σ ≤ −1/2` and `|t| ≥ 2`, its reflection `1 − s` has
real part `1 − σ ∈ [3/2, 5/2]`, deep inside the half-plane of absolute convergence
`Re w > 1`.  The functional equation in logarithmic-derivative form
(`zeta_logDeriv_fe_expanded`)

    ζ'/ζ (s) = log(2π) − ψ(1−s) + (π/2)·tan(π(1−s)/2) − ζ'/ζ (1−s)

then bounds `ζ'/ζ (s)` by

* a constant `M` for the reflected term `ζ'/ζ (1−s)` (`logDeriv_zeta_const_bound`,
  from the absolutely convergent von-Mangoldt Dirichlet series `−ζ'/ζ = ∑ Λ(n) n^{-w}`
  valid for `Re w > 1`; here moreover `Re (1−s) ≥ 3/2`),
* the digamma bound `‖ψ(1−s)‖ ≤ 3 L³` (`digamma_mid_strip_le`), and
* the tangent bound `‖(π/2)·tan(π(1−s)/2)‖ ≤ 2π L³` (`tan_norm_le_of_abs_im_ge`, using
  `|Im (π(1−s)/2)| = (π/2)|t| ≥ π ≥ 1`),

with `L_ns = log(|t|+3)+1 ≥ 1`.  Finally `logDeriv ζ₁ = ζ'/ζ + 1/(s−1)` with `1/‖s−1‖ ≤ 1`.

The Riemann hypothesis only enters through the nonvanishing of `ζ` on the strip (a zero
there would have real part `1/2`); the analytic bounds themselves are unconditional.
-/

/-- A constant bound for `‖ζ'/ζ‖` in the half-plane `Re ≥ 3/2`, coming from the absolutely
convergent von-Mangoldt Dirichlet series `−ζ'/ζ(w) = ∑ Λ(n) n^{-w}`. -/
theorem logDeriv_zeta_const_bound_b :
    ∃ M : ℝ, 0 < M ∧ M ≤ 28 ∧ ∀ w : ℂ, (3 / 2 : ℝ) ≤ w.re →
      ‖deriv riemannZeta w / riemannZeta w‖ ≤ M := by
  set F : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hFdef
  have hsum : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
      (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    summable_vonMangoldt_div_rpow (by norm_num)
  refine ⟨(∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)) + 1,
    by positivity, ?_, ?_⟩
  · have hsum54 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
        (n : ℝ) ^ ((5 : ℝ) / 4)) := summable_vonMangoldt_div_rpow (by norm_num)
    have hle : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) ≤
        (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 4) := by
      intro n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        have hnp : (0 : ℝ) < (n : ℝ) := by linarith
        have hpow : (n : ℝ) ^ ((5 : ℝ) / 4) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        have hinv : ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ ≤ ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hnp _) (Real.rpow_pos_of_pos hnp _)).mpr hpow
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv ArithmeticFunction.vonMangoldt_nonneg
    have h27 := Commons.NumberTheory.Zeta.vonMangoldt_rpow_five_fourths_tsum_le
    have hcmp := Summable.tsum_le_tsum hle hsum hsum54
    linarith
  intro w hw
  have hw1 : (1 : ℝ) < w.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := w) hw1
  have hsumm : Summable (LSeries.term F w) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := w) hw1
    rw [LSeriesSummable] at h
    simpa [F] using h
  have hnormsum : Summable (fun n => ‖LSeries.term F w n‖) := summable_norm_iff.mpr hsumm
  have h1 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ ∑' n, ‖LSeries.term F w n‖ := by
    rw [show deriv riemannZeta w / riemannZeta w = - LSeries F w by rw [hL]; ring]
    rw [norm_neg, LSeries]
    exact norm_tsum_le_tsum_norm hnormsum
  have h2 : (∑' n, ‖LSeries.term F w n‖) ≤
      ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    apply Summable.tsum_le_tsum ?_ hnormsum hsum
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hnormF : ‖F n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simp [F, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      rw [hnormF]
      apply div_le_div_of_nonneg_left hΛ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hn1 hw
  linarith

/-- Under RH, `ζ` has no zero on the strip `−3/2 ≤ Re s ≤ −1/2`: a zero there is not a trivial
zero (`−2, −4, …` all have real part `≤ −2`), so the Riemann hypothesis forces real part `1/2`. -/
private lemma zeta_ne_zero_of_rh_neg_strip_ns (h : RiemannHypothesis) {s : ℂ}
    (hlo : -(3 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ -(1 / 2 : ℝ)) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hren : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by norm_num
    rw [hren] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    linarith
  have hhalf : s.re = 1 / 2 := h s hz htriv hs1
  linarith

/-- If `0 < re w` then `w` avoids the non-positive integers. -/
private lemma ne_neg_nat_of_re_pos_ns {w : ℂ} (hw : (0 : ℝ) < w.re) : ∀ n : ℕ, w ≠ -(n : ℂ) := by
  intro n hn
  have hre := congrArg Complex.re hn
  have hren : (-(n : ℂ)).re = -((n : ℝ)) := by simp
  rw [hren] at hre
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hnn : -((n : ℝ)) ≤ 0 := by linarith
  linarith

/-- The cosine factor `cos (π(1−s)/2)` of the functional equation is nonzero whenever
`im s ≠ 0`, because it vanishes only at real points `s = −2k`. -/
private lemma cos_pi_one_sub_two_ne_zero_of_im_ne_zero_ns {s : ℂ} (ht : s.im ≠ 0) :
    Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
  intro hz
  rcases Complex.cos_eq_zero_iff.mp hz with ⟨k, hk⟩
  have hz_im0 : (↑Real.pi * (1 - s) / 2).im = 0 := by
    rw [hk]
    simp
  have hzi_ne : (↑Real.pi * (1 - s) / 2).im ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hne : (Real.pi / 2) ≠ 0 := div_ne_zero hpi (by norm_num)
    have : -(Real.pi / 2) * s.im ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hne) ht
    simpa [Complex.mul_im] using this
  exact hzi_ne hz_im0

/-- `ζ₁ = (s−1)·ζ` in logarithmic-derivative form (for `s ≠ 1` with `ζ s ≠ 0`). -/
private lemma zeta1_logDeriv_eq_ns (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := by
  have hEq : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hzne
    have hz := riemannZeta_eq_inv_sub_mul hzne
    calc
      riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hzne)]
        simp
      _ = (z - 1) * riemannZeta z := by rw [hz]
  have hcong := logDeriv_congr_nhds hEq
  have hval : logDeriv riemannZeta₁ s = logDeriv (fun z => (z - 1) * riemannZeta z) s :=
    hcong.self_of_nhds
  rw [hval]
  have hmul := logDeriv_mul (x := s) (f := fun z => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζs (by fun_prop) (differentiableAt_riemannZeta hs1)
  simp only [Pi.mul_def] at hmul
  rw [hmul]
  have hld_id : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => z - 1) s = 1 := by
      simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
    rw [hd]
    simp
  rw [hld_id, logDeriv_apply]
  ring

/-- `‖logDeriv ζ₁ s‖ ≤ ‖ζ'/ζ (s)‖ + 1/‖s−1‖` for `s ≠ 1` with `ζ s ≠ 0`. -/
private lemma norm_zeta1_logDeriv_le_ns (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta₁ s‖ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
  rw [zeta1_logDeriv_eq_ns s hs1 hζs]
  exact norm_add_le _ _

/-- The logarithmic factor `L_ns(t) := log (|t| + 3) + 1`. -/
private def L_ns (t : ℝ) : ℝ := Real.log (|t| + 3) + 1

private lemma L_ge_one_ns (t : ℝ) (ht : (2 : ℝ) ≤ |t|) : (1 : ℝ) ≤ L_ns t := by
  dsimp [L_ns]
  have h : 0 ≤ Real.log (|t| + 3) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  linarith

private lemma L_pow3_ge_one_ns (t : ℝ) (ht : (2 : ℝ) ≤ |t|) : (1 : ℝ) ≤ (L_ns t) ^ 3 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (L_ge_one_ns t ht) 3
  simpa using h

/-- Norm of the constant `log(2π)` equals `log (2π)`. -/
private lemma norm_log_two_pi_ns : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ = Real.log (2 * Real.pi) := by
  have h0le : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hclog : Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) :=
    (Complex.ofReal_log h0le).symm
  rw [hclog]
  have hnon : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  exact Complex.norm_of_nonneg hnon

/-- `log (2π) · L_ns(t)³` absorbs the constant `log(2π)`. -/
private lemma log_two_pi_mul_L3_le_ns (t : ℝ) (ht : (2 : ℝ) ≤ |t|) :
    Real.log (2 * Real.pi) ≤ Real.log (2 * Real.pi) * (L_ns t) ^ 3 := by
  have hnon : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  calc
    Real.log (2 * Real.pi) = Real.log (2 * Real.pi) * 1 := by ring
    _ ≤ Real.log (2 * Real.pi) * (L_ns t) ^ 3 := by
      exact mul_le_mul_of_nonneg_left (L_pow3_ge_one_ns t ht) hnon

/-- Digamma bound on the reflected point `1 − s = (1−σ) − i t`: `‖ψ‖ ≤ log(2 + |t|) + 2`. -/
private lemma digamma_bound_ns {σ t : ℝ} (hlo : -(3 / 2 : ℝ) ≤ σ) (hhi : σ ≤ -(1 / 2 : ℝ)) :
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.log (2 + |t|) + 2 := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hx1 : (1 / 2 : ℝ) ≤ 1 - σ := by linarith
  have hx2 : 1 - σ ≤ 8 := by linarith
  have hmid := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (1 - σ) (-t) hx1 hx2
  have harg : ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = 1 - s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  rw [← harg]
  simpa using hmid

/-- Polynomial-in-`log` digamma bound: `‖ψ (1−s)‖ ≤ 3 L_ns(t)³`. -/
private lemma digamma_poly_bound_ns {σ t : ℝ} (hlo : -(3 / 2 : ℝ) ≤ σ) (hhi : σ ≤ -(1 / 2 : ℝ))
    (ht : (2 : ℝ) ≤ |t|) :
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ 3 * (L_ns t) ^ 3 := by
  change ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
    3 * (Real.log (|t| + 3) + 1) ^ 3
  have hb := digamma_bound_ns (σ := σ) (t := t) hlo hhi
  have hlelog : Real.log (2 + |t|) ≤ Real.log (|t| + 3) := by
    apply Real.log_le_log
    · positivity
    · linarith [abs_nonneg t]
  have hX1 : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
    have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hX : Real.log (|t| + 3) + 1 ≤ (Real.log (|t| + 3) + 1) ^ 3 := by
    have hp := pow_le_pow_right₀ hX1 (by norm_num : (1 : ℕ) ≤ 3)
    simpa using hp
  calc
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.log (2 + |t|) + 2 := hb
    _ ≤ Real.log (|t| + 3) + 2 := by linarith
    _ ≤ 3 * (Real.log (|t| + 3) + 1) := by
      have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    _ ≤ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by
      exact mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 3)

/-- Imaginary part of the tangent argument `π (1−s)/2`. -/
private lemma tan_arg_im_ns {σ t : ℝ} (s : ℂ) (hsim : s.im = t) :
    (↑Real.pi * (1 - s) / 2).im = -(Real.pi / 2) * t := by
  calc
    (↑Real.pi * (1 - s) / 2).im = -(Real.pi / 2) * s.im := by
      simp [Complex.mul_im]
      ring
    _ = -(Real.pi / 2) * t := by rw [hsim]

/-- `|Im (π(1−s)/2)| = (π/2)·|t|`, and in particular is `≥ 1` for `|t| ≥ 2`. -/
private lemma tan_arg_abs_ns (σ t : ℝ) (ht : (2 : ℝ) ≤ |t|) :
    (1 : ℝ) ≤ |(↑Real.pi * (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) / 2).im| := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsim : s.im = t := by simp [s]
  have hE : |(↑Real.pi * (1 - s) / 2).im| = (Real.pi / 2) * |t| := by
    rw [tan_arg_im_ns (σ := σ) (t := t) s hsim]
    have hpi : 0 < Real.pi / 2 := by positivity
    rw [abs_mul, abs_neg]
    rw [abs_of_pos hpi]
  rw [hE]
  nlinarith [Real.two_le_pi, ht]

/-- Polynomial-in-`log` bound for the tangent term `(π/2)·tan u` with `|Im u| ≥ 1`:
`≤ 2π · L_ns(t)³`. -/
private lemma tan_term_poly_bound_ns (u : ℂ) (hu : (1 : ℝ) ≤ |u.im|) {t : ℝ}
    (ht : (2 : ℝ) ≤ |t|) :
    ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan u‖ ≤ 2 * Real.pi * (L_ns t) ^ 3 := by
  have htan : ‖Complex.tan u‖ ≤ 4 :=
    Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge u hu
  calc
    ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan u‖
        = ‖((Real.pi / 2 : ℝ) : ℂ)‖ * ‖Complex.tan u‖ := by rw [norm_mul]
    _ = (Real.pi / 2) * ‖Complex.tan u‖ := by
            congr 1
            exact Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    _ ≤ (Real.pi / 2) * 4 := by
            exact mul_le_mul_of_nonneg_left htan (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    _ = 2 * Real.pi := by ring
    _ ≤ 2 * Real.pi * (L_ns t) ^ 3 := by
            simpa using mul_le_mul_of_nonneg_left (L_pow3_ge_one_ns t ht)
              (by positivity : (0 : ℝ) ≤ 2 * Real.pi)

/-- `1/‖s−1‖ ≤ 1` on the strip `|t| ≥ 2`. -/
private lemma inv_sub_one_le_one_ns (σ t : ℝ) (ht : (2 : ℝ) ≤ |t|) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ) - 1)⁻¹‖ ≤ 1 := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsim : s.im = t := by simp [s]
  have hs1n : (1 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (1 : ℝ) ≤ |t| / 2 := by linarith
      _ ≤ |t| := by
        have ht0 : 0 ≤ |t| := abs_nonneg t
        linarith
      _ = |(s - 1).im| := by simp [hsim]
      _ ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
  have hpos : 0 < ‖s - 1‖ := by linarith
  rw [norm_inv]
  exact (inv_le_one₀ hpos).mpr hs1n

/-- The assembled constant is positive. -/
private lemma negstrip_const_pos_ns {M : ℝ} (hM : 0 < M) :
    0 < M + Real.log (2 * Real.pi) + 2 * Real.pi + 4 := by
  have hlog : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.two_le_pi])
  linarith [Real.pi_pos]

/-- The requested bound for the logarithmic derivative of the entire function `ζ₁`
on the strip `−3/2 ≤ σ ≤ −1/2`, `|t| ≥ 2`, assuming the Riemann hypothesis. -/
theorem zeta_logDeriv_negStrip_bound_b (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧ ∀ σ t : ℝ, -(3 / 2 : ℝ) ≤ σ → σ ≤ -(1 / 2 : ℝ) → 2 ≤ |t| →
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 := by
  rcases logDeriv_zeta_const_bound_b with ⟨M, hMpos, hMle, hMb⟩
  let C : ℝ := M + Real.log (2 * Real.pi) + 2 * Real.pi + 4
  have hCpos : 0 < C := negstrip_const_pos_ns hMpos
  refine ⟨C, hCpos, ?_, ?_⟩
  · have hlog2pi : Real.log (2 * Real.pi) ≤ 7 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
      have h2 := Real.pi_lt_four
      linarith
    have hpi8 : 2 * Real.pi ≤ 8 := by have := Real.pi_lt_four; linarith
    dsimp only [C]
    linarith
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let Lv : ℝ := L_ns t
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have ht_ne : t ≠ 0 := by
    intro ht0
    rw [ht0] at ht
    norm_num at ht
  have hs0 : s ≠ 0 := by
    intro hs0'
    have h : s.im = 0 := by rw [hs0']; simp
    rw [hsim] at h
    exact ht_ne h
  have hs1 : s ≠ 1 := by
    intro hs1'
    have h : s.re = (1 : ℂ).re := congrArg Complex.re hs1'
    rw [hsre] at h
    norm_num at h
    linarith
  have hζs : riemannZeta s ≠ 0 := zeta_ne_zero_of_rh_neg_strip_ns h (by rw [hsre]; exact hσlo)
    (by rw [hsre]; exact hσhi) hs1
  have hre_w : (3 / 2 : ℝ) ≤ (1 - s).re := by
    have hsub : (1 - s).re = 1 - σ := by rw [Complex.sub_re, hsre]; norm_num
    rw [hsub]; linarith
  have hζw : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hre_w0 : (0 : ℝ) < (1 - s).re := by linarith
  have hΓ : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := ne_neg_nat_of_re_pos_ns hre_w0
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    apply cos_pi_one_sub_two_ne_zero_of_im_ne_zero_ns
    rw [hsim]
    exact ht_ne
  have hFE := zeta_logDeriv_fe_expanded hζs hζw hs0 hs1 hΓ hcos
  have hFE' : deriv riemannZeta s / riemannZeta s =
      Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
          deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
    simpa using hFE
  have hL3 : (1 : ℝ) ≤ Lv ^ 3 := by dsimp [Lv]; exact L_pow3_ge_one_ns t ht
  -- the constant term
  have hbnd_log : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ ≤ Real.log (2 * Real.pi) * Lv ^ 3 := by
    rw [norm_log_two_pi_ns]
    dsimp [Lv]
    exact log_two_pi_mul_L3_le_ns t ht
  -- the digamma term
  have hbnd_dg : ‖Complex.digamma (1 - s)‖ ≤ 3 * Lv ^ 3 := by
    have h' := digamma_poly_bound_ns (σ := σ) (t := t) hσlo hσhi ht
    simpa [s, Lv] using h'
  -- the tangent term
  have hbnd_T : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤
      2 * Real.pi * Lv ^ 3 := by
    have hu : (1 : ℝ) ≤ |(↑Real.pi * (1 - s) / 2).im| := by
      simpa [s] using (tan_arg_abs_ns σ t ht)
    have h' := tan_term_poly_bound_ns (↑Real.pi * (1 - s) / 2) hu ht
    simpa [Lv] using h'
  -- the reflected ζ'/ζ term: constant bound, absorbed into Lv³
  have hbnd_R : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ M * Lv ^ 3 := by
    have hM := hMb (1 - s) hre_w
    have hML : M ≤ M * Lv ^ 3 := le_mul_of_one_le_right (le_of_lt hMpos) hL3
    linarith
  -- assemble ζ'/ζ
  have hnorm_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (M + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 := by
    have htri : ‖deriv riemannZeta s / riemannZeta s‖ ≤
        ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
        ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
          ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
      rw [hFE']
      have h1 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
              deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
              ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
        simpa [sub_eq_add_neg] using
          (norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
              ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2))
            (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))))
      have h2 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ :=
        norm_add_le _ _
      have h3 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ := by
        simpa [sub_eq_add_neg] using
          (norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ)) (-Complex.digamma (1 - s)))
      linarith
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
              ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := htri
      _ ≤ Real.log (2 * Real.pi) * Lv ^ 3 + 3 * Lv ^ 3 + 2 * Real.pi * Lv ^ 3 +
            M * Lv ^ 3 :=
          add_le_add (add_le_add (add_le_add hbnd_log hbnd_dg) hbnd_T) hbnd_R
      _ = (M + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 := by ring
  -- lift to ζ₁
  have hζ1main : ‖logDeriv riemannZeta₁ s‖ ≤ C * Lv ^ 3 := by
    have hle1 := norm_zeta1_logDeriv_le_ns s hs1 hζs
    have hinv : ‖(s - 1)⁻¹‖ ≤ 1 := by simpa [s] using (inv_sub_one_le_one_ns σ t ht)
    have hpre : ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ ≤
        (M + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 + 1 :=
      add_le_add hnorm_main hinv
    calc
      ‖logDeriv riemannZeta₁ s‖ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := hle1
      _ ≤ (M + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 + 1 := hpre
      _ ≤ C * Lv ^ 3 := by
        dsimp [C]
        nlinarith only [hL3]
  have hgoal : ‖logDeriv riemannZeta₁ (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
      C * (Real.log (|t| + 3) + 1) ^ 3 := by
    change ‖logDeriv riemannZeta₁ s‖ ≤ C * Lv ^ 3
    exact hζ1main
  exact hgoal

/-- `‖tan (π/4 + u·I)‖ = 1` for all real `u`. -/
private lemma norm_tan_pi_div_four_add_I (u : ℝ) :
    ‖Complex.tan ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ = 1 := by
  have hsin : Complex.sin ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
        (((Real.cosh u : ℝ) : ℂ) + ((Real.sinh u : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hcos : Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
        (((Real.cosh u : ℝ) : ℂ) - ((Real.sinh u : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    ring
  have hsqP : Complex.normSq (((Real.cosh u : ℝ) : ℂ) + ((Real.sinh u : ℝ) : ℂ) * Complex.I) =
      Real.cosh u ^ 2 + Real.sinh u ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.add_im, Complex.mul_im, Complex.I_im]
    ring
  have hsqM : Complex.normSq (((Real.cosh u : ℝ) : ℂ) - ((Real.sinh u : ℝ) : ℂ) * Complex.I) =
      Real.cosh u ^ 2 + Real.sinh u ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.sub_im, Complex.mul_im, Complex.I_im]
    ring
  have hsp : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2) = 1 / 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hnorm_sin : ‖Complex.sin ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ^ 2 =
      (1 / 2) * (Real.cosh u ^ 2 + Real.sinh u ^ 2) := by
    rw [hsin, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal, hsqP, hsp]
  have hnorm_cos : ‖Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ^ 2 =
      (1 / 2) * (Real.cosh u ^ 2 + Real.sinh u ^ 2) := by
    rw [hcos, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal, hsqM, hsp]
  have hcos_ne : Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have h1 : ‖Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ^ 2 = 0 := by
      rw [h0]; simp
    rw [hnorm_cos] at h1
    have hc : 0 < Real.cosh u := Real.cosh_pos u
    nlinarith [sq_nonneg (Real.sinh u), hc]
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  have heq : ‖Complex.sin ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ =
      ‖Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ := by
    have h1 : ‖Complex.sin ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ^ 2 =
        ‖Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
      rw [hnorm_sin, hnorm_cos]
    have h2 := norm_nonneg (Complex.sin ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I))
    have h3 := norm_nonneg (Complex.cos ((Real.pi / 4 : ℝ) + (u : ℂ) * Complex.I))
    nlinarith
  rw [heq]
  exact div_self (by
    intro h0
    exact hcos_ne (norm_eq_zero.mp h0))
/-- Reflection bound: if the reflected logarithmic derivative `ζ'/ζ(1-s)` is bounded by `B`
at `s = σ + I*τ` with `σ < 1/2`, `|τ| ≥ 5`, then `‖logDeriv ζ₁ s‖ ≤ B + 20·L³` where
`L = log(|τ|+3)+1`. -/
private lemma logDeriv_zeta1_reflect_le (h : RiemannHypothesis) {σ τ B : ℝ} (hτ : 5 ≤ |τ|)
    (hσlo : -(3 / 2 : ℝ) ≤ σ) (hσlt : σ < 1 / 2)
    (hB : ‖deriv riemannZeta (1 - ((σ : ℂ) + Complex.I * (τ : ℂ))) /
        riemannZeta (1 - ((σ : ℂ) + Complex.I * (τ : ℂ)))‖ ≤ B) :
    ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (τ : ℂ))‖ ≤
      B + 20 * (Real.log (|τ| + 3) + 1) ^ 3 := by
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs
  have hτpos : 0 < |τ| := by linarith
  have hτne : τ ≠ 0 := by
    intro h
    rw [h] at hτ
    norm_num at hτ
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = τ := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro hh
    have := congrArg Complex.re hh
    rw [hsre] at this
    norm_num at this
    linarith
  have hs0 : s ≠ 0 := by
    intro hh
    have := congrArg Complex.im hh
    rw [hsim] at this
    simp at this
    exact hτne this
  have hζs : riemannZeta s ≠ 0 := by
    intro hz
    by_cases hσ0 : 0 < σ
    · exact zeta_ne_zero_of_rh_lt_half h (by rw [hsre]; exact hσ0) (by rw [hsre]; exact hσlt) hz
    · have hσle : s.re ≤ 0 := by rw [hsre]; linarith
      have htr := (riemannZeta_eq_zero_iff_trivial_of_re_nonpos hσle).mp hz
      obtain ⟨n, hn⟩ := htr
      have him := congrArg Complex.im hn
      rw [hsim] at him
      simp at him
      exact hτne him
  have hζw : riemannZeta (1 - s) ≠ 0 := by
    apply zeta_ne_zero_of_rh_gt_half h
    rw [Complex.sub_re, hsre]
    norm_num
    linarith
  have hΓ : ∀ n : ℕ, 1 - s ≠ -↑n := by
    intro n hn
    have hr := congrArg Complex.re hn
    rw [Complex.sub_re, hsre] at hr
    have hr' : 1 - σ = -(n : ℝ) := by simpa using hr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have him := congrArg Complex.im hk
    have h1 : (↑Real.pi * (1 - s) / 2).im = -(Real.pi * τ / 2) := by
      simp [hs]; ring
    have h2 : (((2 * (k : ℂ) + 1) * (↑Real.pi) / 2 : ℂ)).im = 0 := by
      have hcast : ((2 * (k : ℂ) + 1) * (↑Real.pi) / 2 : ℂ) =
          (((2 * (k : ℝ) + 1) * Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast]; simp
    rw [h1, h2] at him
    have h3 : Real.pi * τ / 2 = 0 := by linarith
    have h4 : τ = 0 := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      have : Real.pi * τ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hπ
    exact hτne h4
  have hFE := zeta_logDeriv_fe_expanded hζs hζw hs0 hs1 hΓ hcos
  have hdig : ‖Complex.digamma (1 - s)‖ ≤ Real.log (2 + |τ|) + 2 := by
    have hd := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (1 - σ) (-τ)
      (by linarith) (by linarith)
    have heq : (((1 - σ : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) = 1 - s := by
      simp [hs]; ring
    rw [heq, abs_neg] at hd
    exact hd
  have htan : ‖Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ 4 := by
    refine Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge _ ?_
    have h1 : (↑Real.pi * (1 - s) / 2).im = -(Real.pi * τ / 2) := by simp [hs]; ring
    rw [h1, abs_neg]
    have h2 : |Real.pi * τ / 2| = Real.pi * |τ| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [h2]
    nlinarith [Real.pi_gt_three, abs_nonneg τ, hτ]
  have hlog2π : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ ≤ Real.log (2 * Real.pi) := by
    rw [show Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) by
      rw [Complex.ofReal_log (le_of_lt (by positivity : (0 : ℝ) < 2 * Real.pi))]]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
  have htan2 : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.pi / 2 * ‖Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤ Real.pi / 2 * 4 :=
      mul_le_mul_of_nonneg_left htan (by positivity)
    nlinarith [Real.pi_pos]
  have hmain : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      Real.log (2 * Real.pi) + (Real.log (2 + |τ|) + 2) + 2 * Real.pi + B := by
    rw [hFE]
    have h1 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
            deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
        ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
          ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
      have hA : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
              deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
        simpa [sub_eq_add_neg] using (norm_add_le
          (Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2))
          (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))))
      have hB' : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ :=
        norm_add_le _ _
      have hC : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ := by
        simpa [sub_eq_add_neg] using
          (norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ)) (-Complex.digamma (1 - s)))
      linarith
    have hBrew : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ B := by
      have heq : 1 - s = 1 - ((σ : ℂ) + Complex.I * (τ : ℂ)) := by rw [hs]
      rw [heq]; exact hB
    calc _ ≤ ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
          ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := h1
      _ ≤ Real.log (2 * Real.pi) + (Real.log (2 + |τ|) + 2) + 2 * Real.pi + B := by linarith
  have hld : ‖logDeriv riemannZeta₁ s‖ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + 2 := by
    rw [zeta1_logDeriv_eq_ns s hs1 hζs]
    refine le_trans (norm_add_le _ _) ?_
    have hge : (1 : ℝ) / 2 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      simp only [Complex.sub_re, hsre, Complex.one_re] at h
      have h2 : |σ - 1| = 1 - σ := by rw [abs_of_nonpos (by linarith)]; ring
      rw [h2] at h
      linarith
    have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      rw [inv_le_comm₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1)) (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log (|τ| + 3) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ |τ| + 3 by linarith)
    linarith
  calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (τ : ℂ))‖ = ‖logDeriv riemannZeta₁ s‖ := by
        rw [hs]
    _ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + 2 := hld
    _ ≤ Real.log (2 * Real.pi) + (Real.log (2 + |τ|) + 2) + 2 * Real.pi + B + 2 := by linarith
    _ ≤ B + 20 * (Real.log (|τ| + 3) + 1) ^ 3 := by
        have h1 : Real.log (2 * Real.pi) ≤ 7 := by
          have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
          have h2 := Real.pi_lt_four
          linarith
        have h2 : 2 * Real.pi ≤ 8 := by have := Real.pi_lt_four; linarith
        have h3 : Real.log (2 + |τ|) ≤ Real.log (|τ| + 3) :=
          Real.log_le_log (by positivity) (by linarith)
        have hLge : (3 : ℝ) ≤ Real.log (|τ| + 3) + 1 := by
          have hlog8ge : (2 : ℝ) ≤ Real.log 8 := by
            rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
            have := Real.log_two_gt_d9
            push_cast; nlinarith
          have hlogτ : Real.log (8 : ℝ) ≤ Real.log (|τ| + 3) :=
            Real.log_le_log (by norm_num) (by linarith)
          linarith
        have hsq : (9 : ℝ) ≤ (Real.log (|τ| + 3) + 1) ^ 2 := by nlinarith [hLge]
        have hcube : (27 : ℝ) ≤ (Real.log (|τ| + 3) + 1) ^ 3 := by nlinarith [hsq, hLge]
        nlinarith [h1, h2, h3, hcube]
theorem zeta1_logDeriv_uniform_b (h : RiemannHypothesis) :
    ∀ σ T δ : ℝ, -(3 / 2) ≤ σ → σ ≤ 2 → 5 ≤ T → 0 < δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
        (10 : ℝ) ^ 8 * ((Real.log (T + 3) + 1) ^ 3 + (Real.log (T + 3) + 1) ^ 2 / δ) := by
  intro σ T δ hσlo hσhi hT hδ0 hgap
  obtain ⟨C1, hC1pos, hC1le, hC1b⟩ := zeta_logDeriv_negStrip_bound_b h
  obtain ⟨C2, hC2pos, hC2le, hC2b⟩ := zeta_logDeriv_strip_bound_rh_b
  obtain ⟨C3, hC3pos, hC3le, hC3b⟩ := zeta1_logDeriv_goodHeight_delta_b h
  set L : ℝ := Real.log (T + 3) + 1 with hL
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hL]
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 3 by linarith)
    linarith
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hL3nn : 0 ≤ L ^ 3 := pow_nonneg hLnn 3
  have hL2dnn : 0 ≤ L ^ 2 / δ := div_nonneg (sq_nonneg L) hδ0.le
  have hsum0 : 0 ≤ L ^ 3 + L ^ 2 / δ := by linarith
  have hdist_base : (1 / 4 : ℝ) ≤ T := by linarith
  rcases lt_or_ge σ (-(1 / 2)) with hσ | hσ
  · -- σ < -1/2 : negative strip
    have hb := hC1b σ T hσlo hσ.le (by rw [hTabs]; linarith)
    have hLlog : Real.log (|T| + 3) + 1 = L := by rw [hL, hTabs]
    rw [hLlog] at hb
    calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ C1 * L ^ 3 := hb
      _ ≤ 100 * L ^ 3 := mul_le_mul_of_nonneg_right hC1le hL3nn
      _ ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) := by nlinarith [hL3nn, hL2dnn, hL1]
  · rcases lt_or_ge σ (1 / 8) with hσ8 | hσ8
    · -- -1/2 ≤ σ < 1/8 : reflect, gap parameter 3/8
      have hσlt : σ < 1 / 2 := by linarith
      have hss : ((1 - σ : ℝ) : ℂ) + Complex.I * ((-T : ℝ) : ℂ) =
          1 - ((σ : ℂ) + Complex.I * (T : ℂ)) := by push_cast; ring
      have hdist : (1 / 4 : ℝ) ≤ ‖(((1 - σ : ℝ) : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) - 1‖ := by
        rw [show (((1 - σ : ℝ) : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) - 1 =
          -(((σ : ℂ) + Complex.I * (T : ℂ))) by push_cast; ring, norm_neg]
        refine le_trans hdist_base ?_
        simpa [hTabs] using Complex.abs_im_le_norm ((σ : ℂ) + Complex.I * (T : ℂ))
      have hraw := hC2b h (3 / 8) (1 - σ) (-T) (by norm_num) (by norm_num) (by linarith)
        (by linarith) (by rw [abs_neg]; linarith) hdist
      have hB : ‖deriv riemannZeta (1 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
          riemannZeta (1 - ((σ : ℂ) + Complex.I * (T : ℂ)))‖ ≤ 5 * 10 ^ 6 * L ^ 3 := by
        rw [← hss]
        refine hraw.trans ?_
        rw [abs_neg, hTabs, ← hL]
        have hp : (1 + 1 / (3 / 8 : ℝ)) ^ 3 ≤ 50 := by norm_num
        nlinarith [hp, hL3nn, hC2pos, hC2le]
      have hfin := logDeriv_zeta1_reflect_le (σ := σ) (τ := T) h (by rw [hTabs]; exact hT) hσlo hσlt hB
      have hfin' : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          5 * 10 ^ 6 * L ^ 3 + 20 * L ^ 3 := by
        have heq : (Real.log (|T| + 3) + 1) = L := by rw [hL, hTabs]
        rw [heq] at hfin
        linarith
      calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖
          ≤ 5 * 10 ^ 6 * L ^ 3 + 20 * L ^ 3 := hfin'
        _ ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) := by nlinarith [hL3nn, hL2dnn, hL1]
    · rcases lt_or_ge σ (3 / 8) with hσ38 | hσ38
      · -- 1/8 ≤ σ < 3/8 : reflect, gap parameter 1/8
        have hσlt : σ < 1 / 2 := by linarith
        have hss : ((1 - σ : ℝ) : ℂ) + Complex.I * ((-T : ℝ) : ℂ) =
            1 - ((σ : ℂ) + Complex.I * (T : ℂ)) := by push_cast; ring
        have hdist : (1 / 4 : ℝ) ≤ ‖(((1 - σ : ℝ) : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) - 1‖ := by
          rw [show (((1 - σ : ℝ) : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) - 1 =
            -(((σ : ℂ) + Complex.I * (T : ℂ))) by push_cast; ring, norm_neg]
          refine le_trans hdist_base ?_
          simpa [hTabs] using Complex.abs_im_le_norm ((σ : ℂ) + Complex.I * (T : ℂ))
        have hraw := hC2b h (1 / 8) (1 - σ) (-T) (by norm_num) (by norm_num) (by linarith)
          (by linarith) (by rw [abs_neg]; linarith) hdist
        have hB : ‖deriv riemannZeta (1 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
            riemannZeta (1 - ((σ : ℂ) + Complex.I * (T : ℂ)))‖ ≤ 10 ^ 5 * 729 * L ^ 3 := by
          rw [← hss]
          refine hraw.trans ?_
          rw [abs_neg, hTabs, ← hL]
          have hp : (1 + 1 / (1 / 8 : ℝ)) ^ 3 ≤ 729 := by norm_num
          nlinarith [hp, hL3nn, hC2pos, hC2le]
        have hfin := logDeriv_zeta1_reflect_le (σ := σ) (τ := T) h (by rw [hTabs]; exact hT) hσlo hσlt hB
        have hfin' : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
            10 ^ 5 * 729 * L ^ 3 + 20 * L ^ 3 := by
          have heq : (Real.log (|T| + 3) + 1) = L := by rw [hL, hTabs]
          rw [heq] at hfin
          linarith
        calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖
            ≤ 10 ^ 5 * 729 * L ^ 3 + 20 * L ^ 3 := hfin'
          _ ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) := by nlinarith [hL3nn, hL2dnn, hL1]
      · rcases lt_or_ge σ (1 / 2) with hσ12 | hσ12
        · -- 3/8 ≤ σ < 1/2 : reflect, using the good-height bound at height +T
          have hσlt : σ < 1 / 2 := hσ12
          set w : ℂ := ((1 - σ : ℝ) : ℂ) + Complex.I * ((T : ℝ) : ℂ) with hw
          have hwre : w.re = 1 - σ := by simp [hw]
          have hwim : w.im = T := by simp [hw]
          have hwgt : (1 / 2 : ℝ) < w.re := by rw [hwre]; linarith
          have hζw : riemannZeta w ≠ 0 := zeta_ne_zero_of_rh_gt_half h hwgt
          have hwne1 : w ≠ 1 := by
            intro hh
            have := congrArg Complex.re hh
            rw [hwre] at this
            norm_num at this
            linarith
          have hgh := hC3b T δ hT hδ0 hgap (1 - σ) (by linarith) (by linarith)
          have hgh' : ‖logDeriv riemannZeta₁ w‖ ≤ C3 * (L ^ 3 + L ^ 2 / δ) := by
            have heq : (Real.log (T + 3) + 1) = L := hL.symm
            rw [heq] at hgh
            rw [hw]
            exact hgh
          have hrel : deriv riemannZeta w / riemannZeta w = logDeriv riemannZeta₁ w - (w - 1)⁻¹ := by
            rw [← logDeriv_apply, zeta1_logDeriv_eq_ns w hwne1 hζw, logDeriv_apply, div_eq_mul_inv]
            ring
          have hinv : ‖(w - 1)⁻¹‖ ≤ 1 / 5 := by
            rw [norm_inv]
            rw [inv_le_comm₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hwne1)) (by norm_num : (0:ℝ) < 1/5)]
            have him : (w - 1).im = T := by simp [hw]
            have h := Complex.abs_im_le_norm (w - 1)
            rw [him, hTabs] at h
            linarith
          have hss : 1 - ((σ : ℂ) + Complex.I * (T : ℂ)) = starRingEnd ℂ w := by
            rw [hw]; apply Complex.ext <;> simp
          have hB : ‖deriv riemannZeta (1 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
              riemannZeta (1 - ((σ : ℂ) + Complex.I * (T : ℂ)))‖ ≤
              10 ^ 7 * (L ^ 3 + L ^ 2 / δ) + 1 / 5 := by
            rw [hss, logDeriv_conj_zeta, norm_conj, hrel]
            refine le_trans (norm_sub_le _ _) ?_
            have h3 : ‖logDeriv riemannZeta₁ w‖ ≤ 10 ^ 7 * (L ^ 3 + L ^ 2 / δ) := by
              refine hgh'.trans ?_
              nlinarith [hC3le, hL3nn, hL2dnn, hC3pos]
            linarith
          have hfin := logDeriv_zeta1_reflect_le (σ := σ) (τ := T) h (by rw [hTabs]; exact hT) hσlo hσlt hB
          have hfin' : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
              10 ^ 7 * (L ^ 3 + L ^ 2 / δ) + 1 / 5 + 20 * L ^ 3 := by
            have heq : (Real.log (|T| + 3) + 1) = L := by rw [hL, hTabs]
            rw [heq] at hfin
            linarith
          calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖
              ≤ 10 ^ 7 * (L ^ 3 + L ^ 2 / δ) + 1 / 5 + 20 * L ^ 3 := hfin'
            _ ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) := by nlinarith [hL3nn, hL2dnn, hL1, hsum0]
        · rcases lt_or_ge σ (5 / 8) with hσ58 | hσ58
          · -- 1/2 ≤ σ < 5/8 : good-height bound directly
            have hb := hC3b T δ hT hδ0 hgap σ hσ12 hσ58.le
            have hb' : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
                10 ^ 7 * (L ^ 3 + L ^ 2 / δ) := by
              have heq : (Real.log (T + 3) + 1) = L := hL.symm
              rw [heq] at hb
              exact hb.trans (by nlinarith [hC3le, hL3nn, hL2dnn, hC3pos])
            calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
                  10 ^ 7 * (L ^ 3 + L ^ 2 / δ) := hb'
              _ ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) := by nlinarith [hsum0, hL1]
          · -- 5/8 ≤ σ ≤ 2 : strip bound directly
            have hs1 : (1 / 4 : ℝ) ≤ ‖(((σ : ℂ) + Complex.I * (T : ℂ)) - 1)‖ := by
              refine le_trans hdist_base ?_
              have him : (((σ : ℂ) + Complex.I * (T : ℂ)) - 1).im = T := by simp
              have h := Complex.abs_im_le_norm (((σ : ℂ) + Complex.I * (T : ℂ)) - 1)
              rw [him, hTabs] at h
              exact h
            have hb := hC2b h (1 / 8) σ T (by norm_num) (by norm_num) (by linarith) hσhi
              (by rw [hTabs]; linarith) hs1
            have hb' : ‖deriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) /
                riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ 10 ^ 5 * 729 * L ^ 3 := by
              refine hb.trans ?_
              rw [hTabs, ← hL]
              have hp : (1 + 1 / (1 / 8 : ℝ)) ^ 3 ≤ 729 := by norm_num
              nlinarith [hp, hL3nn, hC2pos, hC2le]
            have hsne : ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 1 := by
              intro hh
              have := congrArg Complex.im hh
              simp at this
              linarith
            have hz1 : riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
              apply zeta_ne_zero_of_rh_gt_half h
              have hre : ((σ : ℂ) + Complex.I * (T : ℂ)).re = σ := by simp
              rw [hre]; linarith
            have hcorr : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
                10 ^ 5 * 729 * L ^ 3 + 1 := by
              rw [zeta1_logDeriv_eq_ns _ hsne hz1]
              refine le_trans (norm_add_le _ _) ?_
              have hinv : ‖(((σ : ℂ) + Complex.I * (T : ℂ)) - 1)⁻¹‖ ≤ 1 := by
                rw [norm_inv]
                rw [inv_le_comm₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hsne)) (by norm_num : (0:ℝ) < 1)]
                have him : (((σ : ℂ) + Complex.I * (T : ℂ)) - 1).im = T := by simp
                have h := Complex.abs_im_le_norm (((σ : ℂ) + Complex.I * (T : ℂ)) - 1)
                rw [him, hTabs] at h
                linarith
              linarith
            calc ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖
                ≤ 10 ^ 5 * 729 * L ^ 3 + 1 := hcorr
              _ ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) := by nlinarith [hL3nn, hL2dnn, hL1]
theorem edgeT_bound_neg_b (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 750000000 ∧ ∀ (x a b T δ K : ℝ), 1 ≤ x → -(3 / 2 : ℝ) ≤ a →
      a ≤ (1 / 8 : ℝ) → (5 / 8 : ℝ) ≤ b → b ≤ 2 → 5 ≤ T → 0 < δ → 1 ≤ K →
      1 ≤ K * (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ‖edgeT a b T (psiIntF1 x)‖ ≤
        C * K * ((Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ b / T)) := by
  refine ⟨(750000000 : ℝ), by norm_num, by norm_num, ?_⟩
  intro x a b T δ K hx ha ha8 hb1 hb2 hT hδ0 hK1 hKδ hgap
  have hx1 : (1 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set L : ℝ := Real.log (T + 3) + 1 with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 3 by linarith)
    linarith
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hL3nn : 0 ≤ L ^ 3 := pow_nonneg hLnn 3
  have hL3ge : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hxpow0 : (0 : ℝ) ≤ (x : ℝ) ^ b := Real.rpow_nonneg hx0.le b
  -- the pointwise bound
  have hpt : ∀ σ ∈ Set.uIoc a b,
      ‖psiIntF1 x ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        ((10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ b / T) := by
    intro σ hσ
    rw [Set.uIoc_of_le (by linarith : a ≤ b)] at hσ
    have hσlo : -(3 / 2 : ℝ) ≤ σ := le_trans ha (le_of_lt hσ.1)
    have hσhi : σ ≤ 2 := le_trans hσ.2 hb2
    have hs_eq : (σ : ℂ) + (T : ℂ) * Complex.I = (σ : ℂ) + Complex.I * (T : ℂ) := by
      rw [mul_comm]
    rw [hs_eq]
    have hU := zeta1_logDeriv_uniform_b h σ T δ hσlo hσhi hT hδ0 hgap
    rw [← hL] at hU
    have hb0 := psiIntF1_norm_le_logDeriv hx0 ((σ : ℂ) + Complex.I * (T : ℂ))
    have hre : ((σ : ℂ) + Complex.I * (T : ℂ)).re = σ := by simp
    rw [hre] at hb0
    have hnorm1 : T ≤ ‖(σ : ℂ) + Complex.I * (T : ℂ)‖ := by
      have hh := Complex.abs_im_le_norm ((σ : ℂ) + Complex.I * (T : ℂ))
      have him : ((σ : ℂ) + Complex.I * (T : ℂ)).im = T := by simp
      rw [him, abs_of_nonneg hT0.le] at hh
      exact hh
    have hinv : 1 / ‖((σ : ℂ) + Complex.I * (T : ℂ)) - 1‖ ≤ 1 := by
      have hh := Complex.abs_im_le_norm (((σ : ℂ) + Complex.I * (T : ℂ)) - 1)
      have him : (((σ : ℂ) + Complex.I * (T : ℂ)) - 1).im = T := by simp
      rw [him, abs_of_nonneg hT0.le] at hh
      rw [div_le_one (by linarith : (0 : ℝ) < ‖((σ : ℂ) + Complex.I * (T : ℂ)) - 1‖)]
      linarith
    have hpow : (x : ℝ) ^ σ ≤ (x : ℝ) ^ b :=
      Real.rpow_le_rpow_of_exponent_le hx1 hσ.2
    calc ‖psiIntF1 x ((σ : ℂ) + Complex.I * (T : ℂ))‖
        ≤ (‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ +
            1 / ‖((σ : ℂ) + Complex.I * (T : ℂ)) - 1‖) *
              ((x : ℝ) ^ σ / ‖(σ : ℂ) + Complex.I * (T : ℂ)‖) := hb0
      _ ≤ ((10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ σ / T) := by
          have h1 : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ +
              1 / ‖((σ : ℂ) + Complex.I * (T : ℂ)) - 1‖ ≤
              (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1 := by linarith
          have h2 : (x : ℝ) ^ σ / ‖(σ : ℂ) + Complex.I * (T : ℂ)‖ ≤ (x : ℝ) ^ σ / T :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le σ) hT0 hnorm1
          have h3 : (0 : ℝ) ≤ (x : ℝ) ^ σ / ‖(σ : ℂ) + Complex.I * (T : ℂ)‖ :=
            div_nonneg (Real.rpow_nonneg hx0.le σ) (norm_nonneg _)
          have h4 : (0 : ℝ) ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1 := by
            have := div_nonneg (sq_nonneg L) hδ0.le
            nlinarith [hL3nn]
          exact mul_le_mul h1 h2 h3 h4
      _ ≤ ((10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ b / T) := by
          have h4 : (0 : ℝ) ≤ (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1 := by
            have := div_nonneg (sq_nonneg L) hδ0.le
            nlinarith [hL3nn]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hT0.le) h4
  have hedge : edgeT a b T (psiIntF1 x) = ∫ (σ : ℝ) in a..b, psiIntF1 x ((σ : ℂ) + (T : ℂ) * Complex.I) := by
    rw [edgeT, wRect_im]
  rw [hedge]
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => psiIntF1 x ((σ : ℂ) + (T : ℂ) * Complex.I)) hpt
  -- 1/δ ≤ K L
  have hinvδ : 1 / δ ≤ K * L := by
    rw [div_le_iff₀ hδ0]
    have := hKδ
    nlinarith [hK1, hLnn, hδ0]
  have hL2δ : L ^ 2 / δ ≤ K * L ^ 3 := by
    rw [div_le_iff₀ hδ0]
    nlinarith [hinvδ, hδ0, hLnn, sq_nonneg L]
  have hceil : (10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1 ≤ 2 * 10 ^ 8 * K * L ^ 3 + 1 := by
    have h1 : L ^ 3 + L ^ 2 / δ ≤ 2 * K * L ^ 3 := by
      have := mul_le_mul_of_nonneg_right hK1 hL3nn
      linarith [hL2δ]
    nlinarith [h1]
  have hfin : (((10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ b / T)) * |b - a| ≤
      ((750000000 : ℝ)) * K * ((Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ b / T)) := by
    have hab3 : |b - a| ≤ 3.5 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hxbT : 0 ≤ (x : ℝ) ^ b / T := div_nonneg hxpow0 hT0.le
    have hKL3 : 1 ≤ K * L ^ 3 := by nlinarith [hK1, hL3ge]
    have hstep1 : (((10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ b / T)) * |b - a| ≤
        ((2 * 10 ^ 8 * K * L ^ 3 + 1) * ((x : ℝ) ^ b / T)) * 3.5 := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hceil hxbT) hab3 (abs_nonneg _)
        (by positivity)
    refine le_trans hstep1 ?_
    have hKL3nn : 0 ≤ K * L ^ 3 := by linarith
    have hfinal : ((2 * 10 ^ 8 * K * L ^ 3 + 1) * ((x : ℝ) ^ b / T)) * 3.5 ≤
        ((750000000 : ℝ)) * K * (L ^ 3 * ((x : ℝ) ^ b / T)) := by
      have h1 : 1 ≤ K * L ^ 3 := hKL3
      nlinarith [hxbT, hKL3nn, h1, hK1, hL3ge]
    exact le_trans hfinal (le_of_eq (by rw [hL]))
  calc ‖∫ (σ : ℝ) in a..b, psiIntF1 x ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ ((10 : ℝ) ^ 8 * (L ^ 3 + L ^ 2 / δ) + 1) * ((x : ℝ) ^ b / T) * |b - a| := hmain
    _ ≤ ((750000000 : ℝ)) * K * ((Real.log (T + 3) + 1) ^ 3 * ((x : ℝ) ^ b / T)) := hfin
/-- Bound for `ζ'/ζ` on the vertical line `Re s = -3/2`, valid for all imaginary parts. -/
private lemma zeta_logDeriv_neg_three_halves_line (h : RiemannHypothesis) (y : ℝ) :
    ‖deriv riemannZeta (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)) /
        riemannZeta (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ ≤
      50 * (Real.log (|y| + 3) + 1) := by
  set s : ℂ := ((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ) with hs
  set w : ℂ := 1 - s with hw
  have hsre : s.re = -(3 / 2) := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hwre : w.re = 5 / 2 := by rw [hw, hs]; simp; norm_num
  have hwim : w.im = -y := by rw [hw, hs]; simp
  have hs1 : s ≠ 1 := by
    intro hh
    have := congrArg Complex.re hh
    rw [hsre] at this
    norm_num at this
  have hs0 : s ≠ 0 := by
    intro hh
    have := congrArg Complex.re hh
    rw [hsre] at this
    norm_num at this
  have hζs : riemannZeta s ≠ 0 := by
    intro hz
    have hle : s.re ≤ 0 := by rw [hsre]; norm_num
    obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_trivial_of_re_nonpos hle).mp hz
    have := congrArg Complex.re hn
    rw [hsre] at this
    have h2 : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [h2] at this
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    norm_num at this
    linarith
  have hζw : riemannZeta w ≠ 0 := by
    apply zeta_ne_zero_of_rh_gt_half h
    rw [hwre]; norm_num
  have hΓ : ∀ n : ℕ, 1 - s ≠ -↑n := by
    intro n hn
    have := congrArg Complex.re hn
    rw [Complex.sub_re, hsre, Complex.one_re] at this
    have h2 : ((-(n : ℂ))).re = -(n : ℝ) := by simp
    rw [h2] at this
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hre := congrArg Complex.re hk
    have h3 : (↑Real.pi * (1 - s) / 2).re = 5 * Real.pi / 4 := by
      have hval : ↑Real.pi * (1 - s) / 2 =
          ((5 * Real.pi / 4 : ℝ) : ℂ) + ((-(Real.pi * y / 2) : ℝ) : ℂ) * Complex.I := by
        rw [hs]; push_cast; ring
      rw [hval, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re]
      norm_num
    have h4 : (((2 * (k : ℂ) + 1) * (↑Real.pi) / 2 : ℂ)).re =
        ((2 * (k : ℝ) + 1) * Real.pi / 2) := by
      have hcast : ((2 * (k : ℂ) + 1) * (↑Real.pi) / 2 : ℂ) =
          (((2 * (k : ℝ) + 1) * Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast]; simp
    rw [h3, h4] at hre
    have hprod : Real.pi * (5 / 4 - (2 * (k : ℝ) + 1) / 2) = 0 := by nlinarith [hre]
    have h5 : 5 / 4 - (2 * (k : ℝ) + 1) / 2 = 0 := (mul_eq_zero.mp hprod).resolve_left Real.pi_ne_zero
    have h6 : (2 * (k : ℝ) + 1) = 5 / 2 := by linarith
    have h7 : (4 : ℝ) * (k : ℝ) = 3 := by linarith
    have h4k : (4 : ℤ) * k = 3 := by exact_mod_cast h7
    omega
  have hFE := zeta_logDeriv_fe_expanded hζs hζw hs0 hs1 hΓ hcos
  have hdig : ‖Complex.digamma w‖ ≤ Real.log (2 + |y|) + 2 := by
    have hd := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (5 / 2) (-y)
      (by norm_num) (by norm_num)
    have heq : (((5 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) = w := by
      rw [hw, hs]; push_cast; ring
    rw [heq, abs_neg] at hd
    exact hd
  have htan : ‖Complex.tan (↑Real.pi * w / 2)‖ ≤ 1 := by
    have h1 : ↑Real.pi * w / 2 =
        ((Real.pi / 4 : ℝ) + ((-(Real.pi * y / 2) : ℝ) : ℂ) * Complex.I) + (Real.pi : ℂ) := by
      rw [hw, hs]; push_cast; ring
    rw [h1, Complex.tan_add_pi]
    exact le_of_eq (norm_tan_pi_div_four_add_I (-(Real.pi * y / 2)))
  have h28 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ 28 := by
    obtain ⟨M, hMpos, hMle, hMb⟩ := logDeriv_zeta_const_bound_b
    refine le_trans (hMb w ?_) hMle
    rw [hwre]; norm_num
  have hlog2pi : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ ≤ 7 := by
    rw [show Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) by
      rw [Complex.ofReal_log (le_of_lt (by positivity : (0 : ℝ) < 2 * Real.pi))]]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have h1 : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.pi < 4 := Real.pi_lt_four
    linarith
  have htan2 : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2)‖ ≤ 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.pi / 2 * ‖Complex.tan (↑Real.pi * w / 2)‖ ≤ Real.pi / 2 * 1 :=
      mul_le_mul_of_nonneg_left htan (by positivity)
    have h2 : Real.pi / 2 ≤ 4 := by have := Real.pi_lt_four; linarith
    linarith
  have hmain : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      7 + (Real.log (2 + |y|) + 2) + 4 + 28 := by
    rw [hFE]
    have h1 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w +
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2) -
            deriv riemannZeta w / riemannZeta w‖ ≤
        ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma w‖ +
          ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2)‖ +
            ‖deriv riemannZeta w / riemannZeta w‖ := by
      have hA : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2) -
              deriv riemannZeta w / riemannZeta w‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2)‖ +
            ‖deriv riemannZeta w / riemannZeta w‖ := by
        simpa [sub_eq_add_neg] using (norm_add_le
          (Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2))
          (-(deriv riemannZeta w / riemannZeta w)))
      have hB : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w +
            ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2)‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w‖ +
            ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2)‖ :=
        norm_add_le _ _
      have hC : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma w‖ ≤
          ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma w‖ := by
        simpa [sub_eq_add_neg] using
          (norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ)) (-Complex.digamma w))
      linarith
    calc _ ≤ ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma w‖ +
          ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * w / 2)‖ +
            ‖deriv riemannZeta w / riemannZeta w‖ := h1
      _ ≤ 7 + (Real.log (2 + |y|) + 2) + 4 + 28 := by linarith
  have hlogy : Real.log (2 + |y|) ≤ Real.log (|y| + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have hLy : (1 : ℝ) ≤ Real.log (|y| + 3) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ |y| + 3 by linarith [abs_nonneg y])
    linarith
  calc ‖deriv riemannZeta (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)) /
        riemannZeta (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖
      = ‖deriv riemannZeta s / riemannZeta s‖ := by rw [hs]
    _ ≤ 7 + (Real.log (2 + |y|) + 2) + 4 + 28 := hmain
    _ ≤ 50 * (Real.log (|y| + 3) + 1) := by nlinarith [hLy, hlogy]

/-- The logarithmic derivative of `ζ₁` on the vertical line `Re s = -3/2`. -/
private lemma logDeriv_zeta1_neg_three_halves_line (h : RiemannHypothesis) (y : ℝ) :
    ‖logDeriv riemannZeta₁ (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ ≤
      55 * (Real.log (|y| + 3) + 1) := by
  set s : ℂ := ((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ) with hs
  have hsre : s.re = -(3 / 2) := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro hh
    have := congrArg Complex.re hh
    rw [hsre] at this
    norm_num at this
  have hζs : riemannZeta s ≠ 0 := by
    intro hz
    have hle : s.re ≤ 0 := by rw [hsre]; norm_num
    obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_trivial_of_re_nonpos hle).mp hz
    have := congrArg Complex.re hn
    rw [hsre] at this
    have h2 : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [h2] at this
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    norm_num at this
    linarith
  have hb : ‖deriv riemannZeta s / riemannZeta s‖ ≤ 50 * (Real.log (|y| + 3) + 1) := by
    simpa [hs] using zeta_logDeriv_neg_three_halves_line h y
  rw [zeta1_logDeriv_eq_ns s hs1 hζs]
  refine le_trans (norm_add_le _ _) ?_
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    rw [inv_le_comm₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1)) (by norm_num : (0 : ℝ) < 2)]
    have hh := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre, Complex.one_re] at hh
    have h2 : |(-(3 / 2) - 1 : ℝ)| = 5 / 2 := by norm_num
    rw [h2] at hh
    linarith
  have hLy : (1 : ℝ) ≤ Real.log (|y| + 3) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ |y| + 3 by linarith [abs_nonneg y])
    linarith
  linarith

/-- `∫_{-Tp}^{Tp} dy / ‖-3/2 + iy‖ ≤ 4·(log (Tp+3) + 1)`. -/
private lemma integral_inv_norm_le (Tp : ℝ) (hT : 5 ≤ Tp) :
    (∫ (y : ℝ) in -Tp..Tp, 1 / ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) ≤
      4 * (Real.log (Tp + 3) + 1) := by
  set g : ℝ → ℝ := fun y => 1 / ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖ with hg
  have hnorm_ge : ∀ y : ℝ, (3 / 2 : ℝ) ≤ ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖ := by
    intro y
    have hh := Complex.abs_re_le_norm (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))
    have hre : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = -(3 / 2) := by simp
    rw [hre] at hh
    have h2 : |(-(3 / 2) : ℝ)| = 3 / 2 := by norm_num
    rwa [h2] at hh
  have hcont : Continuous g := by
    simp only [hg]
    exact Continuous.div continuous_const
      (continuous_const.add (continuous_const.mul continuous_ofReal)).norm
      (fun y => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (hnorm_ge y)))
  have heven : ∀ y : ℝ, g (-y) = g y := by
    intro y
    simp only [hg]
    have h : ((-(3 / 2) : ℝ) : ℂ) + Complex.I * ((-y : ℝ) : ℂ) =
        starRingEnd ℂ (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [h, norm_conj]
  have hsym : (∫ (y : ℝ) in -Tp..0, g y) = ∫ (y : ℝ) in 0..Tp, g y := by
    have h1 : (∫ (y : ℝ) in (0 : ℝ)..Tp, g (-y)) = ∫ (y : ℝ) in -Tp..0, g y := by
      have h2 := intervalIntegral.integral_comp_neg (f := g) (a := (0 : ℝ)) (b := Tp)
      simpa using h2
    rw [← h1]
    apply intervalIntegral.integral_congr
    intro y _
    exact heven y
  have hsplit : (∫ (y : ℝ) in -Tp..Tp, g y) =
      (∫ (y : ℝ) in -Tp..0, g y) + ∫ (y : ℝ) in 0..Tp, g y :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hhalf : (∫ (y : ℝ) in (0 : ℝ)..Tp, g y) ≤ 2 * Real.log (Tp + 3 / 2) := by
    have hpoint : ∀ y ∈ Set.Icc (0 : ℝ) Tp, g y ≤ 2 / (y + 3 / 2) := by
      intro y hy
      rw [Set.mem_Icc] at hy
      simp only [hg]
      have him : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)).im = y := by simp
      have hB : y ≤ ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖ := by
        have hh := Complex.abs_im_le_norm (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))
        rw [him] at hh
        rwa [abs_of_nonneg hy.1] at hh
      have hsum : (y + 3 / 2) / 2 ≤ ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖ := by
        linarith [hnorm_ge y, hB]
      refine le_trans (one_div_le_one_div_of_le (by linarith : (0 : ℝ) < (y + 3 / 2) / 2) hsum) ?_
      rw [one_div, inv_div]
    have hcont2 : ContinuousOn (fun y : ℝ => 2 / (y + 3 / 2)) (Set.uIcc (0 : ℝ) Tp) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_id.add continuousOn_const) ?_
      intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact ne_of_gt (by linarith [hy.1])
    have hkey := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (0 : ℝ) ≤ Tp)
      (hcont.intervalIntegrable _ _) (hcont2.intervalIntegrable) hpoint
    have hval : (∫ (y : ℝ) in (0 : ℝ)..Tp, 2 / (y + 3 / 2)) =
        2 * (Real.log (Tp + 3 / 2) - Real.log (3 / 2)) := by
      have h1 : (∫ (y : ℝ) in (0 : ℝ)..Tp, 2 / (y + 3 / 2)) =
          2 * (∫ (y : ℝ) in (0 : ℝ)..Tp, 1 / (y + 3 / 2)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro y _
        ring
      rw [h1]
      have h2 : (∫ (y : ℝ) in (0 : ℝ)..Tp, 1 / (y + 3 / 2)) =
          ∫ (z : ℝ) in (3 / 2)..(Tp + 3 / 2), 1 / z := by
        have h3 := intervalIntegral.integral_comp_add_right (f := fun z : ℝ => 1 / z)
          (a := (0 : ℝ)) (b := Tp) (d := 3 / 2)
        simpa [show (0 : ℝ) + 3 / 2 = 3 / 2 by ring] using h3
      rw [h2, integral_one_div_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
        (by linarith : (0 : ℝ) < Tp + 3 / 2)]
      rw [Real.log_div (by linarith : (Tp + 3 / 2 : ℝ) ≠ 0) (by norm_num : ((3 : ℝ) / 2) ≠ 0)]
    rw [hval] at hkey
    refine le_trans hkey ?_
    have hlog3 : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlogle : Real.log (Tp + 3 / 2) ≤ Real.log (Tp + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log (Tp + 3) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Tp + 3 by linarith)
    linarith
  have hlogle : Real.log (Tp + 3 / 2) ≤ Real.log (Tp + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith [hsplit, hsym, hhalf, hL1, hlogle]

theorem edgeL_neg_three_halves_bound_b (h : RiemannHypothesis) :
    ∀ x Tp : ℝ, 1 ≤ x → 5 ≤ Tp →
      ‖(∫ (y : ℝ) in -Tp..Tp, psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)))‖ ≤
        (400 : ℝ) * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (Tp + 3) + 1) ^ 4 := by
  intro x Tp hx hT
  have hx0 : 0 < x := by linarith
  set L : ℝ := Real.log (Tp + 3) + 1 with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have := Real.log_nonneg (show (1 : ℝ) ≤ Tp + 3 by linarith)
    linarith
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hxpow0 : (0 : ℝ) ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hx0.le _
  set G : ℝ → ℝ := fun y => 56 * L * ((x : ℝ) ^ (-(3 / 2) : ℝ) /
    ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) with hG
  have hnorm_ge : ∀ y : ℝ, (3 / 2 : ℝ) ≤ ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖ := by
    intro y
    have hh := Complex.abs_re_le_norm (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))
    have hre : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = -(3 / 2) := by simp
    rw [hre] at hh
    have h2 : |(-(3 / 2) : ℝ)| = 3 / 2 := by norm_num
    rwa [h2] at hh
  have hpt : ∀ y ∈ Set.Icc (-Tp) Tp,
      ‖psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ ≤ G y := by
    intro y hy
    rw [Set.mem_Icc] at hy
    have hb := psiIntF1_norm_le_logDeriv hx0 (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))
    have hre : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = -(3 / 2) := by simp
    rw [hre] at hb
    have hLy : Real.log (|y| + 3) + 1 ≤ L := by
      rw [hL]
      have h1 : |y| ≤ Tp := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have h2 : Real.log (|y| + 3) ≤ Real.log (Tp + 3) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hld := logDeriv_zeta1_neg_three_halves_line h y
    have h1 : ‖logDeriv riemannZeta₁ (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ ≤ 55 * L :=
      le_trans hld (by nlinarith [hLy])
    have h2 : 1 / ‖((((-(3 / 2) : ℝ)) : ℂ) + Complex.I * (y : ℂ)) - 1‖ ≤ 1 := by
      have hh := Complex.abs_re_le_norm (((((-(3 / 2) : ℝ)) : ℂ) + Complex.I * (y : ℂ)) - 1)
      have h3 : (((((-(3 / 2) : ℝ)) : ℂ) + Complex.I * (y : ℂ)) - 1).re = -(5 / 2) := by
        simp
        norm_num
      rw [h3] at hh
      have h4 : |(-(5 / 2) : ℝ)| = 5 / 2 := by norm_num
      rw [h4] at hh
      rw [div_le_one (by linarith : (0 : ℝ) < ‖((((-(3 / 2) : ℝ)) : ℂ) + Complex.I * (y : ℂ)) - 1‖)]
      linarith
    rw [hG]
    calc ‖psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖
        ≤ (‖logDeriv riemannZeta₁ (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ +
            1 / ‖((((-(3 / 2) : ℝ)) : ℂ) + Complex.I * (y : ℂ)) - 1‖) *
              ((x : ℝ) ^ (-(3 / 2) : ℝ) /
                ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) := hb
      _ ≤ (55 * L + 1) * ((x : ℝ) ^ (-(3 / 2) : ℝ) /
            ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hxpow0 (norm_nonneg _))
          linarith
      _ ≤ 56 * L * ((x : ℝ) ^ (-(3 / 2) : ℝ) /
            ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) := by
          have h3 : (55 * L + 1) ≤ 56 * L := by linarith
          exact mul_le_mul_of_nonneg_right h3 (div_nonneg hxpow0 (norm_nonneg _))
  have hcontf : Continuous (fun y : ℝ => psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = -(3 / 2) := by simp
    have hs0 : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
      intro hh
      have h2 := congrArg Complex.re hh
      rw [hre] at h2
      simp at h2
    have hs1 : (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)) ≠ 1 := by
      intro hh
      have h2 := congrArg Complex.re hh
      rw [hre] at h2
      simp at h2
      linarith
    have hζ1 : riemannZeta₁ (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)) ≠ 0 := by
      refine zeta1_ne_zero_of_re_le_zero ?_ ?_
      · rw [hre]
      · rw [hre]; norm_num
    have hinner : Continuous (fun y : ℝ => (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))) :=
      continuous_const.add (continuous_ofReal.const_mul Complex.I)
    exact (psiIntF1_analyticAt hx0 hs0 hs1 hζ1).continuousAt.comp
      (f := fun y : ℝ => (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))) hinner.continuousAt
  have hcontG : Continuous G := by
    rw [hG]
    refine Continuous.mul continuous_const (Continuous.div continuous_const ?_ ?_)
    · exact (continuous_const.add (continuous_ofReal.const_mul Complex.I)).norm
    · intro y
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (hnorm_ge y))
  have hone : ‖(∫ (y : ℝ) in -Tp..Tp, psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)))‖ ≤
      ∫ (y : ℝ) in -Tp..Tp, ‖psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith : -Tp ≤ Tp)
  have htwo : (∫ (y : ℝ) in -Tp..Tp,
        ‖psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖) ≤
      ∫ (y : ℝ) in -Tp..Tp, G y := by
    refine intervalIntegral.integral_mono_on (μ := volume) (by linarith)
      (hcontf.norm.intervalIntegrable _ _) (hcontG.intervalIntegrable _ _) hpt
  have hthree : (∫ (y : ℝ) in -Tp..Tp, G y) =
      56 * L * (x : ℝ) ^ (-(3 / 2) : ℝ) *
        (∫ (y : ℝ) in -Tp..Tp, 1 / ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) := by
    rw [hG]
    rw [show (fun y : ℝ => 56 * L * ((x : ℝ) ^ (-(3 / 2) : ℝ) /
        ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖)) =
        (fun y : ℝ => (56 * L * (x : ℝ) ^ (-(3 / 2) : ℝ)) *
          (1 / ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖)) by
      funext y
      rw [div_eq_mul_inv, one_div]
      try ring]
    rw [intervalIntegral.integral_const_mul]
  have hfour : (∫ (y : ℝ) in -Tp..Tp, 1 / ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) ≤
      4 * L := by
    have hh := integral_inv_norm_le Tp hT
    rw [hL]
    exact hh
  have hfive : 56 * L * (x : ℝ) ^ (-(3 / 2) : ℝ) * (4 * L) ≤
      400 * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := by
    have hL4 : L ^ 2 ≤ L ^ 4 := by nlinarith [hL1, sq_nonneg (L ^ 2 - 1), sq_nonneg L]
    nlinarith [hxpow0, hLnn, hL4, hL1]
  calc ‖(∫ (y : ℝ) in -Tp..Tp, psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)))‖
      ≤ ∫ (y : ℝ) in -Tp..Tp, ‖psiIntF1 x (((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ))‖ := hone
    _ ≤ ∫ (y : ℝ) in -Tp..Tp, G y := htwo
    _ = 56 * L * (x : ℝ) ^ (-(3 / 2) : ℝ) *
        (∫ (y : ℝ) in -Tp..Tp, 1 / ‖((-(3 / 2) : ℝ) : ℂ) + Complex.I * (y : ℂ)‖) := hthree
    _ ≤ 56 * L * (x : ℝ) ^ (-(3 / 2) : ℝ) * (4 * L) := by
        refine mul_le_mul_of_nonneg_left hfour (by positivity)
    _ ≤ 400 * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := hfive
    _ = 400 * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (Tp + 3) + 1) ^ 4 := by rw [hL]

/-! Development of the truncated Perron formula for Chebyshev's psi function. -/




/-! ## Local definitions and facts -/

/-- The per-step Perron integral `(1/2π) ∫_{-T}^{T} exp((σ+it)·log z)/(σ+it) dt`. -/
private noncomputable def perronStep (σ T : ℝ) (z : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ))) /
      ((σ : ℂ) + Complex.I * (t : ℂ)))

/-- The mangoldt error summand appearing in the Perron bound. -/
private noncomputable def mangoldtErrSummand (x T : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
    min 1 (1 / (T * |Real.log (x / (n : ℝ))|))

private lemma log_pos_of_three_le_pt {x : ℝ} (hx : 3 ≤ x) : 0 < Real.log x := by
  have h1x : 1 < x := by linarith
  exact Real.log_pos h1x

private lemma sigma_ge_one_pt {x : ℝ} (hx : 3 ≤ x) : 1 ≤ 1 + 1 / Real.log x := by
  have hlog : 0 < Real.log x := log_pos_of_three_le_pt hx
  nlinarith [one_div_pos.mpr hlog]

private lemma sigma_gt_one_pt {x : ℝ} (hx : 3 ≤ x) : 1 < 1 + 1 / Real.log x := by
  have hlog : 0 < Real.log x := log_pos_of_three_le_pt hx
  have : 0 < 1 / Real.log x := one_div_pos.mpr hlog
  linarith

private lemma nat_le_x_iff_floor_pt {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (n : ℝ) ≤ x ↔ n ≤ ⌊x⌋₊ := by
  constructor
  · intro h
    exact Nat.le_floor h
  · intro h
    have hcast : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h
    exact le_trans hcast (Nat.floor_le hx)

/-- `ψ x` equals the tsum of the (complex) von Mangoldt values over naturals ≤ x. -/
private lemma psi_eq_tsum_indicator_pt {x : ℝ} (hx : 0 ≤ x) :
    (Chebyshev.psi x : ℂ) = ∑' n : ℕ, if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0 := by
  have hmain : (∑' n : ℕ, if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
      = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0) := by
    apply tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.Icc 0 ⌊x⌋₊)
      (f := fun n : ℕ => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
    intro n hn
    by_cases hx0 : (n : ℝ) ≤ x
    · exfalso
      have hnfl : n ≤ ⌊x⌋₊ := (nat_le_x_iff_floor_pt hx n).mp hx0
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩)
    · simp [hx0]
  rw [hmain]
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hle : (n : ℝ) ≤ x := (nat_le_x_iff_floor_pt hx n).mpr (Finset.mem_Icc.mp hn).2
  simp [hle]

/-- Per-step deviation bound, restated for our definition `perronStep`. -/
private lemma perronStep_dev_le_pt {σ T z : ℝ} (hσ : 1 ≤ σ) (hT : 1 ≤ T) (hz : 0 < z) (hz1 : z ≠ 1) :
    ‖perronStep σ T z - (if 1 < z then (1 : ℂ) else 0)‖ ≤
      (32 / (2 * Real.pi)) * (z ^ σ) * min 1 (1 / (T * |Real.log z|)) := by
  simpa [perronStep] using
    (Commons.Analysis.Fourier.perronStep_deviation σ T z hσ hT hz hz1)

private lemma one_lt_div_iff_pt {x n : ℝ} (hn : 0 < n) : (1 < x / n) ↔ (n < x) := by
  rw [lt_div_iff₀ hn]
  simp

/-- Indicator equivalence for the Perron step: `1 < x/n` iff `n < x`. -/
private lemma perronStep_indicator_pt {x n : ℝ} (hn : 0 < n) :
    (if 1 < x / n then (1 : ℂ) else 0) = if n < x then (1 : ℂ) else 0 := by
  by_cases h : n < x
  · have : 1 < x / n := (one_lt_div_iff_pt hn).mpr h
    simp [h, this]
  · have hnot : ¬ 1 < x / n := by
      intro h1
      exact h ((one_lt_div_iff_pt hn).mp h1)
    simp [h, hnot]

/-- Bound on a single von-Mangoldt weighted Perron deviation term (n ≥ 1, n ≠ x). -/
private lemma perronStep_mangoldt_le_pt {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) {n : ℕ} (hn1 : 1 ≤ n)
    (hnx : (n : ℝ) ≠ x) :
    ‖perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)) -
        (if (n : ℝ) < x then (1 : ℂ) else 0)‖ ≤
      (32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
  have hxpos : 0 < x := by linarith
  have hz : 0 < x / (n : ℝ) := div_pos hxpos hnpos
  have hz1 : x / (n : ℝ) ≠ 1 := by
    intro h
    have hxeq : x = (n : ℝ) := by
      have h' := congrArg (fun y : ℝ => y * (n : ℝ)) h
      rw [div_mul_cancel₀ _ hnpos.ne'] at h'
      simpa using h'
    exact hnx hxeq.symm
  have hmain := perronStep_dev_le_pt (σ := 1 + 1 / Real.log x) (T := T) (z := x / (n : ℝ))
    (sigma_ge_one_pt hx3) (by linarith) hz hz1
  have hind : (if 1 < x / (n : ℝ) then (1 : ℂ) else 0) = if (n : ℝ) < x then (1 : ℂ) else 0 :=
    perronStep_indicator_pt (x := x) (n := (n : ℝ)) hnpos
  simpa [hind] using hmain

/-- `‖1 - w‖ ≤ 3/2` provided `‖w‖ ≤ 1/2`. -/
private lemma norm_sub_one_le_pt {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖(1 : ℂ) - w‖ ≤ 3 / 2 := by
  calc
    ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ 1 + 1 / 2 := by simpa using add_le_add_left hw (‖(1 : ℂ)‖)
    _ = 3 / 2 := by norm_num

private lemma perronStep_one_pt (σ T : ℝ) :
    perronStep σ T 1 =
      (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
        (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
  unfold perronStep
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp

private lemma perronStep_one_norm_pt {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ‖perronStep σ T 1‖ ≤ 1 / 2 := by
  rw [perronStep_one_pt]
  exact perronOne_bound σ T hσ hT

/-- Factor `Λ n` out of the indicator-cut von Mangoldt value. -/
private lemma mangoldt_if_mul_pt (x : ℝ) (n : ℕ) :
    (if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
      = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (if (n : ℝ) ≤ x then (1 : ℂ) else 0) := by
  by_cases h : (n : ℝ) ≤ x <;> simp [h]

/-- Pointwise bound for the `n`-th term of the error sum. -/
private lemma mangoldt_pointwise_pt {x T : ℝ} (hx3 : 3 ≤ x) (hT : 2 ≤ T) (n : ℕ) :
    ‖(if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
        - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
      ≤ ((ArithmeticFunction.vonMangoldt n : ℝ)) *
            ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) +
          (if (n : ℝ) = x then 2 * (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    by_cases hnx : (n : ℝ) = x
    · -- case n = x
      have hle : (n : ℝ) ≤ x := le_of_eq hnx
      have hxeq : x = (n : ℝ) := hnx.symm
      have hdiv : x / (n : ℝ) = 1 := by
        rw [hxeq]
        exact div_self (by exact_mod_cast (Nat.pos_of_ne_zero hn0).ne')
      rw [if_pos hle]
      rw [if_pos hnx]
      rw [hdiv]
      have hfac : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) -
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              perronStep (1 + 1 / Real.log x) T 1
          = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1) := by
        ring
      rw [hfac]
      have hnormΛ : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      have hQ : ‖(1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1‖ ≤ 3 / 2 := by
        apply norm_sub_one_le_pt
        apply perronStep_one_norm_pt (σ := 1 + 1 / Real.log x) (T := T)
        · have : 0 < 1 + 1 / Real.log x := by
            exact lt_of_lt_of_le zero_lt_one (sigma_ge_one_pt hx3)
          exact this
        · linarith
      calc
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1)‖
            ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ *
                ‖(1 : ℂ) - perronStep (1 + 1 / Real.log x) T 1‖ := by
              exact norm_mul_le _ _
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (3 / 2) := by
          rw [hnormΛ]
          exact mul_le_mul_of_nonneg_left hQ (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        _ ≤ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) := by
          nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
      simp [Real.log_one]
    · -- case n ≠ x
      rw [if_neg hnx]
      have hind : (if (n : ℝ) ≤ x then (1 : ℂ) else 0) = if (n : ℝ) < x then (1 : ℂ) else 0 := by
        by_cases hlt : (n : ℝ) < x
        · have hle' : (n : ℝ) ≤ x := le_of_lt hlt
          simp [hlt, hle']
        · have hle' : ¬ (n : ℝ) ≤ x := by
            intro h
            exact hlt (lt_of_le_of_ne h hnx)
          simp [hlt, hle']
      have hB : ‖(if (n : ℝ) < x then (1 : ℂ) else 0) - perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
          ≤ (32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
        rw [norm_sub_rev]
        exact perronStep_mangoldt_le_pt hx3 hT hn1 hnx
      calc
        ‖(if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))‖
            = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                ((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              rw [mangoldt_if_mul_pt x n, hind, ← mul_sub]
            _ ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ *
                ‖((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              exact norm_mul_le _ _
            _ = (ArithmeticFunction.vonMangoldt n : ℝ) *
                ‖((if (n : ℝ) < x then (1 : ℂ) else 0) -
                  perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)))‖ := by
              have hnorm : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
                  (ArithmeticFunction.vonMangoldt n : ℝ) := by
                simp [abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

              rw [hnorm]
            _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
                ((32 / (2 * Real.pi)) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
                  min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := by
              exact mul_le_mul_of_nonneg_left hB (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      simp

/-- The truncated Perron integral from the statement. -/
private noncomputable def perronInt (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
      (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))

/-- The Perron integral expands into the weighted per-step sums. -/
private lemma perronInt_eq_tsum_pt {x : ℝ} (hx : 1 < x) {T : ℝ} :
    perronInt x T =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        perronStep (1 + 1 / Real.log x) T (x / (n : ℝ)) := by
  unfold perronInt
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [mangoldt_perron_sum_eq x (by linarith) (1 + 1 / Real.log x) T (by
    have : 0 < 1 / Real.log x := one_div_pos.mpr hlog
    linarith)]
  apply tsum_congr
  intro n
  simp [perronStep, mul_assoc]

/-- Indicator-cut von Mangoldt sequence is summable (finite support). -/
private lemma summable_indicator_pt {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0) := by
  let s : Finset ℕ := Finset.Icc 0 ⌊x⌋₊
  have hfin : HasSum (fun n : ℕ => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
      (∑ n ∈ s, (if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)) := by
    apply hasSum_sum_of_ne_finset_zero (s := s)
    intro n hn
    by_cases hle : (n : ℝ) ≤ x
    · exfalso
      have hnfl : n ≤ ⌊x⌋₊ := (nat_le_x_iff_floor_pt hx n).mp hle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩)
    · simp [hle]
  exact hfin.summable

/-- A natural number equal to `x` must be `⌊x⌋₊`. -/
private lemma nat_eq_floor_of_eq_pt {x : ℝ} (n : ℕ) (h : (n : ℝ) = x) : n = ⌊x⌋₊ := by
  rw [← h]
  simp

/-- Extra term `2·Λ n` for the boundary index `n = x` is summable (support ≤ 1). -/
private lemma summable_extra_pt {x : ℝ} :
    Summable (fun n : ℕ => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) := by
  let s : Finset ℕ := {⌊x⌋₊}
  have hfin : HasSum (fun n : ℕ => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0)
      (∑ n ∈ s, (if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0)) := by
    apply hasSum_sum_of_ne_finset_zero (s := s)
    intro n hn
    have hnne : n ≠ ⌊x⌋₊ := by
      intro heq
      exact hn (Finset.mem_singleton.mpr heq)
    have hnx : (n : ℝ) ≠ x := by
      intro hx0
      exact hnne (nat_eq_floor_of_eq_pt n hx0)
    simp [hnx]
  exact hfin.summable

/-- The extra boundary contribution is exactly bounded by the boundary term of the statement:
`2·log x` when `x` is an integer, and `0` otherwise. -/
private lemma extra_tsum_le_refined_pt {x : ℝ} :
    (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) ≤
      (if (⌊x⌋₊ : ℝ) = x then 2 * Real.log x else 0) := by
  by_cases h : (⌊x⌋₊ : ℝ) = x
  · rw [if_pos h]
    have hsingle : ∀ n : ℕ, n ≠ ⌊x⌋₊ →
        (if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) = 0 := by
      intro n hn
      have hnx : (n : ℝ) ≠ x := by
        intro hx0
        exact hn (nat_eq_floor_of_eq_pt n hx0)
      simp [hnx]
    rw [tsum_eq_single ⌊x⌋₊ hsingle]
    simp only [h, if_true]
    have hlog : (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ) ≤ Real.log x := by
      calc (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ) ≤ Real.log (⌊x⌋₊ : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log (n := ⌊x⌋₊)
        _ = Real.log x := by rw [h]
    linarith
  · rw [if_neg h]
    have hzero : ∀ n : ℕ,
        (if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) = 0 := by
      intro n
      have hnx : (n : ℝ) ≠ x := by
        intro hx0
        exact h (by rw [← nat_eq_floor_of_eq_pt n hx0]; exact hx0)
      simp [hnx]
    exact le_of_eq (by rw [tsum_congr hzero, tsum_zero])

/-- The main inequality: `ψ(x)` approximates the truncated Perron integral. -/
private lemma psi_sub_perron_main_pt {x T : ℝ} (hx : 4 ≤ x) (hT : 2 ≤ T) :
    ‖(Chebyshev.psi x : ℂ) - perronInt x T‖ ≤
      (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) +
        (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) := by
  have hx3 : 3 ≤ x := by linarith
  let ind : ℕ → ℂ := fun n => if (n : ℝ) ≤ x then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0
  let q : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      perronStep (1 + 1 / Real.log x) T (x / (n : ℝ))
  let u : ℕ → ℂ := fun n => ind n - q n
  let a : ℕ → ℝ := fun n => mangoldtErrSummand x T n
  let extra : ℕ → ℝ := fun n => if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0
  let e : ℕ → ℝ := fun n => (32 / (2 * Real.pi)) * a n + extra n
  have hxpos : 0 < x := by linarith
  have hψ : (Chebyshev.psi x : ℂ) = ∑' n : ℕ, ind n := by
    dsimp [ind]
    exact psi_eq_tsum_indicator_pt hxpos.le
  have hJ : perronInt x T = ∑' n : ℕ, q n := by
    dsimp [q]
    exact perronInt_eq_tsum_pt (x := x) (hx := by linarith) (T := T)
  have hsum_a : Summable a := by
    exact (mangoldtPerronError_bound_2472 x hx T hT).1
  have hsum_ind : Summable ind := by
    simpa [ind] using (summable_indicator_pt (x := x) hxpos.le)
  have hsum_extra : Summable extra := by
    simpa [extra] using (summable_extra_pt (x := x))
  have hpt : ∀ n : ℕ, ‖u n‖ ≤ e n := by
    intro n
    have hmain := mangoldt_pointwise_pt (x := x) (T := T) hx3 hT n
    -- mangoldt_pointwise_pt concludes ‖(if n≤x then Λn else 0) − (Λn)·Q‖ ≤ Λn·B + extra
    simp only [u, ind, q, e, a, extra, mangoldtErrSummand] at hmain ⊢
    -- RHS of hmain: (Λ n) * ((32/(2π)) * ((x/n)^c) * min 1 ...) + if (n:ℝ)=x then 2Λn else 0
    -- = (32/(2π))·(Λn·(x/n)^c·min...) + extra n
    convert hmain using 1
    ring
  have hsum_e : Summable e := by
    have hmul : Summable (fun n : ℕ => (32 / (2 * Real.pi)) * a n) := by
      simpa [a] using (hsum_a.const_smul (32 / (2 * Real.pi)) : Summable (fun n => (32 / (2 * Real.pi)) • a n))
    exact Summable.add hmul hsum_extra
  have hsum_norm_u : Summable (fun n : ℕ => ‖u n‖) := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => (hpt n)) hsum_e
  have hsum_u : Summable u := Summable.of_norm hsum_norm_u
  calc
    ‖(Chebyshev.psi x : ℂ) - perronInt x T‖ = ‖(∑' n : ℕ, ind n) - (∑' n : ℕ, q n)‖ := by
      rw [hψ, hJ]
    _ = ‖∑' n : ℕ, u n‖ := by
      have hqsum : (∑' n : ℕ, q n) = (∑' n : ℕ, ind n) - (∑' n : ℕ, u n) := by
        have hts := Summable.tsum_sub hsum_ind hsum_u
        -- hts : Σ'(ind - u) = Σ'ind - Σ'u
        -- q n = ind n - u n
        simpa [u, q] using hts
      rw [hqsum]
      congr 1
      ring
    _ ≤ ∑' n : ℕ, ‖u n‖ := norm_tsum_le_tsum_norm hsum_norm_u
    _ ≤ ∑' n : ℕ, e n := by
      exact hasSum_le (fun n => hpt n) hsum_norm_u.hasSum hsum_e.hasSum
    _ = (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) + (∑' n : ℕ, extra n) := by
      have hmul' : (∑' n : ℕ, (32 / (2 * Real.pi)) * a n) = (32 / (2 * Real.pi)) * (∑' n : ℕ, a n) := by
        exact tsum_mul_left (a := (32 / (2 * Real.pi))) (f := a)
      have hts := Summable.tsum_add (f := fun n : ℕ => (32 / (2 * Real.pi)) * a n) (g := extra)
        (by simpa [a] using (hsum_a.const_smul (32 / (2 * Real.pi)) : Summable (fun n => (32 / (2 * Real.pi)) • a n))) hsum_extra
      -- hts : Σ'( (32/2π)·a + extra ) = Σ'((32/2π)·a) + Σ'extra
      rw [hts, hmul']
    _ ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) +
          (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) := by
      rw [show (∑' n : ℕ, a n) = ∑' n : ℕ, mangoldtErrSummand x T n by rfl]

theorem chebyshevPsi_truncatedPerron_40000 :
    ∀ (x : ℝ), 4 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        40000 * (x * (Real.log x) ^ 2 / T + Real.log x *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) := by
  have hCA : ∀ x : ℝ, 4 ≤ x → ∀ T : ℝ, 2 ≤ T →
      Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ∧
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
        2472 * (x * (Real.log x) ^ 2 / T + Real.log x *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) :=
    mangoldtPerronError_bound_2472
  intro x hx T hT
  have hx3 : 3 ≤ x := by linarith
  have hm := psi_sub_perron_main_pt (x := x) (T := T) hx hT
  have hA : (∑' n : ℕ, mangoldtErrSummand x T n) ≤
      (2472 : ℝ) * (x * (Real.log x) ^ 2 / T + Real.log x *
        (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
         min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) := (hCA x hx T hT).2
  have hb := extra_tsum_le_refined_pt (x := x)
  have hc : 0 ≤ (32 / (2 * Real.pi)) := by positivity
  calc
    ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖
        ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) +
            (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0) := by
          change ‖(Chebyshev.psi x : ℂ) - perronInt x T‖ ≤
            (32 / (2 * Real.pi)) * (∑' n : ℕ, mangoldtErrSummand x T n) +
              (∑' n : ℕ, if (n : ℝ) = x then (2 * (ArithmeticFunction.vonMangoldt n : ℝ)) else 0)
          exact hm
    _ ≤ (32 / (2 * Real.pi)) *
          ((2472 : ℝ) * (x * (Real.log x) ^ 2 / T + Real.log x *
            (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
             min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|))))) +
          (if (⌊x⌋₊ : ℝ) = x then 2 * Real.log x else 0) := by
          linarith [mul_le_mul_of_nonneg_left hA hc, hb]
    _ = ((32 / (2 * Real.pi)) * 2472) * (x * (Real.log x) ^ 2 / T + Real.log x *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
          (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) := by
          ring
    _ ≤ 40000 * (x * (Real.log x) ^ 2 / T + Real.log x *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
          (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) := by
          have hc : ((32 / (2 * Real.pi)) * 2472) ≤ 40000 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
            nlinarith [Real.pi_gt_three]
          have hE : 0 ≤ x * (Real.log x) ^ 2 / T + Real.log x *
              (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
               min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|))) := by
            have h1 : 0 ≤ x * (Real.log x) ^ 2 / T :=
              div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
            have h2 : 0 ≤ min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) :=
              le_min (by norm_num) (div_nonneg (by linarith) (mul_nonneg (by linarith) (abs_nonneg _)))
            have h3 : 0 ≤ min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)) :=
              le_min (by norm_num) (div_nonneg (by linarith) (mul_nonneg (by linarith) (abs_nonneg _)))
            nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ x)]
          nlinarith [mul_le_mul_of_nonneg_right hc hE]

theorem chebyshevPsi_aux_b (h : RiemannHypothesis) (Cp CL : ℝ)
    (hCppos : 0 < Cp) (hCple : Cp ≤ 40000) (hCLpos : 0 < CL) (hCLle : CL ≤ 400)
    (hCp : ∀ x : ℝ, 4 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(Chebyshev.psi x : ℂ) - (1 / (2 * Real.pi)) *
          (∫ (t : ℝ) in -T..T,
            (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        Cp * (x * (Real.log x) ^ 2 / T + Real.log x *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0))
    (hCL : ∀ x Tp : ℝ, 1 ≤ x → 5 ≤ Tp →
      ‖(∫ (y : ℝ) in -Tp..Tp,
        (-(logDeriv riemannZeta₁ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) *
            ((x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
              ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) +
          (x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
            (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) *
              (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) - 1))))‖ ≤
        CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (Tp + 3) + 1) ^ 4) :
    ∃ C C₂ D : ℝ, 0 < C ∧ 0 < C₂ ∧ 0 < D ∧ C ≤ 10 ^ 9 ∧ C₂ ≤ 10 ^ 5 ∧ D ≤ 400 ∧
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ T δ K : ℝ,
      5 ≤ T → x ≤ T ^ 2 → 0 < δ → 1 ≤ K → 1 ≤ K * (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ T ∧ ρ.im ≠ -T) →
      ‖(Chebyshev.psi x : ℂ) - ((x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
          ∑ ρ ∈ zRectZeros (R := 2 + |T|) (by positivity) (-(3 / 2)) (1 + 1 / Real.log x) T,
            (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
        C * (x * (Real.log (T + 3) + 1) ^ 3 / T) * K +
        C₂ * ((Real.log (T + 3) + 1) *
          (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
           min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
        (if (Nat.floor x : ℝ) = x then 4 * (Real.log (T + 3) + 1) else 0) +
        D * ((x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4) := by
  obtain ⟨CT, hCTpos, hCTle, hCT⟩ := edgeT_bound_neg_b h
  refine ⟨Cp + 4 * CT / Real.pi + 1, 2 * Cp + 1, CL / (2 * Real.pi) + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < 4 * CT / Real.pi := div_pos (by linarith) Real.pi_pos
    linarith
  · linarith
  · have : 0 < CL / (2 * Real.pi) := div_pos hCLpos (by positivity)
    linarith
  · have hpi : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
    have h1 : 4 * CT / Real.pi ≤ 4 * 750000000 / 3.14 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hCTle, hpi]
    linarith
  · linarith
  · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h1 : CL / (2 * Real.pi) ≤ 400 / (2 * 3) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hCLle, hpi]
    linarith
  · refine ⟨Real.exp 9 + 100, ?_⟩
    intro x hx0 T δ K hT hTx hδ0 hK1 hKδ hgap hgood
    have hexp9 : Real.exp 9 ≤ x := by linarith
    have hx1 : (1 : ℝ) ≤ x :=
      le_trans (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 9)) hexp9
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
    have hlog8 : (8 : ℝ) ≤ Real.log x := by
      have h1 : Real.log (Real.exp 9) ≤ Real.log x :=
        Real.log_le_log (Real.exp_pos 9) hexp9
      rw [Real.log_exp] at h1
      linarith
    have hT0 : 0 < T := by linarith
    set L : ℝ := Real.log (T + 3) + 1 with hL
    have hL0 : 0 ≤ L := by
      rw [hL]
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
      linarith
    have hlogx_le : Real.log x ≤ 2 * L := by
      have h1 : Real.log x ≤ Real.log (T ^ 2) := Real.log_le_log hxpos hTx
      have h2 : Real.log (T ^ 2) = 2 * Real.log T := by
        rw [Real.log_pow]; push_cast; ring
      have h3 : Real.log T ≤ Real.log (T + 3) := Real.log_le_log hT0 (by linarith)
      rw [h2] at h1
      rw [hL]
      linarith
    have hLlogx : (Real.log x) ^ 2 ≤ L ^ 3 := by
      have h4 : (4 : ℝ) ≤ L := by linarith [hlogx_le, hlog8]
      have h5 : 0 ≤ L ^ 2 * (L - 4) := mul_nonneg (sq_nonneg L) (by linarith)
      nlinarith [hlogx_le, h4, hL0, h5, sq_nonneg (Real.log x)]
    set Gx : ℝ := min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
      min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)) with hGx
    have hG0 : 0 ≤ Gx := by
      rw [hGx]
      have h2x : 0 ≤ 2 * x := by linarith
      have h1 : 0 ≤ 2 * x / (T * |x - (Nat.floor x : ℝ)|) :=
        div_nonneg h2x (mul_nonneg hT0.le (abs_nonneg _))
      have h2 : 0 ≤ 2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|) :=
        div_nonneg h2x (mul_nonneg hT0.le (abs_nonneg _))
      exact add_nonneg (le_min (by norm_num) h1) (le_min (by norm_num) h2)
    have h1b : 1 < 1 + 1 / Real.log x := by
      have : 0 < 1 / Real.log x := by positivity
      linarith
    have hb2 : 1 + 1 / Real.log x ≤ 2 := by
      have hlog1 : (1 : ℝ) ≤ Real.log x := by linarith
      have h1 : 1 / Real.log x ≤ 1 := by rw [div_le_one (by linarith)]; exact hlog1
      linarith
    have hR : (0 : ℝ) ≤ 2 + |T| := by positivity
    have ha : -(3 / 2 : ℝ) ≤ -(3 / 2) := le_refl _
    have ha0 : (-(3 / 2) : ℝ) < 0 := by norm_num
    have hrect : closedContourRect (-(3 / 2)) (1 + 1 / Real.log x) T ⊆
        Metric.closedBall (0 : ℂ) (2 + |T|) := by
      intro z hz
      have hab : (-(3 / 2) : ℝ) ≤ 1 + 1 / Real.log x := by
        have : 0 < 1 / Real.log x := by positivity
        linarith
      have hTle : -T ≤ T := by linarith
      have hmem := (mem_closedContourRect hab hTle z).mp hz
      obtain ⟨h1, h2, h3, h4⟩ := hmem
      have hre : |z.re| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith
      have him : |z.im| ≤ T := by
        rw [abs_le]; constructor <;> linarith
      have hnorm : ‖z‖ ≤ 2 + |T| := by
        have h1' : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        have hTabs : |T| = T := abs_of_nonneg hT0.le
        rw [hTabs]
        linarith
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm
    have hx4 : (4 : ℝ) ≤ x := by have := Real.exp_pos 9; linarith
    have hP := hCp x hx4 T (by linarith)
    have hE := edgeR_eq_perron_raw x (1 + 1 / Real.log x) T h1b
    rw [← hE] at hP
    have hScal : (1 / (2 * Real.pi)) * edgeR (1 + 1 / Real.log x) T (psiIntF1 x) =
        edgeR (1 + 1 / Real.log x) T (psiIntF1 x) * ((2 : ℂ) * (Real.pi : ℂ))⁻¹ := by
      field_simp [Real.pi_ne_zero]
    rw [hScal] at hP
    have hPR := perron_raw_sub_zero_sum_bound_farLeft h hR hxpos ha ha0 h1b hT0 hrect hgood
    let A : ℂ := (Chebyshev.psi x : ℂ)
    let B : ℂ := edgeR (1 + 1 / Real.log x) T (psiIntF1 x) * ((2 : ℂ) * (Real.pi : ℂ))⁻¹
    let Cc : ℂ := (x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
        ∑ ρ ∈ zRectZeros (R := 2 + |T|) hR (-(3 / 2)) (1 + 1 / Real.log x) T,
          (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ
    have hP' : ‖A - B‖ ≤ Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) := by
      simpa [A, B, hGx] using hP
    have hPR' : ‖B - Cc‖ ≤
        (‖edgeB (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
          ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
          ‖edgeL (-(3 / 2)) T (psiIntF1 x)‖) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ := by
      simpa [B, Cc] using hPR
    have htri : ‖A - Cc‖ ≤ ‖A - B‖ + ‖B - Cc‖ := by
      calc ‖A - Cc‖ = ‖(A - B) + (B - Cc)‖ := by congr 1; abel
        _ ≤ ‖A - B‖ + ‖B - Cc‖ := norm_add_le (A - B) (B - Cc)
    have hBTn : ‖edgeB (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ =
        ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ := by
      rw [edgeB_eq_conj_edgeT hxpos, Complex.norm_conj]
    have hsideT : ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ ≤
        CT * K * (L ^ 3 * ((x : ℝ) ^ (1 + 1 / Real.log x) / T)) := by
      have hh := hCT x (-(3 / 2)) (1 + 1 / Real.log x) T δ K hx1 (by norm_num)
        (by linarith : (-(3 / 2) : ℝ) ≤ 1 / 8) (by linarith) hb2 hT hδ0 hK1 hKδ hgap
      simpa only [hL] using hh
    have hxpow : (x : ℝ) ^ (1 + 1 / Real.log x) ≤ 4 * x := by
      have hlog0 : Real.log x ≠ 0 := by linarith
      have hsplit : (x : ℝ) ^ (1 + 1 / Real.log x) =
          (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ (1 / Real.log x) :=
        Real.rpow_add hxpos 1 (1 / Real.log x)
      have hone : (x : ℝ) ^ (1 : ℝ) = x := Real.rpow_one x
      have hexp : (x : ℝ) ^ (1 / Real.log x) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        field_simp
      rw [hsplit, hone, hexp]
      have h4 : Real.exp 1 ≤ 4 := by
        have := Real.exp_one_lt_d9
        linarith
      nlinarith [Real.exp_pos 1]
    have hsideL : ‖edgeL (-(3 / 2)) T (psiIntF1 x)‖ ≤
        CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4 := by
      have hh := hCL x T hx1 (by linarith)
      have hEq : edgeL (-(3 / 2)) T (psiIntF1 x) =
          (∫ (y : ℝ) in -T..T,
            (-(logDeriv riemannZeta₁ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) *
                ((x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
                  ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) +
              (x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
                (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) *
                  (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) - 1)))) := by
        rw [edgeL, zRect_re]
        apply intervalIntegral.integral_congr
        intro y _
        simp only [psiIntF1, mul_comm Complex.I]
      rw [hEq]
      simpa only [hL] using hh
    have h2pi : ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ = 1 / (2 * Real.pi) :=
      norm_inv_two_pi_I
    have hsum : ‖edgeB (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
        ‖edgeT (-(3 / 2)) (1 + 1 / Real.log x) T (psiIntF1 x)‖ +
        ‖edgeL (-(3 / 2)) T (psiIntF1 x)‖ ≤
        2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := by
      have hT4 : CT * K * (L ^ 3 * ((x : ℝ) ^ (1 + 1 / Real.log x) / T)) ≤
          CT * K * (L ^ 3 * (4 * x / T)) := by
        have hdiv : (x : ℝ) ^ (1 + 1 / Real.log x) / T ≤ 4 * x / T :=
          div_le_div_of_nonneg_right (by linarith [hxpow]) hT0.le
        have h1 : L ^ 3 * ((x : ℝ) ^ (1 + 1 / Real.log x) / T) ≤ L ^ 3 * (4 * x / T) :=
          mul_le_mul_of_nonneg_left hdiv (pow_nonneg hL0 3)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hL4 : CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4 =
          CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := by rw [hL]
      rw [hBTn, hL4]
      linarith
    have hbase : ‖A - Cc‖ ≤ Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) +
        (2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) *
          (1 / (2 * Real.pi)) := by
      have h1 := htri
      have h2 := hPR'
      rw [h2pi] at h2
      have h3 : ‖B - Cc‖ ≤ (2 * (CT * K * (L ^ 3 * (4 * x / T))) +
          CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) * (1 / (2 * Real.pi)) :=
        le_trans h2 (mul_le_mul_of_nonneg_right hsum (by positivity))
      linarith
    have hCp0 : 0 ≤ Cp := hCppos.le
    have hCT0 : 0 ≤ CT := hCTpos.le
    have hCL0 : 0 ≤ CL := hCLpos.le
    have hxlog : 0 ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hxpos.le _
    have hlogx0 : 0 ≤ Real.log x := by linarith
    have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
    have hL4nn : 0 ≤ L ^ 4 := pow_nonneg hL0 4
    have hxT : 0 ≤ x / T := div_nonneg hxpos.le hT0.le
    have hxl3 : 0 ≤ x * L ^ 3 / T :=
      div_nonneg (mul_nonneg hxpos.le hL3) hT0.le
    have hxl4 : 0 ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _) hL4nn
    have hCLpi : 0 ≤ CL / (2 * Real.pi) := div_nonneg hCL0 (by positivity)
    have hpi4 : 0 ≤ 4 * CT / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
    have hK0 : 0 ≤ K := by linarith
    have hind : (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) ≤
        (if (Nat.floor x : ℝ) = x then 4 * L else 0) := by
      by_cases hh : (Nat.floor x : ℝ) = x
      · rw [if_pos hh, if_pos hh]; linarith [hlogx_le]
      · rw [if_neg hh, if_neg hh]
    have htermp : Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) ≤
        Cp * (x * L ^ 3 / T) + (2 * Cp) * (L * Gx) := by
      have h1 : x * (Real.log x) ^ 2 / T ≤ x * L ^ 3 / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLlogx hxpos.le) hT0.le
      have h2 : Real.log x * Gx ≤ (2 * L) * Gx :=
        mul_le_mul_of_nonneg_right hlogx_le hG0
      have h3 : Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) =
          Cp * (x * (Real.log x) ^ 2 / T) + Cp * (Real.log x * Gx) := by ring
      have h4 : Cp * (x * (Real.log x) ^ 2 / T) ≤ Cp * (x * L ^ 3 / T) :=
        mul_le_mul_of_nonneg_left h1 hCp0
      have h5 : Cp * (Real.log x * Gx) ≤ Cp * ((2 * L) * Gx) :=
        mul_le_mul_of_nonneg_left h2 hCp0
      have h6 : Cp * ((2 * L) * Gx) = (2 * Cp) * (L * Gx) := by ring
      linarith [h3, h4, h5, h6]
    have hP1 : 0 ≤ x * L ^ 3 / T := hxl3
    have hPK : Cp * (x * L ^ 3 / T) ≤ Cp * (x * L ^ 3 / T) * K := by
      have h1 : (x * L ^ 3 / T) ≤ K * (x * L ^ 3 / T) := by
        have := mul_le_mul_of_nonneg_right hK1 hP1
        simpa using this
      calc Cp * (x * L ^ 3 / T) ≤ Cp * (K * (x * L ^ 3 / T)) :=
            mul_le_mul_of_nonneg_left h1 hCp0
        _ = Cp * (x * L ^ 3 / T) * K := by ring
    have hterm2 : (2 * (CT * K * (L ^ 3 * (4 * x / T)))) * (1 / (2 * Real.pi)) ≤
        (4 * CT / Real.pi) * (x * L ^ 3 / T) * K := by
      apply le_of_eq
      field_simp [Real.pi_ne_zero, (by linarith : T ≠ 0)]
      try ring
    have hterm3 : (CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) * (1 / (2 * Real.pi)) ≤
        (CL / (2 * Real.pi)) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) := by
      apply le_of_eq
      field_simp [Real.pi_ne_zero] <;> ring
    have hfin : Cp * (x * (Real.log x) ^ 2 / T + Real.log x * Gx) +
        (if (Nat.floor x : ℝ) = x then 2 * Real.log x else 0) +
        (2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) *
          (1 / (2 * Real.pi)) ≤
        (Cp + 4 * CT / Real.pi + 1) * (x * L ^ 3 / T) * K + (2 * Cp + 1) * (L * Gx) +
        (if (Nat.floor x : ℝ) = x then 4 * L else 0) +
        (CL / (2 * Real.pi) + 1) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) := by
      have hsplit : (2 * (CT * K * (L ^ 3 * (4 * x / T))) + CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) *
          (1 / (2 * Real.pi)) =
          (2 * (CT * K * (L ^ 3 * (4 * x / T)))) * (1 / (2 * Real.pi)) +
          (CL * (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) * (1 / (2 * Real.pi)) := by ring
      have hexp : (Cp + 4 * CT / Real.pi + 1) * (x * L ^ 3 / T) * K
          = Cp * (x * L ^ 3 / T) * K + (4 * CT / Real.pi) * (x * L ^ 3 / T) * K
            + (x * L ^ 3 / T) * K := by ring
      have hcomb : Cp * (x * L ^ 3 / T) + (4 * CT / Real.pi) * (x * L ^ 3 / T) * K
          ≤ Cp * (x * L ^ 3 / T) * K + (4 * CT / Real.pi) * (x * L ^ 3 / T) * K
            + (x * L ^ 3 / T) * K := by
        have h2 : 0 ≤ (x * L ^ 3 / T) * K := mul_nonneg hP1 hK0
        linarith [hPK, h2]
      have h2cp : (2 * Cp) * (L * Gx) ≤ (2 * Cp + 1) * (L * Gx) := by
        have h2 : 0 ≤ L * Gx := mul_nonneg hL0 hG0
        nlinarith [h2]
      have hcl : (CL / (2 * Real.pi)) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4)
          ≤ (CL / (2 * Real.pi) + 1) * ((x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4) := by
        have h2 : 0 ≤ (x : ℝ) ^ (-(3 / 2) : ℝ) * L ^ 4 := hxl4
        nlinarith [h2]
      rw [hsplit, hexp]
      linarith [htermp, hterm2, hterm3, hind, hcomb, h2cp, hcl]
    linarith [hbase, hfin]

theorem chebyshevPsi_at_height_farLeft_neg_consts_bounded (h : RiemannHypothesis) :
    ∃ C C₂ D : ℝ, 0 < C ∧ 0 < C₂ ∧ 0 < D ∧ C ≤ 10 ^ 9 ∧ C₂ ≤ 10 ^ 5 ∧ D ≤ 400 ∧
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ T δ K : ℝ, 5 ≤ T → x ≤ T ^ 2 → 0 < δ → 1 ≤ K →
      1 ≤ K * (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ T ∧ ρ.im ≠ -T) →
      ‖(Chebyshev.psi x : ℂ) - ((x : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
        ∑ ρ ∈ Commons.NumberTheory.Zeta.zRectZeros (R := 2 + |T|) (by positivity) (-(3 / 2)) (1 + 1 / Real.log x) T,
          (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
        C * (x * (Real.log (T + 3) + 1) ^ 3 / T) * K +
        C₂ * ((Real.log (T + 3) + 1) * (min 1 (2 * x / (T * |x - (Nat.floor x : ℝ)|)) +
          min 1 (2 * x / (T * |x - ((Nat.floor x : ℝ) + 1)|)))) +
        (if (Nat.floor x : ℝ) = x then 4 * (Real.log (T + 3) + 1) else 0) +
        D * ((x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (T + 3) + 1) ^ 4) := by
  have hCLexp : ∀ x Tp : ℝ, 1 ≤ x → 5 ≤ Tp →
      ‖(∫ (y : ℝ) in -Tp..Tp,
        (-(logDeriv riemannZeta₁ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) *
            ((x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
              ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ))) +
          (x : ℂ) ^ ((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) /
            (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) *
              (((↑(-(3 / 2) : ℝ) : ℂ) + Complex.I * (↑y : ℂ)) - 1))))‖ ≤
        (400 : ℝ) * (x : ℝ) ^ (-(3 / 2) : ℝ) * (Real.log (Tp + 3) + 1) ^ 4 := by
    intro x Tp hx hT
    have hh := edgeL_neg_three_halves_bound_b h x Tp hx hT
    simpa only [psiIntF1] using hh
  exact chebyshevPsi_aux_b h 40000 400 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    chebyshevPsi_truncatedPerron_40000 hCLexp

end Commons.NumberTheory.Zeta
