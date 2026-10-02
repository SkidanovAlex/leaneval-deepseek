import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_growth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le

open Complex Filter Set
open scoped Real Topology BigOperators
noncomputable section
namespace Commons.NumberTheory.Zeta

-- ############ R2: emN machinery (copied from commons pattern) ############

private lemma norm_nat_cpow_neg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(((n : ℕ) : ℂ) ^ (-s))‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)]
  rw [Complex.neg_re]

private lemma norm_head_le (N : ℕ) (s : ℂ) :
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
  calc
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact norm_nat_cpow_neg hn1 s

private lemma norm_add_mul_I_le (σ t : ℝ) (hσ0 : 0 ≤ σ) :
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

private lemma pole_norm_le (s : ℂ) (ht : 1 ≤ |s.im|) (N : ℕ) (hN : 1 ≤ N) :
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
    linarith only [ht, hcontra]
  have hnorm_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hsne
  have hden : 1 ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).im| ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
    have h2 : |(s - 1).im| = |s.im| := by simp
    linarith only [ht, h1, h2]
  have hpow_nonneg : 0 ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := Real.rpow_nonneg hN0le _
  calc
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ = ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ / ‖s - 1‖ := by rw [norm_div]
    _ = ((N : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by rw [hnormN]
    _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [div_le_iff₀ hnorm_pos]
      calc
        ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) * 1 := by ring
        _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) * ‖s - 1‖ := mul_le_mul_of_nonneg_left hden hpow_nonneg

private lemma em_tail_norm_le (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
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
private lemma zeta_bound_emN3 {σ t : ℝ} (hσ0 : 0 < σ) (hσ3 : σ ≤ 3) (ht : 1 ≤ |t|)
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
    linarith only [ht, habs]
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN0
  have hNnorm : ‖s‖ ≤ (N : ℝ) := by
    have h1 : ‖s‖ ≤ σ + |t| := by
      simpa [s] using norm_add_mul_I_le σ t (le_of_lt hσ0)
    have h2 : σ + |t| ≤ (N : ℝ) := by
      have : |t| + 3 ≤ (N : ℝ) := hNt
      linarith only [hσ3, hNt]
    linarith only [hσ3, hNt, h1]
  have hmul' : ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by
    calc
      ((N : ℕ) : ℝ) ^ (1 - s.re)
          = ((N : ℕ) : ℝ) ^ (1 + -s.re) := by rw [sub_eq_add_neg]
      _ = ((N : ℕ) : ℝ) ^ (1 : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by rw [Real.rpow_add hN0]
      _ = ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) := by rw [Real.rpow_one]
  have hmul : ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ) ^ (-s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) := hmul'.symm
  have htailT : ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) := by
    have h := em_tail_norm_le s hs0 hs1 N hN
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
    have h := pole_norm_le s ht' N hN
    dsimp [M, P]
    rw [hsre] at h
    exact h
  have hAhead : ‖H‖ ≤ A0 := by
    have h := norm_head_le N s
    dsimp [H, A0]
    rw [hsre] at h
    exact h
  have htri : ‖H + M + T‖ ≤ ‖H‖ + ‖M‖ + ‖T‖ := by
    have h1 : ‖H + M + T‖ ≤ ‖H + M‖ + ‖T‖ := norm_add_le (H + M) T
    have h2 : ‖H + M‖ ≤ ‖H‖ + ‖M‖ := norm_add_le H M
    linarith only [h1, h2]
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
private theorem zeta_re_quarter_three_poly :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ t : ℝ), (1 / 4 : ℝ) ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4 := by
  refine ⟨12, by norm_num, ?_⟩
  intro σ t hσlo hσhi ht
  have hσ0 : 0 < σ := by linarith only [hσlo]
  have hσn0 : 0 ≤ σ := le_of_lt hσ0
  let N : ℕ := Nat.floor |t| + 4
  have hNge : |t| + 3 ≤ (N : ℝ) := by
    dsimp [N]
    rw [Nat.cast_add]
    have hlt : |t| < ((Nat.floor |t| : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one |t|
    norm_num
    linarith only [hlt]
  have hNle : (N : ℝ) ≤ |t| + 4 := by
    dsimp [N]
    rw [Nat.cast_add]
    norm_num
    have hfl : ((Nat.floor |t| : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    linarith only [hfl]
  have hN1 : 1 ≤ N := by
    have hfl1 : (1 : ℕ) ≤ Nat.floor |t| := by
      exact Nat.le_floor (by exact_mod_cast ht : ((1 : ℕ) : ℝ) ≤ |t|)
    dsimp [N]
    omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hb := zeta_bound_emN3 (σ := σ) (t := t) hσ0 hσhi ht N hN1 hNge
  have hA0 : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ (N : ℝ) := by
    have hle : ∀ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) ≤ (1 : ℝ) := by
      intro n hn
      have hn1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1n
      calc
        ((n : ℕ) : ℝ) ^ (-σ) ≤ ((n : ℕ) : ℝ) ^ (0 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hσ0] : -σ ≤ 0)
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
    have h4s : (1 : ℝ) ≤ 4 * σ := by linarith only [hσlo]
    simpa using (div_le_iff₀ hσ0).mpr h4s
  have h15 : (1 + 1 / σ : ℝ) ≤ 5 := by
    have : (1 / σ : ℝ) ≤ 4 := by simpa [one_div] using hinv
    linarith only [this]
  have hP : ((N : ℕ) : ℝ) ^ (1 - σ) ≤ (N : ℝ) := by
    calc
      ((N : ℕ) : ℝ) ^ (1 - σ) ≤ ((N : ℕ) : ℝ) ^ (1 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith only [hσ0] : 1 - σ ≤ 1)
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
      have ht13 : (|t| + 4 : ℝ) ≤ 2 * (|t| + 3) := by linarith only [ht]
      linarith only [ht]
    _ ≤ 12 * (|t| + 3) ^ 4 := by
      have hx : 1 ≤ |t| + 3 := by linarith only [ht]
      have hpow : (|t| + 3 : ℝ) ≤ (|t| + 3) ^ 4 := by
        have h1 : (|t| + 3 : ℝ) ^ (1 : ℕ) ≤ (|t| + 3) ^ 4 := pow_le_pow_right₀ hx (by norm_num : (1:ℕ) ≤ 4)
        simpa using h1
      exact mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 12)
    _ = (12 : ℝ) * (|t| + 3) ^ 4 := by norm_num


-- ############ R1: functional-equation machinery ############

/-- Gamma upper bound on the strip `3/4 ≤ x ≤ 2` with polynomial degree 2. -/
private lemma gamma_strip_poly2 {x t : ℝ} (hxlo : (3 / 4 : ℝ) ≤ x) (hx2 : x ≤ 2) (ht : 1 ≤ |t|) :
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
      (h1 := (show (1 : ℝ) ≤ x + 1 by linarith only [hxlo])) (hσL := (show x + 1 ≤ 2 by linarith only [hx1])) t
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
private lemma cos_pi_two_bound {σ t : ℝ} (w : ℂ) (hw : w = 1 - ((σ : ℂ) + I * (t : ℂ))) :
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
private theorem zeta_strip_threeQuarter_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (u t : ℝ), (3 / 4 : ℝ) ≤ u → u ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((u : ℂ) + I * (t : ℂ))‖ ≤ C * (|t| + 3) := by
  rcases zeta_strip_growth with ⟨C0, hC0, hC0spec⟩
  refine ⟨5 * C0, mul_pos (by norm_num) hC0, ?_⟩
  intro u t hu h2 ht
  have hb := hC0spec (1 / 4) u t (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) (by linarith only [hu] : (1 / 2 + 1 / 4 : ℝ) ≤ u) h2 ht
  -- hb : ‖ζ(u+it)‖ ≤ C0 * (1 + 1 / (1/4)) * (|t| + 3) ^ (1/2 - (1/4)/2)
  have hpow : (|t| + 3) ^ ((1 / 2 - (1 / 4) / 2 : ℝ)) ≤ |t| + 3 := by
    have hx : 1 ≤ |t| + 3 := by linarith only [ht]
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
        linarith only []
      have hx0 : 0 ≤ |t| + 3 := by positivity
      linarith only []


/-- Region lemma 1 (`-1 ≤ σ ≤ 1/4`): functional equation + Gamma bounds. -/
private theorem zeta_left_poly :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ t : ℝ), -1 ≤ σ → σ ≤ 1 / 4 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4 := by
  rcases zeta_strip_threeQuarter_two with ⟨C34, hC34pos, hC34spec⟩
  let G2 : ℝ := Commons.Analysis.Complex.Mbig * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)
  have hM : 0 < Commons.Analysis.Complex.Mbig := by
    dsimp [Commons.Analysis.Complex.Mbig]
    positivity
  have hG2pos : 0 < G2 := by
    dsimp [G2]
    exact mul_pos (mul_pos hM (Real.exp_pos 1))
      (Real.rpow_pos_of_pos (by positivity : 0 < Real.pi / 2) (2 : ℝ))
  refine ⟨2 * G2 * C34, by positivity, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let u : ℝ := 1 - σ
  let w : ℂ := 1 - s
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  have hu_ge : (3 / 4 : ℝ) ≤ u := by dsimp [u]; linarith only [hσhi]
  have hu_le : u ≤ 2 := by dsimp [u]; linarith only [hσlo]
  have hwim : w.im = -t := by dsimp [w, s]; simp
  have hw_ne : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have him := congrArg Complex.im hn
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith only [him]
    rw [ht0] at ht
    norm_num at ht
  have hw1 : w ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    rw [hwim] at him
    simp at him
    have ht0 : t = 0 := by linarith only [him]
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
      linarith only [hpi]
    have hle : σ - 1 ≤ 0 := by linarith only [hσhi]
    calc
      (2 * Real.pi : ℝ) ^ (σ - 1) ≤ (2 * Real.pi : ℝ) ^ (0 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hx hle
      _ = 1 := by rw [Real.rpow_zero]
  -- factor: Gamma
  have hGn0 : ‖Complex.Gamma w‖ ≤
      G2 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
    have h := gamma_strip_poly2 (x := u) (t := -t) hu_ge hu_le (by simpa using ht)
    rw [hwform]
    simpa [G2] using h
  -- factor: cos
  have hcos : ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ Real.exp ((Real.pi / 2) * |t|) := by
    exact cos_pi_two_bound w (by dsimp [w, s])
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
      have hx1 : 1 + |t| ≤ |t| + 3 := by linarith only []
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
      have hx : 1 ≤ |t| + 3 := by linarith only [ht]
      have hp : (|t| + 3) ^ 3 ≤ (|t| + 3) ^ 4 := pow_le_pow_right₀ hx (by norm_num : (3 : ℕ) ≤ 4)
      exact mul_le_mul_of_nonneg_left hp hconst0

/-- The requested theorem: uniform quartic growth on the strip `-1 ≤ σ ≤ 3`, `|t| ≥ 1`. -/
theorem zeta_strip_polyGrowth :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4 := by
  rcases zeta_left_poly with ⟨C1, hC1, hC1spec⟩
  rcases zeta_re_quarter_three_poly with ⟨C2, hC2, hC2spec⟩
  refine ⟨C1 + C2, add_pos hC1 hC2, ?_⟩
  intro σ t hσlo hσhi ht
  by_cases hσ : σ ≤ 1 / 4
  · have hb := hC1spec σ t hσlo hσ ht
    calc
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C1 * (|t| + 3) ^ 4 := hb
      _ ≤ (C1 + C2) * (|t| + 3) ^ 4 := by
        have hx0 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        nlinarith only [hC2, hx0]
  · have hσ2 : (1 / 4 : ℝ) ≤ σ := by linarith only [hσ]
    have hb := hC2spec σ t hσ2 hσhi ht
    calc
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C2 * (|t| + 3) ^ 4 := hb
      _ ≤ (C1 + C2) * (|t| + 3) ^ 4 := by
        have hx0 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        nlinarith only [hC1, hx0]

end Commons.NumberTheory.Zeta
