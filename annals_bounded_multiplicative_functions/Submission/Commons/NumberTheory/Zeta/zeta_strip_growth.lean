import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.NumberTheory.Zeta.zeta_strip_glue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
open Complex Filter Set
open scoped Topology BigOperators
noncomputable section
namespace Commons.NumberTheory.Zeta

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

/-- Main reduction: `‖ζ(σ+I t)‖ ≤ A(N) + (1 + 1/σ)·N^{1-σ}`. -/
private lemma zeta_bound_emN {σ t : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (ht : 1 ≤ |t|)
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
      simpa [s] using norm_add_mul_I_le σ t (le_of_lt hσ0)
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



theorem zeta_strip_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (1 + 1 / δ) * (|t| + 3) ^ (1 / 2 - δ / 2) := by
  refine ⟨1000000, by norm_num, ?_⟩
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
  have hb := zeta_bound_emN (σ := σ) (t := t) hσ0 hσhi ht N hN1 hNge
  have hg := zeta_strip_glue δ σ t N hδ0 hδ1 hσlo hσhi ht hNge hNle
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℕ) : ℝ) ^ (1 - σ) := hb
    _ ≤ 1000000 * (1 + 1 / δ) * (|t| + 3) ^ (1 / 2 - δ / 2) := hg

end Commons.NumberTheory.Zeta
