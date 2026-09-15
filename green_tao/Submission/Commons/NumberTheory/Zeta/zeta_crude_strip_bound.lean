import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth

/-!
# A crude strip bound for the Riemann zeta function

We prove that for `1/2 ≤ σ ≤ 1` and `t ≥ 3` one has, whenever `σ ≤ 15/16` or `t ≤ 10^100`,

  `‖ζ(σ + i t)‖ ≤ A · t^{4 (1-σ)^{3/2}} · (log t)^{2/3}`

with a universal constant `A`.

Two regimes are used.

* For `σ ≤ 15/16` we use the Euler–Maclaurin expansion
  `ζ(s) = ∑_{n ≤ N} n^{-s} + N^{1-s}/(s-1) + tail` with `N ≈ t`.
  The partial sum is bounded by
  `∑_{n ≤ N} n^{-σ} ≤ (1 + (1-σ)^{-1}) N^{1-σ}` (integral comparison), the pole term by
  `N^{1-σ}` and the tail by `N^{1-σ}/σ`, so that altogether
  `‖ζ(σ+it)‖ ≤ 10 (1-σ)^{-1} (t+3)^{1-σ}`.
  Since `1 - σ ≥ 1/16` in this range we have `1 - σ ≤ 4 (1-σ)^{3/2}`, and the claim follows
  from `t ≥ 3`.

* For `t ≤ 10^100` we appeal to the (explicitly bounded) polynomial strip bound
  `‖ζ(σ+it)‖ ≤ C (|t|+3)^4` and absorb the resulting constant `C (10^100+3)^4` into `A`;
  the right hand side is at least `A` because `t^{4(1-σ)^{3/2}} ≥ 1` and `(log t)^{2/3} ≥ 1`.
-/

open Complex Filter Set
open scoped Real Topology BigOperators
noncomputable section
namespace Commons.NumberTheory.Zeta

/-! ## The integral-comparison bound for `∑ n^{-σ}` -/

private lemma sum_Icc1_eq_sum_range_succ (X : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, f n) = ∑ m ∈ Finset.range X, f (m + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
      by_cases h0 : X = 0
      · subst X
        simp
      · have hX : 1 ≤ X := by omega
        rw [Finset.sum_range_succ]
        rw [Finset.sum_Icc_succ_top (a := 1) (b := X) (by omega)]
        rw [ih]

private lemma range_eq_insert_Ico (X : ℕ) (hX : 1 ≤ X) :
    Finset.range X = insert 0 (Finset.Ico 1 X) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_insert]
  constructor <;> omega

/-- Integral comparison: for `0 < σ < 1` and `1 ≤ X`,
`∑_{n ≤ X} n^{-σ} ≤ (1 + (1-σ)^{-1}) X^{1-σ}`. -/
private lemma sum_rpow_neg_le (X : ℕ) (hX : 1 ≤ X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-σ)) ≤ (1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := by
  let f : ℝ → ℝ := fun x => x ^ (-σ)
  have hanti0 : AntitoneOn f (Set.Ioi (0 : ℝ)) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)
  have hanti : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) (X : ℝ)) := hanti0.mono (by
    intro x hx
    have h1 : (1 : ℝ) ≤ x := by exact_mod_cast (Set.mem_Icc.mp hx).1
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one h1))
  have hXle : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have h_int : (∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), x ^ (-σ)) =
      ((X : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    have hne : -σ ≠ (-1 : ℝ) := by linarith
    have hnot0 : 0 ∉ Set.uIcc (((1 : ℕ) : ℝ)) (X : ℝ) := by
      intro hx
      have hx' : (0 : ℝ) ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
        simpa [Set.uIcc_of_le hXle] using hx
      have h01 : (1 : ℝ) ≤ (0 : ℝ) := (Set.mem_Icc.mp hx').1
      linarith
    have hint := integral_rpow (r := -σ) (a := (((1 : ℕ) : ℝ))) (b := (X : ℝ))
      (Or.inr ⟨hne, hnot0⟩)
    rw [hint]
    have hD : -σ + 1 = 1 - σ := by ring
    rw [hD]
    simp
  have h_int_le : (∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), f x) ≤
      (1 - σ)⁻¹ * (X : ℝ) ^ (1 - σ) := by
    rw [h_int]
    have hpos : 0 < 1 - σ := sub_pos.mpr hσ1
    calc
      ((X : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ (X : ℝ) ^ (1 - σ) / (1 - σ) := by
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hpos)
      _ = (1 - σ)⁻¹ * (X : ℝ) ^ (1 - σ) := by
            field_simp [ne_of_gt hpos]
  have hint_b : (∑ i ∈ Finset.Ico 1 X, f ((i + 1 : ℕ) : ℝ)) ≤
      ∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), f x := by
    exact AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := X) hX hanti
  have hge1 : (1 : ℝ) ≤ (X : ℝ) ^ (1 - σ) := by
    exact Real.one_le_rpow hXle (by linarith : 0 ≤ 1 - σ)
  calc
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-σ))
        = ∑ m ∈ Finset.range X, f ((m + 1 : ℕ) : ℝ) := by
            rw [sum_Icc1_eq_sum_range_succ]
    _ = f 1 + ∑ i ∈ Finset.Ico 1 X, f ((i + 1 : ℕ) : ℝ) := by
            rw [range_eq_insert_Ico X hX, Finset.sum_insert]
            · simp
            · rw [Finset.mem_Ico]; omega
    _ ≤ f 1 + ∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), f x := by
            exact add_le_add le_rfl hint_b
    _ ≤ f 1 + (1 - σ)⁻¹ * (X : ℝ) ^ (1 - σ) := by
            exact add_le_add le_rfl h_int_le
    _ ≤ (1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := by
            have hf1 : f 1 = 1 := by
              dsimp [f]
              simp
            rw [hf1]
            linarith

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


/-- Euler–Maclaurin bound on the strip `1/2 ≤ σ < 1`:
`‖ζ(σ+i t)‖ ≤ 10 (1-σ)^{-1} (t+3)^{1-σ}` for `t ≥ 3`. -/
private lemma zeta_conv_bound (σ t : ℝ) (hσlo : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ < 1) (ht : 3 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      10 * (1 / (1 - σ)) * (t + 3) ^ (1 - σ) := by
  have hσ0 : 0 < σ := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have habs : |t| = t := abs_of_nonneg ht0
  set N : ℕ := Nat.floor t + 4 with hNdef
  have hfloor_lt : t < ((Nat.floor t : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hfloor_le : ((Nat.floor t : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hNge : |t| + 3 ≤ (N : ℝ) := by
    rw [hNdef, Nat.cast_add, Nat.cast_ofNat, habs]
    linarith
  have hNle : (N : ℝ) ≤ t + 4 := by
    rw [hNdef, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hN1 : 1 ≤ N := by
    rw [hNdef]; omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h1σ : 0 < 1 - σ := by linarith
  have hb := zeta_bound_emN (σ := σ) (t := t) hσ0 (by linarith : σ ≤ 2)
    (by rw [habs]; linarith : 1 ≤ |t|) N hN1 hNge
  set P : ℝ := (N : ℝ) ^ (1 - σ) with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNpos.le _
  have hsum := sum_rpow_neg_le N hN1 hσ0 hσ1
  have hsum' : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ (1 + (1 - σ)⁻¹) * P := by
    rw [hPdef]; exact hsum
  have hinv1 : (1 : ℝ) ≤ (1 - σ)⁻¹ := by
    rw [one_le_inv₀ h1σ]
    linarith
  have hcoef2 : 1 + 1 / σ ≤ 3 := by
    have h : 1 / σ ≤ 2 := by
      rw [div_le_iff₀ hσ0]
      linarith
    linarith
  have htail : (1 + 1 / σ) * P ≤ 3 * P :=
    mul_le_mul_of_nonneg_right hcoef2 hP0
  have hPN : P ≤ 2 * (t + 3) ^ (1 - σ) := by
    have h1 : (N : ℝ) ≤ 2 * (t + 3) := by linarith
    calc P = (N : ℝ) ^ (1 - σ) := hPdef
      _ ≤ (2 * (t + 3)) ^ (1 - σ) := Real.rpow_le_rpow hNpos.le h1 (le_of_lt h1σ)
      _ = 2 ^ (1 - σ) * (t + 3) ^ (1 - σ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * (t + 3) ^ (1 - σ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _)
          have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (show (1 : ℝ) - σ ≤ 1 by linarith)
          simpa using h2
  have hX0 : 0 ≤ (t + 3) ^ (1 - σ) := Real.rpow_nonneg (by linarith) _
  calc ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖
      ≤ (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * P := hb
    _ ≤ (1 + (1 - σ)⁻¹) * P + 3 * P := add_le_add hsum' htail
    _ = (4 + (1 - σ)⁻¹) * P := by ring
    _ ≤ 5 * (1 - σ)⁻¹ * P := by
        refine mul_le_mul_of_nonneg_right ?_ hP0
        linarith
    _ ≤ 5 * (1 - σ)⁻¹ * (2 * (t + 3) ^ (1 - σ)) := by
        refine mul_le_mul_of_nonneg_left hPN ?_
        positivity
    _ = 10 * (1 / (1 - σ)) * (t + 3) ^ (1 - σ) := by
        rw [one_div]
        ring


/-- Euler–Maclaurin strip bound, in existential form: on `1/2 ≤ σ < 1` and `t ≥ 3`,
`‖ζ(σ+i t)‖ ≤ C (1-σ)^{-1} (t+3)^{1-σ}`.  This is the standard "trivial" bound
`ζ(σ+i t) = O_σ(t^{1-σ})` with an explicit dependence on `1-σ`. -/
theorem zeta_strip_conv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, (1 / 2 : ℝ) ≤ σ → σ < 1 → 3 ≤ t →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (1 / (1 - σ)) * (t + 3) ^ (1 - σ) :=
  ⟨10, by norm_num, fun σ t hσlo hσ1 ht => zeta_conv_bound σ t hσlo hσ1 ht⟩

/-- **Crude strip bound.**  There is an absolute constant `A` with
`‖ζ(σ+i t)‖ ≤ A t^{4(1-σ)^{3/2}} (log t)^{2/3}` for `1/2 ≤ σ ≤ 1`, `t ≥ 3`, whenever
`σ ≤ 15/16` or `t ≤ 10^100`. -/
theorem zeta_crude_strip_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ 1 → 3 ≤ t →
      (σ ≤ 15 / 16 ∨ t ≤ (10 : ℝ) ^ 100) →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        A * t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) := by
  obtain ⟨C2, hC2pos, hC2spec⟩ := zeta_strip_polyGrowth
  refine ⟨max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1, by positivity, ?_⟩
  intro σ t hσlo hσhi ht hcond
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hx0 : 0 ≤ 1 - σ := by linarith
  have hexp0 : 0 ≤ 4 * (1 - σ) ^ (3 / 2 : ℝ) := by
    have h : 0 ≤ (1 - σ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx0 _
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have h3 : (1 : ℝ) < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht
    linarith
  have htp : 1 ≤ t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := Real.one_le_rpow ht1 hexp0
  have hlogp : 1 ≤ (Real.log t) ^ (2 / 3 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
  have hA0 : 0 ≤ max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1 := by positivity
  have hA384 : (384 : ℝ) ≤ max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1 := by
    have := le_max_left (384 : ℝ) (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4)
    linarith
  have hApoly : C2 * ((10 : ℝ) ^ 100 + 3) ^ 4 ≤
      max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1 := by
    have := le_max_right (384 : ℝ) (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4)
    linarith
  rcases hcond with hσle | ht100
  · -- Regime 1: `σ ≤ 15/16`, all `t ≥ 3`.
    have hσlt1 : σ < 1 := by linarith
    have hb := zeta_conv_bound σ t hσlo hσlt1 ht
    have hx16 : (1 / 16 : ℝ) ≤ 1 - σ := by linarith
    have hx1 : 1 - σ ≤ 1 := by linarith
    have h14 : ((1 / 16 : ℝ)) ^ (1 / 2 : ℝ) = 1 / 4 := by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, ← Real.rpow_natCast (1 / 4) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
    have hxhalf : (1 / 4 : ℝ) ≤ (1 - σ) ^ (1 / 2 : ℝ) := by
      calc (1 / 4 : ℝ) = ((1 / 16 : ℝ)) ^ (1 / 2 : ℝ) := h14.symm
        _ ≤ (1 - σ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hx16 (by norm_num)
    have hxpos : 0 < 1 - σ := by linarith
    have hexp1 : (1 - σ) ≤ 4 * (1 - σ) ^ (3 / 2 : ℝ) := by
      have hsplit : (1 - σ) ^ (3 / 2 : ℝ) = (1 - σ) * (1 - σ) ^ (1 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hxpos, Real.rpow_one]
      rw [hsplit]
      have h := mul_le_mul_of_nonneg_left hxhalf hx0
      nlinarith [h, hx0]
    have h1div : (1 / (1 - σ)) ≤ 16 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - σ)]
      linarith
    have h2 : (t + 3) ^ (1 - σ) ≤ (2 * t) ^ (1 - σ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) hx0
    have h3 : (2 * t) ^ (1 - σ) = 2 ^ (1 - σ) * t ^ (1 - σ) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h4 : (2 : ℝ) ^ (1 - σ) ≤ (2 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hx1
      simpa using h
    have h5 : t ^ (1 - σ) ≤ t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ht1 hexp1
    have hX1 : 0 ≤ (t + 3) ^ (1 - σ) := Real.rpow_nonneg (by linarith) _
    have hXt : 0 ≤ t ^ (1 - σ) := Real.rpow_nonneg ht0 _
    have htE : 0 ≤ t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := Real.rpow_nonneg ht0 _
    have hlg : 0 ≤ (Real.log t) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hlog1)) _
    calc ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖
        ≤ 10 * (1 / (1 - σ)) * (t + 3) ^ (1 - σ) := hb
      _ ≤ 10 * 16 * (t + 3) ^ (1 - σ) := by
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1div (by norm_num : (0 : ℝ) ≤ 10)) hX1
          linarith [h]
      _ ≤ 160 * (2 * t) ^ (1 - σ) := by
          have h := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 160)
          linarith [h]
      _ = 160 * (2 ^ (1 - σ) * t ^ (1 - σ)) := by rw [h3]
      _ ≤ 160 * (2 * t ^ (1 - σ)) := by
          have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hXt)
            (by norm_num : (0 : ℝ) ≤ 160)
          linarith [h]
      _ ≤ 320 * t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := by
          have h := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 160)
          linarith [h]
      _ ≤ 320 * t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) := by
          calc 320 * t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ))
              = 320 * t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * 1 := by ring
            _ ≤ 320 * t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) :=
                mul_le_mul_of_nonneg_left hlogp (by positivity)
      _ ≤ (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
            t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) := by
          have hE0 : 0 ≤ t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) :=
            mul_nonneg htE hlg
          have h1 : 320 * (t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ)) ≤
              384 * (t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hE0
          have h2 : 384 * (t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ)) ≤
              (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
                (t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hA384 hE0
          linarith [h1, h2]
  · -- Regime 2: `t ≤ 10^100` (any `σ ∈ [1/2,1]`).
    have habs : |t| = t := abs_of_nonneg ht0
    have hb := hC2spec σ t (by linarith) (by linarith) (by rw [habs]; linarith)
    rw [habs] at hb
    have hle : C2 * (t + 3) ^ 4 ≤ C2 * ((10 : ℝ) ^ 100 + 3) ^ 4 := by
      refine mul_le_mul_of_nonneg_left ?_ hC2pos.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) 4
    have hstep1 : max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1 ≤
        (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
          t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := by
      calc max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1
          = (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) * 1 := by ring
        _ ≤ (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
              t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left htp hA0
    have hstep2 : (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
          t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) ≤
        (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
          t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) := by
      calc (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
            t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ))
          = (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
              t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * 1 := by ring
        _ ≤ (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
              t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hlogp (by positivity)
    calc ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖
        ≤ C2 * (t + 3) ^ 4 := hb
      _ ≤ C2 * ((10 : ℝ) ^ 100 + 3) ^ 4 := hle
      _ ≤ max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1 := hApoly
      _ ≤ (max 384 (C2 * ((10 : ℝ) ^ 100 + 3) ^ 4) + 1) *
            t ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) :=
          le_trans hstep1 hstep2

end Commons.NumberTheory.Zeta
