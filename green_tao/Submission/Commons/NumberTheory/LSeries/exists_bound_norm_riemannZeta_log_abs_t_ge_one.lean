import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le

open Complex Filter Set
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.LSeries

/-!
# A logarithmic bound for the Riemann zeta function on `re s ≥ 1`

We prove that there is an absolute constant `C > 0` with

`‖ζ(σ + i t)‖ ≤ C · log (|t| + 2)`  for all `σ ≥ 1` and `|t| ≥ 1`.

The proof uses the Euler–Maclaurin decomposition of `ζ` (from the commons,
`zeta_eq_emN`)

`ζ(s) = ∑_{n=1}^{N} n^{-s} + N^{1-s}/(s-1) + ∑_{m} ( (N+m+1)^{-s}
        - ((N+m+1)^{1-s} - (N+m)^{1-s})/(1-s) )`

valid on `0 < re s`, `s ≠ 1`.  Choosing `N ≈ |t|`:

* the head `∑_{n ≤ N} n^{-s}` is bounded by `∑_{n ≤ N} n^{-σ} ≤ ∑_{n ≤ N} 1/n ≤ 1 + log N`
  (because `σ ≥ 1`), which produces the logarithmic growth;
* the pole term is `≤ N^{1-σ} ≤ 1`;
* the tail is bounded by `(‖s‖/σ) N^{-σ ≤ 2}` using `‖s‖ ≤ σ + |t|`, `N ≥ |t|`, `σ ≥ 1`.
-/

/-! ### Elementary norm estimates -/

/-- `‖n^{-s}‖ = n^{-re s}` for a positive natural base. -/
private lemma norm_nat_cpow_neg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(((n : ℕ) : ℂ) ^ (-s))‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)]
  rw [Complex.neg_re]

/-- The triangle inequality for the finite Euler–Maclaurin sum. -/
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

/-- `‖σ + i t‖ ≤ σ + |t|` for `σ ≥ 0`. -/
private lemma norm_add_mul_I_le (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ σ + |t| := by
  calc
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖
        ≤ ‖(σ : ℂ)‖ + ‖(Complex.I * (t : ℂ))‖ := norm_add_le _ _
    _ = σ + |t| := by
      have h1 : ‖(σ : ℂ)‖ = |σ| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(Complex.I * (t : ℂ))‖ = |t| := by
        rw [norm_mul, Complex.norm_I]
        rw [Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [h1, h2, abs_of_nonneg hσ0]

/-- Bound on the pole term of the Euler–Maclaurin decomposition. -/
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
    have hcontra : |s.im| = 0 := by rw [hsi]; simp
    linarith
  have hnorm_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hsne
  have hden : 1 ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).im| ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
    have h2 : |(s - 1).im| = |s.im| := by simp
    linarith
  have hpow_nonneg : 0 ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := Real.rpow_nonneg hN0le _
  calc
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖
        = ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ / ‖s - 1‖ := by rw [norm_div]
    _ = ((N : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by rw [hnormN]
    _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [div_le_iff₀ hnorm_pos]
      calc
        ((N : ℕ) : ℝ) ^ (1 - s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) * 1 := by ring
        _ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) * ‖s - 1‖ :=
            mul_le_mul_of_nonneg_left hden hpow_nonneg

/-! ### The Euler–Maclaurin tail estimate (imported as `emTerm_tsum_le`) -/

private def emTail (N : ℕ) (s : ℂ) : ℂ :=
  ∑' m : ℕ,
    ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
      (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))

private lemma em_tail_norm_le (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ)
    (hN : 1 ≤ N) :
    ‖emTail N s‖ ≤ (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := by
  have htel := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN s hs0 hs1
  have hnormS : Summable (fun m : ℕ =>
      ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖) :=
    htel.1.norm
  calc
    ‖emTail N s‖
        ≤ ∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
          norm_tsum_le_tsum_norm hnormS
    _ ≤ (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := htel.2

/-! ### The harmonic bound on the head -/

private lemma head_sum_le (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ 1 + Real.log N := by
  have hcast : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  have h1 : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ (harmonic N : ℝ) := by
    rw [hcast]
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hb : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    calc ((n : ℕ) : ℝ) ^ (-σ) ≤ ((n : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb (by linarith)
      _ = ((n : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
  have h2 : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  linarith

/-! ### The reduction: Euler–Maclaurin bound for `σ ≥ 1` -/

private lemma zeta_em_bound {σ t : ℝ} (hσ : 1 ≤ σ) (ht : 1 ≤ |t|)
    (N : ℕ) (hN : 1 ≤ N) (hNt : |t| ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + 1 + 2 := by
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hσ0 : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have ht' : 1 ≤ |s.im| := by rw [hsim]; exact ht
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s ≠ 1 := by
    intro h
    have hsi : s.im = 0 := by simpa using congrArg Complex.im h
    have ht0 : t = 0 := by simpa [hsim] using hsi
    have hzero : |t| = 0 := by rw [ht0]; simp
    linarith
  let H : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))
  let M : ℂ := ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
  let T : ℂ := emTail N s
  have hid : riemannZeta s = H + M + T := by
    have h := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hs1 N hN
    rw [h]
    simp only [H, M, T, emTail]
  have hhead : ‖H‖ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) := by
    have h := norm_head_le N s
    simpa [H, hsre] using h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpole : ‖M‖ ≤ 1 := by
    have h := pole_norm_le s ht' N hN
    calc
      ‖M‖ ≤ ((N : ℕ) : ℝ) ^ (1 - s.re) := h
      _ = ((N : ℕ) : ℝ) ^ (1 - σ) := by rw [hsre]
      _ ≤ ((N : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ = 1 := Real.rpow_zero _
  have htail : ‖T‖ ≤ 2 := by
    have h := em_tail_norm_le s hs0 hs1 N hN
    have htre : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
    have hsnorm : ‖s‖ ≤ σ + |t| := by
      simpa [hs] using norm_add_mul_I_le σ t (le_of_lt hσ0)
    have hratio : ‖s‖ / s.re ≤ 1 + |t| := by
      rw [hsre]
      calc
        ‖s‖ / σ ≤ (σ + |t|) / σ := div_le_div_of_nonneg_right hsnorm hσ0.le
        _ = 1 + |t| / σ := by rw [add_div, div_self (ne_of_gt hσ0)]
        _ ≤ 1 + |t| := by
            have hle : |t| / σ ≤ |t| := by
              rw [div_le_iff₀ hσ0]
              nlinarith [htre, hσ]
            linarith
    have hrpow : ((N : ℕ) : ℝ) ^ (-s.re) ≤ 1 / |t| := by
      have h1 : ((N : ℕ) : ℝ) ^ (-s.re) ≤ ((N : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by rw [hsre]; linarith)
      rw [Real.rpow_neg_one] at h1
      calc
        ((N : ℕ) : ℝ) ^ (-s.re) ≤ ((N : ℕ) : ℝ)⁻¹ := h1
        _ = 1 / (N : ℝ) := by rw [one_div]
        _ ≤ 1 / |t| := one_div_le_one_div_of_le htre hNt
    calc
      ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) := h
      _ ≤ (1 + |t|) * (1 / |t|) :=
          mul_le_mul hratio hrpow (Real.rpow_nonneg hNpos.le _) (by positivity)
      _ = (1 + |t|) / |t| := by rw [mul_one_div]
      _ ≤ 2 := by
          rw [div_le_iff₀ htre]
          linarith
  have htri : ‖H + M + T‖ ≤ ‖H‖ + ‖M‖ + ‖T‖ := by
    calc
      ‖H + M + T‖ ≤ ‖H + M‖ + ‖T‖ := norm_add_le (H + M) T
      _ ≤ (‖H‖ + ‖M‖) + ‖T‖ := add_le_add (norm_add_le H M) le_rfl
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ = ‖riemannZeta s‖ := by rw [hs]
    _ = ‖H + M + T‖ := by rw [hid]
    _ ≤ ‖H‖ + ‖M‖ + ‖T‖ := htri
    _ ≤ (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + 1 + 2 :=
        add_le_add (add_le_add hhead hpole) htail

/-! ### The main theorem -/

theorem exists_bound_norm_riemannZeta_log_abs_t_ge_one :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 ≤ σ → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 2) := by
  refine ⟨5, by norm_num, ?_⟩
  intro σ t hσ ht
  rw [mul_comm (t : ℂ) Complex.I]
  set N : ℕ := Nat.floor |t| + 1 with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; omega
  have hNge : |t| ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one |t|
    rw [hNdef]
    push_cast
    linarith
  have hNle : (N : ℝ) ≤ |t| + 2 := by
    have h := Nat.floor_le (abs_nonneg t)
    rw [hNdef]
    push_cast
    linarith
  have hb := zeta_em_bound hσ ht N hN1 hNge
  have hhead := head_sum_le N hσ
  have hlogle : Real.log (N : ℝ) ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by positivity) hNle
  have hlogge : (1 : ℝ) ≤ Real.log (|t| + 2) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hle : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖
        ≤ (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + 1 + 2 := hb
    _ ≤ (1 + Real.log (N : ℝ)) + 1 + 2 := by linarith [hhead]
    _ ≤ Real.log (|t| + 2) + 4 := by linarith [hlogle]
    _ ≤ 5 * Real.log (|t| + 2) := by linarith [hlogge]

end Commons.NumberTheory.LSeries