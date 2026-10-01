import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le

open Complex Filter Set
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.LSeries

/-!
# A `|t|^{1-σ} log |t|` bound for the Riemann zeta function on the critical strip

We prove that there is an absolute constant `C > 0` with

`‖ζ(σ + i t)‖ ≤ C · |t| ^ (1 - σ) · log (|t| + 2)`  for all `1/2 ≤ σ ≤ 1`, `|t| ≥ 1`.

The proof uses the Euler–Maclaurin decomposition of `ζ` on `0 < re s`, `s ≠ 1`
(from the commons, `zeta_eq_emN`)

`ζ(s) = ∑_{n=1}^{N} n^{-s} + N^{1-s}/(s-1) + ∑_{m} ( (N+m+1)^{-s}
        - ((N+m+1)^{1-s} - (N+m)^{1-s})/(1-s) )`

with the choice `N = ⌊|t|⌋ + 4 ≈ |t|`.  The point of the proof is the head
estimate: since `0 ≤ σ ≤ 1`,

`∑_{n ≤ N} n^{-σ} = ∑_{n ≤ N} n^{-1} · n^{1-σ} ≤ N^{1-σ} ∑_{n ≤ N} n^{-1}
   ≤ N^{1-σ} (1 + log N)`,

which upgrades the naive bound `N^{1-σ}/(1-σ)` (valid only for `σ` bounded away
from `1`) to a bound that is uniform on the whole strip.  The pole and tail
terms contribute `N^{1-σ}` and `2 N^{1-σ}` respectively, so
`‖ζ(s)‖ ≤ N^{1-σ}(4 + log N)`, and replacing `N` by `|t|` gives the claim.
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

/-- `‖σ + t·I‖ ≤ σ + |t|` for `σ ≥ 0`. -/
private lemma norm_add_mul_I_le (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + |t| := by
  calc
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = σ + |t| := by
      have h1 : ‖(σ : ℂ)‖ = |σ| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(t : ℂ) * Complex.I‖ = |t| := by
        rw [norm_mul, Complex.norm_I, mul_one]
        rw [Complex.norm_real, Real.norm_eq_abs]
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

/-- The Euler–Maclaurin tail estimate (imported as `emTerm_tsum_le`). -/
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

/-! ### The improved head estimate -/

/-- **The head estimate.**  For `σ ≤ 1` and `N ≥ 1`,
`∑_{n ≤ N} n^{-σ} ≤ N^{1-σ} (1 + log N)`.
The point is that the factor `N^{1-σ}` is paired with only a *logarithmic*
harmonic sum rather than the divergent `(1-σ)^{-1}`. -/
private lemma head_sum_le_improved (N : ℕ) (hN : 1 ≤ N) {σ : ℝ}
    (hσ1 : σ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
      ≤ ((N : ℝ)) ^ (1 - σ) * (1 + Real.log N) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      ((n : ℕ) : ℝ) ^ (-σ) ≤ ((N : ℝ)) ^ (1 - σ) * (((n : ℕ) : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hle : ((n : ℝ)) ≤ (N : ℝ) := by exact_mod_cast hnN
    have hexp : (0 : ℝ) ≤ 1 - σ := sub_nonneg.mpr hσ1
    have hpow : ((n : ℝ)) ^ (1 - σ) ≤ ((N : ℝ)) ^ (1 - σ) :=
      Real.rpow_le_rpow (le_of_lt hnpos) hle hexp
    have hdecomp : ((n : ℝ)) ^ (-σ) = ((n : ℝ)) ^ (-1 : ℝ) * ((n : ℝ)) ^ (1 - σ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    rw [hdecomp, Real.rpow_neg_one]
    calc (n : ℝ)⁻¹ * (n : ℝ) ^ (1 - σ) ≤ (n : ℝ)⁻¹ * (N : ℝ) ^ (1 - σ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (N : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by ring
  calc (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
      ≤ ∑ n ∈ Finset.Icc 1 N, ((N : ℝ)) ^ (1 - σ) * (((n : ℕ) : ℝ))⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = ((N : ℝ)) ^ (1 - σ) * ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ ((N : ℝ)) ^ (1 - σ) * (1 + Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt hN0) _)
        have hcast : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          rw [harmonic_eq_sum_Icc]; push_cast; rfl
        have h2 : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
        rw [← hcast]; exact h2

/-! ### The Euler–Maclaurin bound on the strip -/

/-- The Euler–Maclaurin bound on the strip: for `1/2 ≤ σ ≤ 1`, `|t| ≥ 1`, `N ≥ |t| + 3`,
`‖ζ(σ + i t)‖ ≤ N^{1-σ} (4 + log N)`. -/
private lemma zeta_em_bound_fractional {σ t : ℝ} (hσ12 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 ≤ |t|) (N : ℕ) (hN1 : 1 ≤ N) (hNt : |t| + 3 ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((N : ℝ)) ^ (1 - σ) * (4 + Real.log N) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hσ0 : 0 < σ := by linarith
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hsne : s ≠ 1 := by
    intro h
    have hti : t = 0 := by
      have h0 : s.im = 0 := by rw [h]; simp
      rw [hsim] at h0; exact h0
    have habs : |t| = 0 := by rw [hti]; simp
    linarith
  have ht' : 1 ≤ |s.im| := by rw [hsim]; exact ht
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0le : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN0
  let H : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))
  let M : ℂ := ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
  let T : ℂ := emTail N s
  have hid : riemannZeta s = H + M + T := by
    have h := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hsne N hN1
    rw [h]
    simp only [H, M, T, emTail]
  have hhead : ‖H‖ ≤ ((N : ℝ)) ^ (1 - σ) * (1 + Real.log N) := by
    have h1 : ‖H‖ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) := by
      have h := norm_head_le N s
      simpa [H, hsre] using h
    have h2 := head_sum_le_improved N hN1 hσ1
    linarith
  have hpole : ‖M‖ ≤ ((N : ℝ)) ^ (1 - σ) := by
    have h := pole_norm_le s ht' N hN1
    simpa [M, hsre] using h
  have htail : ‖T‖ ≤ 2 * ((N : ℝ)) ^ (1 - σ) := by
    have h := em_tail_norm_le s hs0 hsne N hN1
    have hsnorm : ‖s‖ ≤ (N : ℝ) := by
      have h1 : ‖s‖ ≤ σ + |t| := by
        simpa [hs] using norm_add_mul_I_le σ t (le_of_lt hσ0)
      have h2 : σ + |t| ≤ (N : ℝ) := by linarith
      linarith
    have hratio : ‖s‖ / s.re ≤ 2 * (N : ℝ) := by
      have h1 : ‖s‖ / s.re ≤ (N : ℝ) / σ := by
        rw [hsre]
        exact div_le_div_of_nonneg_right hsnorm (le_of_lt hσ0)
      have h2 : (N : ℝ) / σ ≤ 2 * (N : ℝ) := by
        rw [div_le_iff₀ hσ0]
        nlinarith [hN0, hσ12]
      linarith
    have hrpow : ((N : ℝ)) ^ (-s.re) = ((N : ℝ)) ^ (-σ) := by rw [hsre]
    have hmulN : (N : ℝ) * (N : ℝ) ^ (-σ) = (N : ℝ) ^ (1 - σ) := by
      rw [show (1 : ℝ) - σ = 1 + (-σ) by ring, Real.rpow_add hN0, Real.rpow_one]
    calc
      ‖T‖ ≤ (‖s‖ / s.re) * (((N : ℝ)) ^ (-s.re)) := by simpa [T] using h
      _ ≤ (2 * (N : ℝ)) * (((N : ℝ)) ^ (-σ)) := by
          rw [hrpow]
          exact mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hN0le _)
      _ = 2 * ((N : ℝ) * (N : ℝ) ^ (-σ)) := by ring
      _ = 2 * ((N : ℝ)) ^ (1 - σ) := by rw [hmulN]
  have htri : ‖H + M + T‖ ≤ ‖H‖ + ‖M‖ + ‖T‖ := by
    calc
      ‖H + M + T‖ ≤ ‖H + M‖ + ‖T‖ := norm_add_le (H + M) T
      _ ≤ (‖H‖ + ‖M‖) + ‖T‖ := add_le_add (norm_add_le H M) le_rfl
  calc
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = ‖riemannZeta s‖ := by rw [hs]
    _ = ‖H + M + T‖ := by rw [hid]
    _ ≤ ‖H‖ + ‖M‖ + ‖T‖ := htri
    _ ≤ ((N : ℝ)) ^ (1 - σ) * (1 + Real.log N) + ((N : ℝ)) ^ (1 - σ)
          + 2 * ((N : ℝ)) ^ (1 - σ) := by linarith [hhead, hpole, htail]
    _ = ((N : ℝ)) ^ (1 - σ) * (4 + Real.log N) := by ring

/-! ### The main theorem -/

theorem exists_bound_norm_riemannZeta_fractional :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1 - σ) * Real.log (|t| + 2) := by
  refine ⟨30, by norm_num, ?_⟩
  intro σ t hσ12 hσ1 ht
  set N : ℕ := Nat.floor |t| + 4 with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; omega
  have hNge : |t| + 3 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one |t|
    rw [hNdef]
    push_cast
    linarith
  have hNle : (N : ℝ) ≤ 5 * |t| := by
    have hfl : ((Nat.floor |t| : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    rw [hNdef]
    push_cast
    linarith
  have hb := zeta_em_bound_fractional hσ12 hσ1 ht N hN1 hNge
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hexp : 0 ≤ 1 - σ := by linarith
  have hNpow : ((N : ℝ)) ^ (1 - σ) ≤ 5 * |t| ^ (1 - σ) := by
    calc
      ((N : ℝ)) ^ (1 - σ) ≤ (5 * |t|) ^ (1 - σ) :=
        Real.rpow_le_rpow (le_of_lt hN0) hNle hexp
      _ = 5 ^ (1 - σ) * |t| ^ (1 - σ) := Real.mul_rpow (by norm_num) (le_of_lt ht0)
      _ ≤ 5 * |t| ^ (1 - σ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht0.le _)
          calc
            5 ^ (1 - σ) ≤ 5 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 5 := Real.rpow_one 5
  have hNle2 : (N : ℝ) ≤ 2 * (|t| + 2) := by
    have hfl : ((Nat.floor |t| : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    rw [hNdef]
    push_cast
    linarith [abs_nonneg t]
  have hlogN : Real.log ((N : ℝ)) ≤ 2 * Real.log (|t| + 2) := by
    calc
      Real.log ((N : ℝ)) ≤ Real.log (2 * (|t| + 2)) := Real.log_le_log hN0 hNle2
      _ = Real.log 2 + Real.log (|t| + 2) :=
          Real.log_mul (by norm_num) (by positivity)
      _ ≤ Real.log (|t| + 2) + Real.log (|t| + 2) := by
          have h : Real.log 2 ≤ Real.log (|t| + 2) :=
            Real.log_le_log (by norm_num) (by linarith)
          linarith
      _ = 2 * Real.log (|t| + 2) := by ring
  have hlog1 : (1 : ℝ) ≤ Real.log (|t| + 2) := by
    have h3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hle : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have hlogN0 : (0 : ℝ) ≤ Real.log ((N : ℝ)) := Real.log_nonneg (by exact_mod_cast hN1)
  have hcomb : 4 + Real.log ((N : ℝ)) ≤ 6 * Real.log (|t| + 2) := by
    linarith [hlogN, hlog1]
  calc
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ((N : ℝ)) ^ (1 - σ) * (4 + Real.log N) := hb
    _ ≤ (5 * |t| ^ (1 - σ)) * (6 * Real.log (|t| + 2)) :=
        mul_le_mul hNpow hcomb (by linarith) (mul_nonneg (by norm_num) (Real.rpow_nonneg ht0.le _))
    _ = 30 * |t| ^ (1 - σ) * Real.log (|t| + 2) := by ring

end Commons.NumberTheory.LSeries
