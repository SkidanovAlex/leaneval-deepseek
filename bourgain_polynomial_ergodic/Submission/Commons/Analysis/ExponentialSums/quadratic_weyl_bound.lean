import Mathlib
import Submission.Commons.Analysis.ExponentialSums.weyl_ineq_two
import Submission.Commons.Analysis.ExponentialSums.quadratic_differencing_counting

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators Topology

set_option maxHeartbeats 0

/-!
# Weyl's inequality for quadratic exponential sums

We prove the classical `k = 2` Weyl bound in the normalisation used by the circle method:

`|(1/N) ∑_{n<N} e(α n²)| ≲_ε N^ε (1/q + 1/N + q/N²)^{1/2}`  whenever
`|α − a/q| ≤ 1/q²` and `gcd a q = 1`.

The proof combines

* Weyl differencing, `weyl_ineq_two` (commons), which bounds the square of a quadratic
  Weyl sum by `M + 2 ∑_{h ≤ M} wcf M ‖2βh‖`, and
* the counting estimate `quadratic_differencing_counting` (commons), which controls that
  sum in terms of `M²/q + M + q`.

These are applied to *windows* of length `M ≤ q`; for `N > q` the sum is split into consecutive
blocks of length `q`, glued together by the telescoping lemma `quad_weyl_blocks`.
-/

/-- The standard additive character `e(x) = exp(2πi x)`. -/
noncomputable def quadChar (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma quadChar_norm (x : ℝ) : ‖quadChar x‖ = 1 := by
  rw [quadChar]; simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

lemma quadChar_add (x y : ℝ) : quadChar (x + y) = quadChar x * quadChar y := by
  rw [quadChar, quadChar, quadChar, ← Complex.exp_add]; congr 1; push_cast; ring

/-- The two spellings of `e(x)` used above and in the target statement agree. -/
lemma quadChar_exp_form (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = quadChar x := by
  rw [quadChar]; congr 1; push_cast; ring

/-! ## The Weyl block (window) bound -/

/-- Weyl's bound for a window of length `M ≤ q` (with arbitrary linear phase `γ`):
`‖∑_{m ≤ M} e(γ m + β m²)‖ ≤ C M^e (q + M)^{1/2}` whenever `|β − a/q| ≤ 1/q²`. -/
lemma quad_weyl_phase_block {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (γ β : ℝ) (a : ℤ) (q : ℕ),
      1 ≤ M → M ≤ q → Int.gcd a (q : ℤ) = 1 →
      |β - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
      ‖∑ m ∈ Finset.Icc 1 M, quadChar (γ * (m : ℝ) + β * (m : ℝ) ^ 2)‖
        ≤ C * (M : ℝ) ^ e * ((q : ℝ) + (M : ℝ)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨C1, hC1pos, hC1⟩ := quadratic_differencing_counting (e := 2 * e) (by positivity)
  refine ⟨(1 + 6 * C1) ^ ((1 : ℝ) / 2), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro M γ β a q hM hMq ha hβ
  have hq1 : 1 ≤ q := le_trans hM hMq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMqR : (M : ℝ) ≤ (q : ℝ) := by exact_mod_cast hMq
  -- transfer the approximation hypothesis from `1/q²` to `1/(qM)`
  have hβ' : ‖β - (a : ℝ) / (q : ℝ)‖ ≤ 1 / ((q : ℝ) * (M : ℝ)) := by
    rw [Real.norm_eq_abs]
    refine le_trans hβ ?_
    apply one_div_le_one_div_of_le (by positivity)
    calc (q : ℝ) * (M : ℝ) ≤ (q : ℝ) * (q : ℝ) := mul_le_mul_of_nonneg_left hMqR hqpos.le
      _ = (q : ℝ) ^ 2 := by ring
  have hw := weyl_ineq_two M hM γ β
  have hcnt := hC1 M hM β a q (by omega) ha hβ'
  have hM21 : (1 : ℝ) ≤ (M : ℝ) ^ (2 * e) := Real.one_le_rpow hM1R (by positivity)
  have hsum_eq : (∑ m ∈ Finset.Icc 1 M,
        Complex.exp (((2 * Real.pi * (γ * (m : ℝ) + β * (m : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I))
      = ∑ m ∈ Finset.Icc 1 M, quadChar (γ * (m : ℝ) + β * (m : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl; intro m _
    rw [quadChar]
  have hkey : ‖∑ m ∈ Finset.Icc 1 M, quadChar (γ * (m : ℝ) + β * (m : ℝ) ^ 2)‖ ^ 2
      ≤ (1 + 6 * C1) * (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ)) := by
    rw [← hsum_eq]
    have h1 : (M : ℝ) ≤ (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ)) := by
      have ha1 : (M : ℝ) ≤ (M : ℝ) ^ (2 * e) * (M : ℝ) := by
        calc (M : ℝ) = 1 * (M : ℝ) := by ring
          _ ≤ (M : ℝ) ^ (2 * e) * (M : ℝ) := mul_le_mul_of_nonneg_right hM21 hMR.le
      have hb1 : (M : ℝ) ^ (2 * e) * (M : ℝ) ≤ (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith [hqpos.le]) (by positivity)
      linarith
    have hP : (M : ℝ) ^ 2 / (q : ℝ) + (M : ℝ) + (q : ℝ) ≤ 3 * ((q : ℝ) + (M : ℝ)) := by
      have hdiv : (M : ℝ) ^ 2 / (q : ℝ) ≤ (M : ℝ) := by
        rw [div_le_iff₀ hqpos]
        nlinarith [hMqR, hMR.le]
      linarith
    calc ‖∑ m ∈ Finset.Icc 1 M,
            Complex.exp (((2 * Real.pi * (γ * (m : ℝ) + β * (m : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I)‖ ^ 2
        ≤ (M : ℝ) + 2 * (∑ h ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
             else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ))))) := hw
      _ ≤ (M : ℝ) + 2 * (C1 * (M : ℝ) ^ (2 * e) * ((M : ℝ) ^ 2 / (q : ℝ) + (M : ℝ) + (q : ℝ))) := by
            linarith [hcnt]
      _ ≤ (M : ℝ) + 2 * (C1 * (M : ℝ) ^ (2 * e) * (3 * ((q : ℝ) + (M : ℝ)))) := by
            have hmono := mul_le_mul_of_nonneg_left hP
              (by positivity : (0 : ℝ) ≤ C1 * (M : ℝ) ^ (2 * e))
            linarith [hmono]
      _ ≤ (1 + 6 * C1) * (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ)) := by nlinarith [h1, hC1pos]
  have hnn : (0 : ℝ) ≤ ‖∑ m ∈ Finset.Icc 1 M, quadChar (γ * (m : ℝ) + β * (m : ℝ) ^ 2)‖ := norm_nonneg _
  have h2 := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq hnn] at h2
  have hM2e : (M : ℝ) ^ (2 * e) = ((M : ℝ) ^ e) ^ 2 := by
    rw [show (2 : ℝ) * e = e * 2 by ring]
    rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    rw [Real.rpow_two]
  have h3 : Real.sqrt ((1 + 6 * C1) * (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ)))
      = (1 + 6 * C1) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ e * ((q : ℝ) + (M : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (1 + 6 * C1) * (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ))
        = (1 + 6 * C1) * ((M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ))) by ring]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 + 6 * C1)
          (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ (2 * e) * ((q : ℝ) + (M : ℝ)))]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ (2 * e))
          (by positivity : (0 : ℝ) ≤ (q : ℝ) + (M : ℝ))]
    rw [show ((M : ℝ) ^ (2 * e)) ^ ((1 : ℝ) / 2) = (M : ℝ) ^ e by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
      ring]
    rw [mul_assoc]
  rw [h3] at h2
  exact h2

/-! ## Windowing: arbitrary starting point -/

/-- The windowed version: a sum over any `M ≤ q` consecutive squares. -/
lemma quad_weyl_shifted_block {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M n0 : ℕ) (β : ℝ) (a : ℤ) (q : ℕ),
      M ≤ q → Int.gcd a (q : ℤ) = 1 → |β - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
      ‖∑ m ∈ Finset.range M, quadChar (β * ((m + n0 : ℕ) : ℝ) ^ 2)‖
        ≤ C * (M : ℝ) ^ e * ((q : ℝ) + (M : ℝ)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨Cb, hCbpos, hCb⟩ := quad_weyl_phase_block (e := e) he
  refine ⟨Cb, hCbpos, ?_⟩
  intro M n0 β a q hMq ha hβ
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero]
    rw [Real.zero_rpow (ne_of_gt he)]
    simp
  · have hM1 : 1 ≤ M := hMpos
    have hreindex : (∑ m ∈ Finset.range M, quadChar (β * ((m + n0 : ℕ) : ℝ) ^ 2))
        = ∑ j ∈ Finset.Icc 1 M, quadChar (β * (((j : ℝ) + ((n0 : ℝ) - 1)) ^ 2)) := by
      rw [wd_sum_Icc_one_eq_sum_range M (fun j => quadChar (β * (((j : ℝ) + ((n0 : ℝ) - 1)) ^ 2)))]
      apply Finset.sum_congr rfl; intro k _
      rw [show ((k + n0 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + ((n0 : ℝ) - 1) by push_cast; ring]
    have hdecomp : (∑ j ∈ Finset.Icc 1 M, quadChar (β * (((j : ℝ) + ((n0 : ℝ) - 1)) ^ 2)))
        = quadChar (β * ((n0 : ℝ) - 1) ^ 2)
          * (∑ j ∈ Finset.Icc 1 M, quadChar ((2 * β * ((n0 : ℝ) - 1)) * (j : ℝ) + β * (j : ℝ) ^ 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [← quadChar_add]; congr 1; ring
    rw [hreindex, hdecomp, norm_mul, quadChar_norm, one_mul]
    exact hCb M (2 * β * ((n0 : ℝ) - 1)) β a q hM1 hMq ha hβ

/-! ## Block splitting -/

/-- If every window of length `≤ q` of a sequence is bounded by `B`, then the sum over
`range N` is bounded by `(N/q + 1)·B`. -/
lemma quad_weyl_blocks {q : ℕ} (hq : 0 < q) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) :
    ∀ (g : ℕ → ℂ), (∀ n0 M, M ≤ q → ‖∑ m ∈ Finset.range M, g (n0 + m)‖ ≤ B) →
      ‖∑ n ∈ Finset.range N, g n‖ ≤ ((N / q : ℕ) + 1 : ℝ) * B := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro g hblock
    rcases lt_or_ge N q with hNq | hNq
    · have h1 : ‖∑ n ∈ Finset.range N, g n‖ ≤ B := by
        have h := hblock 0 N (le_of_lt hNq)
        simpa using h
      have h2 : (1 : ℝ) ≤ ((N / q : ℕ) + 1 : ℝ) := by
        have : (0 : ℝ) ≤ ((N / q : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      calc ‖∑ n ∈ Finset.range N, g n‖ ≤ B := h1
        _ = 1 * B := by ring
        _ ≤ ((N / q : ℕ) + 1 : ℝ) * B := mul_le_mul_of_nonneg_right h2 hB
    · have hdq : ((N - q) / q : ℕ) + 1 = N / q := by
        rw [← Nat.add_div_right (N - q) hq, Nat.sub_add_cancel hNq]
      have hg' : ∀ n0 M, M ≤ q → ‖∑ m ∈ Finset.range M, (fun n => g (q + n)) (n0 + m)‖ ≤ B := by
        intro n0 M hM
        have h := hblock (q + n0) M hM
        simpa [Nat.add_assoc] using h
      have hIH := ih (N - q) (by omega) (fun n => g (q + n)) hg'
      have hsplit : (∑ n ∈ Finset.range N, g n)
          = (∑ n ∈ Finset.range q, g n) + (∑ n ∈ Finset.range (N - q), g (q + n)) := by
        conv_lhs => rw [show N = q + (N - q) by omega]
        rw [Finset.sum_range_add]
      rw [hsplit]
      have h1 : ‖∑ n ∈ Finset.range q, g n‖ ≤ B := by
        have h := hblock 0 q (le_refl q); simpa using h
      calc ‖(∑ n ∈ Finset.range q, g n) + (∑ n ∈ Finset.range (N - q), g (q + n))‖
          ≤ ‖∑ n ∈ Finset.range q, g n‖ + ‖∑ n ∈ Finset.range (N - q), g (q + n)‖ := norm_add_le _ _
        _ ≤ B + ((((N - q) / q : ℕ) : ℝ) + 1) * B := add_le_add h1 hIH
        _ = ((N / q : ℕ) + 1 : ℝ) * B := by
            have hc : (((N / q : ℕ)) : ℝ) = (((N - q) / q : ℕ) : ℝ) + 1 := by
              rw [← hdq]; push_cast; ring
            rw [hc]; ring

/-! ## The main theorem -/

/-- Weyl's inequality for quadratic exponential sums (the classical `k = 2` case, in the
form used by the circle method): for `a/q` in lowest terms with `|α − a/q| ≤ 1/q²`,
`|(1/N) ∑_{n<N} e(α n²)| ≲_ε N^ε (1/q + 1/N + q/N²)^{1/2}`.  Proven by Weyl
differencing (`weyl_ineq_two`) together with the counting estimate
`quadratic_differencing_counting`.  This is the minor-arc input of Bourgain's polynomial
ergodic result for the squares. -/
theorem quadratic_weyl_bound {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ N → 0 < q →
      Int.gcd a (q : ℤ) = 1 →
      ‖α - (a : ℝ) / (q : ℝ)‖ ≤ 1 / ((q : ℝ) ^ 2) →
      ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I * ((α * (n : ℝ) ^ 2 : ℝ) : ℂ))‖
        ≤ C * (N : ℝ) ^ e *
            (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := quad_weyl_shifted_block (e := e) he
  refine ⟨8 * Cw, by positivity, ?_⟩
  intro N α a q hN hq ha hβ1
  have hβ : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
    have h := hβ1; rwa [Real.norm_eq_abs] at h
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set W : ℝ := 1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 2 with hW
  have hWnn : 0 ≤ W := by rw [hW]; positivity
  set S : ℕ → ℂ := fun n => quadChar (α * (n : ℝ) ^ 2) with hSdef
  have hSeq : (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * ((α * (n : ℝ) ^ 2 : ℝ) : ℂ)))
      = ∑ n ∈ Finset.range N, S n := by
    apply Finset.sum_congr rfl; intro n _
    rw [quadChar_exp_form]
  rw [hSeq]
  have hnorm : ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.range N, S n)‖ = ‖∑ n ∈ Finset.range N, S n‖ / (N : ℝ) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
  rw [hnorm]
  have hqinv_le_W : (q : ℝ) ^ (-(1 : ℝ) / 2) ≤ W ^ ((1 : ℝ) / 2) := by
    have h1 : (q : ℝ) ^ (-(1 : ℝ) / 2) = ((q : ℝ) ^ (-(1 : ℝ))) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (le_of_lt hqpos)]; congr 1; ring
    rw [h1]
    have hle : (q : ℝ) ^ (-(1 : ℝ)) ≤ W := by
      rw [Real.rpow_neg_one, hW, one_div]
      have : (0 : ℝ) ≤ 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 2 := by positivity
      linarith
    exact Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hqpos) _) hle (by norm_num)
  have hqhalf_div_le_W : (q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) ≤ W ^ ((1 : ℝ) / 2) := by
    have h1 : (q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) = ((q : ℝ) / (N : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [Real.div_rpow (le_of_lt hqpos) (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
      congr 1
      rw [show ((N : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = (N : ℝ) by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hNpos)]]
    rw [h1]
    have hle : (q : ℝ) / (N : ℝ) ^ 2 ≤ W := by
      rw [hW]
      have : (0 : ℝ) ≤ 1 / (q : ℝ) + 1 / (N : ℝ) := by positivity
      linarith
    exact Real.rpow_le_rpow (by positivity) hle (by norm_num)
  rcases le_or_gt N q with hNq | hNq
  · -- small case: `N ≤ q`, a single window
    have h1 := hCw N 0 α a q hNq ha hβ
    have hsimp : (∑ m ∈ Finset.range N, quadChar (α * ((m + 0 : ℕ) : ℝ) ^ 2)) = ∑ n ∈ Finset.range N, S n := by
      apply Finset.sum_congr rfl; intro m _
      show quadChar (α * ((m + 0 : ℕ) : ℝ) ^ 2) = quadChar (α * (m : ℝ) ^ 2)
      rw [Nat.add_zero]
    rw [hsimp] at h1
    have hsqrtle : ((q : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) * W ^ ((1 : ℝ) / 2) := by
      have hNsq : ((N : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = (N : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hNpos)]
      have h1' : ((q : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 2)
          = ((N : ℝ) ^ 2 * (((q : ℝ) + (N : ℝ)) / (N : ℝ) ^ 2)) ^ ((1 : ℝ) / 2) := by
        congr 1; field_simp
      rw [h1', Real.mul_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
            (by positivity : (0 : ℝ) ≤ ((q : ℝ) + (N : ℝ)) / (N : ℝ) ^ 2), hNsq]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [hW, div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
      have hw2 : (1 / (q : ℝ) + 1 / (N : ℝ) + (q : ℝ) / (N : ℝ) ^ 2) * (N : ℝ) ^ 2
          = (N : ℝ) ^ 2 / (q : ℝ) + (N : ℝ) + (q : ℝ) := by field_simp
      rw [hw2]
      have : (0 : ℝ) ≤ (N : ℝ) ^ 2 / (q : ℝ) := by positivity
      linarith
    calc ‖∑ n ∈ Finset.range N, S n‖ / (N : ℝ)
        ≤ (Cw * (N : ℝ) ^ e * ((q : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 2)) / (N : ℝ) :=
          div_le_div_of_nonneg_right h1 (le_of_lt hNpos)
      _ ≤ (Cw * (N : ℝ) ^ e * ((N : ℝ) * W ^ ((1 : ℝ) / 2))) / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
          apply mul_le_mul_of_nonneg_left hsqrtle (by positivity)
      _ = Cw * (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) := by
          field_simp
      _ ≤ (8 * Cw) * (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) := by
          have hnn : (0 : ℝ) ≤ (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) :=
            mul_nonneg (Real.rpow_nonneg hNpos.le e) (Real.rpow_nonneg hWnn _)
          nlinarith [hnn, hCwpos]
  · -- large case: `q < N`, split into quad_weyl_blocks of length `q`
    have hq_le_N : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_lt hNq)
    have hqe_le_Ne : (q : ℝ) ^ e ≤ (N : ℝ) ^ e := Real.rpow_le_rpow hqpos.le hq_le_N he.le
    have hBnn : (0 : ℝ) ≤ Cw * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2) := by positivity
    have hwin : ∀ n0 M, M ≤ q →
        ‖∑ m ∈ Finset.range M, S (n0 + m)‖ ≤ Cw * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2) := by
      intro n0 M hMq
      have h1 := hCw M n0 α a q hMq ha hβ
      have heq : (∑ m ∈ Finset.range M, S (n0 + m))
          = ∑ m ∈ Finset.range M, quadChar (α * ((m + n0 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl; intro m _
        show quadChar (α * ((n0 + m : ℕ) : ℝ) ^ 2) = quadChar (α * ((m + n0 : ℕ) : ℝ) ^ 2)
        rw [show ((n0 + m : ℕ) : ℝ) = ((m + n0 : ℕ) : ℝ) by push_cast; ring]
      have hMle : (M : ℝ) ≤ (q : ℝ) := by exact_mod_cast hMq
      have hMe : (M : ℝ) ^ e ≤ (q : ℝ) ^ e := Real.rpow_le_rpow (Nat.cast_nonneg M) hMle he.le
      have hsq : ((q : ℝ) + (M : ℝ)) ^ ((1 : ℝ) / 2) ≤ ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      rw [heq]
      calc ‖∑ m ∈ Finset.range M, quadChar (α * ((m + n0 : ℕ) : ℝ) ^ 2)‖
          ≤ Cw * (M : ℝ) ^ e * ((q : ℝ) + (M : ℝ)) ^ ((1 : ℝ) / 2) := h1
        _ ≤ Cw * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hMe hCwpos.le) hsq (by positivity) (by positivity)
    have hSp := quad_weyl_blocks hq hBnn N S hwin
    have hNqbound : (((N / q : ℕ) : ℝ) + 1) ≤ (N : ℝ) * (1 / (q : ℝ) + 1 / (N : ℝ)) := by
      have h1 : (((N / q : ℕ)) : ℝ) ≤ (N : ℝ) / (q : ℝ) := Nat.cast_div_le
      have h3 : (N : ℝ) * (1 / (q : ℝ) + 1 / (N : ℝ)) = (N : ℝ) / (q : ℝ) + 1 := by field_simp
      rw [h3]; linarith
    have hqhalf_le : ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (q : ℝ) + (q : ℝ) = 2 * (q : ℝ) by ring]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hqpos)]
      have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      exact le_trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hqpos) _))
        (le_of_eq (by ring))
    have hterm : (1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ 4 * (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) := by
      have hstep : (1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ 2 * ((q : ℝ) ^ e * (q : ℝ) ^ (-(1 : ℝ) / 2)
              + (q : ℝ) ^ e * ((q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ))) := by
        have hqinv : (1 / (q : ℝ)) = (q : ℝ) ^ (-(1 : ℝ)) := by rw [one_div, ← Real.rpow_neg_one]
        have hqpow : (q : ℝ) ^ (-(1 : ℝ)) * (q : ℝ) ^ ((1 : ℝ) / 2) = (q : ℝ) ^ (-(1 : ℝ) / 2) := by
          rw [← Real.rpow_add hqpos]; congr 1; ring
        have hqq : (1 / (q : ℝ) + 1 / (N : ℝ)) * ((q : ℝ) ^ ((1 : ℝ) / 2))
            = (q : ℝ) ^ (-(1 : ℝ) / 2) + (q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) := by
          calc (1 / (q : ℝ) + 1 / (N : ℝ)) * ((q : ℝ) ^ ((1 : ℝ) / 2))
              = (q : ℝ) ^ (-(1 : ℝ)) * (q : ℝ) ^ ((1 : ℝ) / 2)
                + (1 / (N : ℝ)) * (q : ℝ) ^ ((1 : ℝ) / 2) := by
                rw [hqinv]; ring
            _ = (q : ℝ) ^ (-(1 : ℝ) / 2) + (q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) := by
                rw [hqpow]; ring
        calc (1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2)
            ≤ (1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * (2 * (q : ℝ) ^ ((1 : ℝ) / 2)) := by
              apply mul_le_mul_of_nonneg_left hqhalf_le
              exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hqpos) _)
          _ = 2 * ((1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * (q : ℝ) ^ ((1 : ℝ) / 2)) := by ring
          _ = 2 * ((q : ℝ) ^ e * ((1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ ((1 : ℝ) / 2))) := by ring
          _ = 2 * ((q : ℝ) ^ e * ((q : ℝ) ^ (-(1 : ℝ) / 2) + (q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ))) := by
              rw [hqq]
          _ = 2 * ((q : ℝ) ^ e * (q : ℝ) ^ (-(1 : ℝ) / 2)
                + (q : ℝ) ^ e * ((q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ))) := by ring
      have hA : (q : ℝ) ^ e * (q : ℝ) ^ (-(1 : ℝ) / 2) ≤ (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) :=
        mul_le_mul hqe_le_Ne hqinv_le_W (Real.rpow_nonneg (le_of_lt hqpos) _)
          (Real.rpow_nonneg hNpos.le e)
      have hB : (q : ℝ) ^ e * ((q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ)) ≤ (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) := by
        have h2 : (q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) ≤ W ^ ((1 : ℝ) / 2) := hqhalf_div_le_W
        exact mul_le_mul hqe_le_Ne h2 (by positivity) (Real.rpow_nonneg hNpos.le e)
      calc (1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ 2 * ((q : ℝ) ^ e * (q : ℝ) ^ (-(1 : ℝ) / 2)
              + (q : ℝ) ^ e * ((q : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ))) := hstep
        _ ≤ 2 * ((N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) + (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2)) := by
            linarith [hA, hB]
        _ = 4 * ((N : ℝ) ^ e * W ^ ((1 : ℝ) / 2)) := by ring
        _ = 4 * (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) := by ring
    calc ‖∑ n ∈ Finset.range N, S n‖ / (N : ℝ)
        ≤ ((((N / q : ℕ) : ℝ) + 1) * (Cw * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2))) / (N : ℝ) :=
          div_le_div_of_nonneg_right hSp (le_of_lt hNpos)
      _ ≤ ((N : ℝ) * (1 / (q : ℝ) + 1 / (N : ℝ))
            * (Cw * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2))) / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
          exact mul_le_mul_of_nonneg_right hNqbound (by positivity)
      _ = (1 / (q : ℝ) + 1 / (N : ℝ)) * (q : ℝ) ^ e * ((q : ℝ) + (q : ℝ)) ^ ((1 : ℝ) / 2) * Cw := by
          field_simp
      _ ≤ (4 * (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2)) * Cw := mul_le_mul_of_nonneg_right hterm hCwpos.le
      _ ≤ (8 * Cw) * (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) := by
          have hnn : (0 : ℝ) ≤ (N : ℝ) ^ e * W ^ ((1 : ℝ) / 2) :=
            mul_nonneg (Real.rpow_nonneg hNpos.le e) (Real.rpow_nonneg hWnn _)
          nlinarith [hnn, hCwpos]

end Commons.Analysis.ExponentialSums
