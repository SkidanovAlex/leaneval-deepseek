import Mathlib
import Submission.Commons.Analysis.DirichletPolynomial.well_spaced_block_mean_value

namespace Commons.NumberTheory.DirichletPolynomial

open Finset Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false

/-- Large sieve / sampled mean value bound for a MULTIPLICATIVE BLOCK: there is an
absolute constant `C > 0` such that for every `N ≥ 1`, every coefficient vector `a`
supported in `[N, 2N]`, every `T ≥ 0` and every `1`-separated family `t : Fin R → ℝ`
with values in `[0,T]`,

`Σ_r ‖Σ_{n ∈ [N,2N]} a_n · n^{i t_r}‖² ≤ C·(T + N)·Σ_{n ∈ [N,2N]} ‖a_n‖²`.

This is the discrete ('sampled') form of the Montgomery–Vaughan mean value bound for a
multiplicative block.  The key point is that the frequencies `log n ∈ [log N, log 2N]`
have bounded diameter `log 2 < 1`, so the sampled sum can be compared with the integral
mean value with an absolute constant loss.  (A `C·(T+N)` shape — with the absolute
constant on the `T` term as well — is correct; a coefficient exactly `1` on `T` is
false.)  For `a` supported on a general set of frequencies of diameter ≤ 1 the same
bound holds with `X` in place of `N`.  The statement fails without the bounded
frequency-window hypothesis (e.g. for `a` supported on `{3^k : k ≤ K}` the resonance at
`t = 2πr/log 3` makes the left side `≍ R·(K+1)²` while `Σ‖a_n‖² = K+1`). -/
theorem large_sieve_block_sampled :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 0 ≤ T) (a : ℕ → ℂ)
        (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∀ n, n ∉ Finset.Icc N (2 * N) → a n = 0) →
        (∑ r : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * (t r : ℂ))‖ ^ 2) ≤
          C * (T + (N : ℝ)) * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ ^ 2) := by
  obtain ⟨C, hCpos, hmain⟩ :=
    Commons.Analysis.DirichletPolynomial.well_spaced_block_mean_value
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN T hT a R t hIcc hsep _hsupp
  -- Apply the block mean value estimate with `K = ⌈T⌉₊`.
  have hK : ∀ i, t i ∈ Set.Icc (0 : ℝ) ((Nat.ceil T : ℕ) : ℝ) := by
    intro i
    exact ⟨(hIcc i).1, le_trans (hIcc i).2 (Nat.le_ceil T)⟩
  have hb := hmain N (Nat.ceil T) a R t hN hsep hK
  have hceil : ((Nat.ceil T : ℕ) : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsumNN : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  refine le_trans hb ?_
  apply mul_le_mul_of_nonneg_right _ hsumNN
  have hstep : ((Nat.ceil T : ℕ) : ℝ) + (N : ℝ) ≤ 2 * (T + (N : ℝ)) := by
    nlinarith [hceil, hN1, hT]
  have h1 : C * (((Nat.ceil T : ℕ) : ℝ) + (N : ℝ)) ≤ (2 * C) * (T + (N : ℝ)) := by
    have h2 := mul_le_mul_of_nonneg_left hstep hCpos.le
    nlinarith [h2, hCpos.le]
  exact h1

end Commons.NumberTheory.DirichletPolynomial
