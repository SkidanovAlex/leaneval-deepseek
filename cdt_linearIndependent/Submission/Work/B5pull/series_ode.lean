import Mathlib

/-!
# The ODE satisfied by a power series built from a coefficient recurrence

Given coefficient sequences `c d : ℕ → ℂ` obeying the recurrence

`8 n c n - 2 (n-1) c (n-1) = 4 c n - (if n = 0 then 0 else c (n-1)) - 2 d n + (if n = 1 then 4 else 0)`

and such that the relevant series `∑ c n * y^n`, `∑ n * c n * y^n`, `∑ (n+1) * c (n+1) * y^n`,
`∑ d n * y^n` are summable at `y` (with the derivative of `f z = ∑ c n * z^n` at `y` given by
term-by-term differentiation), the function `f` satisfies the first-order ODE

`2 y (4 - y) f'(y) = (4 - y) f(y) - 2 g(y) + 4 y`,  where `g z = ∑ d n * z^n`.

This is the abstract summation argument used for the "pullback" (B5) step: the recurrence is
`hrec`, and the conclusion is the inhomogeneous linear ODE for `f`.
-/

namespace Work.B5pull

open scoped BigOperators

/-- Prefixing a shift-of-one series with a zero at `n = 0` is summable whenever the original
series `∑ a n * y^n` is. -/
private lemma summable_shift_pow (a : ℕ → ℂ) (y : ℂ) (h : Summable fun n => a n * y ^ n) :
    Summable fun n => (if n = 0 then 0 else a (n - 1)) * y ^ n := by
  rw [← summable_nat_add_iff (f := fun n => (if n = 0 then 0 else a (n - 1)) * y ^ n) 1]
  refine (h.mul_left y).congr (fun n => ?_)
  simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, pow_succ]
  ring

/-- Reindexing identity: the series `∑ (if n = 0 then 0 else a (n-1)) * y^n` is obtained from
`∑ a n * y^n` by multiplying by `y`. -/
private lemma tsum_shift_pow (a : ℕ → ℂ) (y : ℂ) (h : Summable fun n => a n * y ^ n) :
    ∑' n, (if n = 0 then 0 else a (n - 1)) * y ^ n = y * ∑' n, a n * y ^ n := by
  have hG := summable_shift_pow a y h
  rw [hG.tsum_eq_zero_add]
  have h0 : (if (0 : ℕ) = 0 then 0 else a (0 - 1)) * y ^ 0 = 0 := by simp
  rw [h0, zero_add, ← tsum_mul_left]
  exact tsum_congr (fun n => by
    simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, pow_succ]
    ring)

theorem series_ode (c d : ℕ → ℂ) (y : ℂ)
    (hrec : ∀ n : ℕ, 8 * ((n : ℂ) * c n) - 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1))
      = 4 * c n - (if n = 0 then 0 else c (n - 1)) - 2 * d n + (if n = 1 then 4 else 0))
    (hS : Summable fun n : ℕ => c n * y ^ n)
    (hS2 : Summable fun n : ℕ => (n : ℂ) * c n * y ^ n)
    (hS3 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)
    (hSd : Summable fun n : ℕ => d n * y ^ n)
    (hderiv : deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) :
    2 * y * (4 - y) * deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = (4 - y) * (∑' n : ℕ, c n * y ^ n) - 2 * (∑' n : ℕ, d n * y ^ n) + 4 * y := by
  -- `∑ n * c n * y^n = y * f'(y)`, via reindexing and the given term-by-term derivative.
  have hT1val : (∑' n : ℕ, (n : ℂ) * c n * y ^ n)
      = y * deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y := by
    rw [hderiv, ← tsum_shift_pow (fun m => ((m + 1 : ℕ) : ℂ) * c (m + 1)) y hS3]
    exact tsum_congr (fun n => by
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)])
  -- `∑ (n-1) * c (n-1) * y^n = y * ∑ n * c n * y^n`.
  have hT2val : (∑' n : ℕ, (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n)
      = y * (∑' n : ℕ, (n : ℂ) * c n * y ^ n) := by
    rw [← tsum_shift_pow (fun m => (m : ℂ) * c m) y hS2]
    exact tsum_congr (fun n => by
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn])
  -- Summability of the individual pieces of the left-hand side.
  have hA : Summable (fun n : ℕ => 8 * ((n : ℂ) * c n) * y ^ n) :=
    (hS2.mul_left 8).congr (fun n => by ring)
  have hB : Summable (fun n : ℕ => 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n) := by
    have hb : Summable (fun n : ℕ => (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n) :=
      (summable_shift_pow (fun m => (m : ℂ) * c m) y hS2).congr (fun n => by
        by_cases hn : n = 0
        · subst hn; simp
        · simp [hn])
    exact (hb.mul_left 2).congr (fun n => by ring)
  -- Summability of the individual pieces of the right-hand side.
  have hC : Summable (fun n : ℕ => 4 * c n * y ^ n) :=
    (hS.mul_left 4).congr (fun n => by ring)
  have hD : Summable (fun n : ℕ => (if n = 0 then 0 else c (n - 1)) * y ^ n) :=
    summable_shift_pow c y hS
  have hE : Summable (fun n : ℕ => 2 * d n * y ^ n) :=
    (hSd.mul_left 2).congr (fun n => by ring)
  have hF : Summable (fun n : ℕ => (if n = 1 then 4 else 0) * y ^ n) :=
    (hasSum_single (1 : ℕ) (fun b hb => by simp [hb])).summable
  -- Closed forms of the four pieces on the right.
  have hCval : (∑' n : ℕ, 4 * c n * y ^ n) = 4 * (∑' n : ℕ, c n * y ^ n) := by
    rw [← tsum_mul_left]; exact tsum_congr (fun n => by ring)
  have hDval : (∑' n : ℕ, (if n = 0 then 0 else c (n - 1)) * y ^ n)
      = y * (∑' n : ℕ, c n * y ^ n) := tsum_shift_pow c y hS
  have hEval : (∑' n : ℕ, 2 * d n * y ^ n) = 2 * (∑' n : ℕ, d n * y ^ n) := by
    rw [← tsum_mul_left]; exact tsum_congr (fun n => by ring)
  have hFval : (∑' n : ℕ, (if n = 1 then 4 else 0) * y ^ n) = 4 * y := by
    rw [tsum_eq_single 1 (fun b hb => by simp [hb])]; simp
  -- Evaluation of the left-hand sum.
  have hpointL : (fun n : ℕ => (8 * ((n : ℂ) * c n) - 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
        = (fun n : ℕ => 8 * ((n : ℂ) * c n) * y ^ n
            - 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n) :=
    funext (fun n => by ring)
  have hAval : (∑' n : ℕ, 8 * ((n : ℂ) * c n) * y ^ n)
      = 8 * (∑' n : ℕ, (n : ℂ) * c n * y ^ n) := by
    rw [← tsum_mul_left]; exact tsum_congr (fun n => by ring)
  have hBval : (∑' n : ℕ, 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n)
      = 2 * (∑' n : ℕ, (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ n) := by
    rw [← tsum_mul_left]; exact tsum_congr (fun n => by ring)
  have hL : (∑' n : ℕ, (8 * ((n : ℂ) * c n) - 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
      = 2 * y * (4 - y) * deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y := by
    rw [hpointL, hA.tsum_sub hB, hAval, hBval, hT2val, hT1val]
    ring
  -- Evaluation of the right-hand sum.
  have hpointR : (fun n : ℕ => (4 * c n - (if n = 0 then 0 else c (n - 1)) - 2 * d n
          + (if n = 1 then 4 else 0)) * y ^ n)
        = (fun n : ℕ => 4 * c n * y ^ n - (if n = 0 then 0 else c (n - 1)) * y ^ n
            - 2 * d n * y ^ n + (if n = 1 then 4 else 0) * y ^ n) :=
    funext (fun n => by ring)
  have hCD : Summable (fun n : ℕ => 4 * c n * y ^ n - (if n = 0 then 0 else c (n - 1)) * y ^ n) :=
    hC.sub hD
  have hCDE : Summable (fun n : ℕ =>
      (4 * c n * y ^ n - (if n = 0 then 0 else c (n - 1)) * y ^ n) - 2 * d n * y ^ n) :=
    hCD.sub hE
  have hR : (∑' n : ℕ, (4 * c n - (if n = 0 then 0 else c (n - 1)) - 2 * d n
          + (if n = 1 then 4 else 0)) * y ^ n)
      = (4 - y) * (∑' n : ℕ, c n * y ^ n) - 2 * (∑' n : ℕ, d n * y ^ n) + 4 * y := by
    rw [hpointR]
    rw [hCDE.tsum_add hF, hCD.tsum_sub hE, hC.tsum_sub hD]
    rw [hCval, hDval, hEval, hFval]
    ring
  -- The two sums are equal term by term, thanks to the recurrence.
  have key : (∑' n : ℕ, (8 * ((n : ℂ) * c n) - 2 * (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
      = (∑' n : ℕ, (4 * c n - (if n = 0 then 0 else c (n - 1)) - 2 * d n
          + (if n = 1 then 4 else 0)) * y ^ n) :=
    tsum_congr (fun n => by rw [hrec n])
  rw [← hL, key, hR]

end Work.B5pull
