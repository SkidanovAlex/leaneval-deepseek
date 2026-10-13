/-
# Weighted derivatives of `(1+z)·At N 0 z` up to order `7`

Target: `Work.FTS.PhiStar.At_linear_deriv_bound`.

## The mathematics

With `At N j z = ∫_0^1 t^{N+j}/(1+zt)^{j+2} dt` (`FTS/H2/PhiStarE/GbarDefs.lean`) one has
`d/dz (At N j) = -(j+2)·At N (j+1)` (`At_hasDerivAt` in `Gbar_wiln.lean`), and hence, by an
elementary induction,

  `deriv^[k] (fun w => (1+w)·At N 0 w)
      = (-1)^(k-1)·k·k!·At N (k-1)  +  (-1)^k·(k+1)!·(1+z)·At N k`   (`k ≥ 1`),

i.e. the `k`-th derivative is a *two-term* combination of `At N (k-1)` and `(1+z)·At N k`.
(The recurrence behind it: if `g_k = a_k·At N (k-1) + b_k·(1+z)·At N k`, then
`g_k' = (-(k+1)a_k + b_k)·At N k - (k+2)b_k·(1+z)·At N (k+1)`, and
`b_{k+1} = -(k+2)b_k`, `a_{k+1} = -(k+1)a_k + b_k` are solved by `b_k = (-1)^k(k+1)!`,
`a_k = (-1)^(k-1)k·k!`.)

Multiplying by `(1+z)^k` gives

  `(1+z)^k·deriv^[k] f = a_k·(1+z)^k·At N (k-1) + b_k·(1+z)^(k+1)·At N k`,

and the *only* analytic input is the weighted estimate `shift_bound` (proved in
`Gbar_wiln.lean`):

  `|(1+z)^c · z^e · At N j z| ≤ 2^(c+1)/N`  whenever `c + e ≤ j + 1`, `N ≥ 2`, `z ≥ 0`.

Here the exponent budgets are `k ≤ (k-1)+1` and `k+1 ≤ k+1`, i.e. exactly met, so each term is
`O(1/N)` uniformly for `z ≥ 0`, and with the coefficients `|a_k| ≤ 7·7!`, `|b_k| ≤ 8!` the
constant `3·10^7` suffices for all `k ≤ 7`.

The formalisation carries the two coefficients as one family of "slots"
`AtLinComb N k = c1 k·At N k + c2 k·(1+z)·At N (k+1)` and performs the induction on `k` on the
open set `Ioi 0` (where `deriv` is the honest derivative; `At N j` is differentiable on
`Ioi (-1/2)` but the library supplies `At_hasDerivAt` only for `z ≥ 0`).  All terms
`At`, `At'`, … are `@[simp]`-unfolded by the unqualified `simp`/`norm_num`, so the numeric
computations below are phrased with `norm_num [Nat.factorial]` and closed with `ring`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.PhiStarE.Gbar_wiln

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The coefficient of the `At N k` slot in `deriv^[k+1] ((1+z)·At N 0 z)`:
`(-1)^k·(k+1)!·(k+1)`. -/
def AtLinC1 (k : ℕ) : ℝ := (-1) ^ k * ((k + 1).factorial : ℝ) * (k + 1)

/-- The coefficient of the `(1+z)·At N (k+1)` slot in `deriv^[k+1] ((1+z)·At N 0 z)`:
`(-1)^(k+1)·(k+2)!`. -/
def AtLinC2 (k : ℕ) : ℝ := (-1) ^ (k + 1) * ((k + 2).factorial : ℝ)

/-- The two-term combination which equals the `(k+1)`-st derivative of `(1+z)·At N 0 z`. -/
def AtLinComb (N : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => AtLinC1 k * Work.FTS.H2.PhiStarE.At N k z
    + AtLinC2 k * ((1 + z) * Work.FTS.H2.PhiStarE.At N (k + 1) z)

/-- The recursion for the first coefficient. -/
lemma AtLinC1_succ (k : ℕ) :
    AtLinC1 (k + 1) = -((k : ℝ) + 2) * AtLinC1 k + AtLinC2 k := by
  simp only [AtLinC1, AtLinC2, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  ring

/-- The recursion for the second coefficient. -/
lemma AtLinC2_succ (k : ℕ) : AtLinC2 (k + 1) = -((k : ℝ) + 3) * AtLinC2 k := by
  simp only [AtLinC2, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  ring

/-- `|AtLinC1 k| = (k+1)!·(k+1) ≤ 7·7! = 35280` for `k ≤ 6`. -/
lemma AtLin_absC1_le (k : ℕ) (hk : k ≤ 6) : |AtLinC1 k| ≤ 35280 := by
  interval_cases k <;> norm_num [AtLinC1, Nat.factorial]

/-- `|AtLinC2 k| = (k+2)! ≤ 8! = 40320` for `k ≤ 6`. -/
lemma AtLin_absC2_le (k : ℕ) (hk : k ≤ 6) : |AtLinC2 k| ≤ 40320 := by
  interval_cases k <;> norm_num [AtLinC2, Nat.factorial]

/-- The library's `shift_bound` in the `e = 0` shape used below:
`|(1+z)^c·At N j z| ≤ 2^(c+1)/N` when `c ≤ j+1`. -/
lemma AtLin_shift_bound (N : ℝ) (hN : 2 ≤ N) (c j : ℕ) (hc : c ≤ j + 1) {z : ℝ}
    (hz : 0 ≤ z) :
    |(1 + z) ^ c * Work.FTS.H2.PhiStarE.At N j z| ≤ 2 ^ (c + 1) / N := by
  have h := Work.FTS.H2.PhiStarE.shift_bound N hN c j 0 (by omega) hz
  simpa using h

/-- The derivative of `At N (j+1)`, with the cast `((j+1 : ℕ) : ℝ) + 2 = (j:ℝ) + 3`
normalised away. -/
lemma AtLin_hasDerivAt_At_succ (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (Work.FTS.H2.PhiStarE.At N (j + 1))
      (-((j : ℝ) + 3) * Work.FTS.H2.PhiStarE.At N (j + 2) z) z := by
  have h := Work.FTS.H2.PhiStarE.At_hasDerivAt N hN (j + 1) hz
  convert h using 1
  push_cast
  ring

/-- Product rule for the basic pair `(1+z)·At N (j+1)`. -/
lemma AtLin_hasDerivAt_one_add_mul (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun y : ℝ => (1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y)
      (Work.FTS.H2.PhiStarE.At N (j + 1) z
        - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z)) z := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h' : HasDerivAt (fun y : ℝ => (1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y)
      (1 * Work.FTS.H2.PhiStarE.At N (j + 1) z
        + (1 + z) * (-((j : ℝ) + 3) * Work.FTS.H2.PhiStarE.At N (j + 2) z)) z :=
    h1.mul (AtLin_hasDerivAt_At_succ N hN j hz)
  convert h' using 1
  ring

/-- The derivative of the two-term combination `AtLinComb N j`. -/
lemma AtLin_hasDerivAt_comb (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (AtLinComb N j)
      (AtLinC1 j * (-((j : ℝ) + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)
        + AtLinC2 j * (Work.FTS.H2.PhiStarE.At N (j + 1) z
          - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z))) z := by
  have h1 : HasDerivAt (fun y : ℝ => AtLinC1 j * Work.FTS.H2.PhiStarE.At N j y)
      (AtLinC1 j * (-((j : ℝ) + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)) z :=
    (Work.FTS.H2.PhiStarE.At_hasDerivAt N hN j hz).const_mul (AtLinC1 j)
  have h2 : HasDerivAt
      (fun y : ℝ => AtLinC2 j * ((1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y))
      (AtLinC2 j * (Work.FTS.H2.PhiStarE.At N (j + 1) z
        - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z))) z :=
    (AtLin_hasDerivAt_one_add_mul N hN j hz).const_mul (AtLinC2 j)
  have h' : HasDerivAt
      (fun y : ℝ => AtLinC1 j * Work.FTS.H2.PhiStarE.At N j y
        + AtLinC2 j * ((1 + y) * Work.FTS.H2.PhiStarE.At N (j + 1) y))
      (AtLinC1 j * (-((j : ℝ) + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)
        + AtLinC2 j * (Work.FTS.H2.PhiStarE.At N (j + 1) z
          - ((j : ℝ) + 3) * ((1 + z) * Work.FTS.H2.PhiStarE.At N (j + 2) z))) z :=
    h1.add h2
  exact h'

/-- The base case `k = 1`: `deriv ((1+z)·At N 0 z) = At N 0 z - 2·(1+z)·At N 1 z`. -/
lemma AtLin_hasDerivAt_base (N : ℝ) (hN : 0 ≤ N) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun w : ℝ => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w)
      (Work.FTS.H2.PhiStarE.At N 0 z
        - 2 * ((1 + z) * Work.FTS.H2.PhiStarE.At N 1 z)) z := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (Work.FTS.H2.PhiStarE.At N 0)
      (-2 * Work.FTS.H2.PhiStarE.At N 1 z) z := by
    have h := Work.FTS.H2.PhiStarE.At_hasDerivAt N hN 0 hz
    convert h using 1
    norm_num
  have h' : HasDerivAt (fun y : ℝ => (1 + y) * Work.FTS.H2.PhiStarE.At N 0 y)
      (1 * Work.FTS.H2.PhiStarE.At N 0 z + (1 + z) * (-2 * Work.FTS.H2.PhiStarE.At N 1 z)) z :=
    h1.mul h2
  convert h' using 1
  ring

/-- **The explicit formula for the iterated derivatives.**  For `N ≥ 0` and every `j`,
on `(0,∞)` the `(j+1)`-st derivative of `w ↦ (1+w)·At N 0 w` is `AtLinComb N j`, i.e.
`(-1)^j (j+1)! (j+1)·At N j + (-1)^(j+1) (j+2)!·(1+z)·At N (j+1)`. -/
theorem AtLin_iter_formula (N : ℝ) (hN : 0 ≤ N) (j : ℕ) :
    EqOn ((deriv^[j + 1]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w))
      (AtLinComb N j) (Set.Ioi 0) := by
  induction j with
  | zero =>
      intro z hz
      have hz0 : 0 ≤ z := le_of_lt hz
      rw [Function.iterate_one, (AtLin_hasDerivAt_base N hN hz0).deriv, AtLinComb]
      have h1 : AtLinC1 0 = 1 := by norm_num [AtLinC1, Nat.factorial]
      have h2 : AtLinC2 0 = -2 := by norm_num [AtLinC2, Nat.factorial]
      rw [h1, h2]
      ring
  | succ j ih =>
      intro z hz
      have hz0 : 0 ≤ z := le_of_lt hz
      rw [Function.iterate_succ_apply']
      have hev : (deriv^[j + 1]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w)
          =ᶠ[𝓝 z] AtLinComb N j := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih hy
      rw [hev.deriv_eq, (AtLin_hasDerivAt_comb N hN j hz0).deriv]
      simp only [AtLinComb]
      rw [AtLinC1_succ, AtLinC2_succ]
      ring

/-- **The target estimate.**  There is a universal constant `C` with
`|(1+z)^k · (deriv^[k]) (w ↦ (1+w)·At N 0 w) z| ≤ C/N` for all `N ≥ 2`, `z > 0`, `k ≤ 7`.
The constant `3·10^7` is (very) far from optimal: the sharp bound for `k ≤ 7` is
`7·7!·2^8 + 8!·2^9 = 29675520`. -/
theorem At_linear_deriv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (N z : ℝ) (k : ℕ), 2 ≤ N → 0 < z → k ≤ 7 →
      |(1 + z) ^ k * (deriv^[k]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At N 0 w) z| ≤ C / N := by
  refine ⟨30000000, by norm_num, fun N z k hN hz hk => ?_⟩
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : (0 : ℝ) ≤ N := le_of_lt hNpos
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  rcases k with _ | j
  · rw [Function.iterate_zero_apply, pow_zero, one_mul]
    have h := AtLin_shift_bound N hN 1 0 (by norm_num) hz0
    have h4 : (2 : ℝ) ^ (1 + 1) / N = 4 / N := by norm_num
    rw [pow_one, h4] at h
    exact h.trans (div_le_div_of_nonneg_right (by norm_num) hN0)
  · have hk6 : j ≤ 6 := by omega
    rw [AtLin_iter_formula N hN0 j hz]
    have heq : (1 + z) ^ (j + 1) * AtLinComb N j z
        = AtLinC1 j * ((1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z)
          + AtLinC2 j * ((1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z) := by
      rw [AtLinComb, pow_succ]
      ring
    rw [heq]
    have hb1 := AtLin_shift_bound N hN (j + 1) j (le_refl _) hz0
    have hb2 := AtLin_shift_bound N hN (j + 2) (j + 1) (by omega) hz0
    have hp1 : (2 : ℝ) ^ (j + 1 + 1) / N ≤ 256 / N := by
      apply div_le_div_of_nonneg_right _ hN0
      have h8 : j + 1 + 1 ≤ 8 := by omega
      calc (2 : ℝ) ^ (j + 1 + 1) ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) h8
        _ = 256 := by norm_num
    have hp2 : (2 : ℝ) ^ (j + 2 + 1) / N ≤ 512 / N := by
      apply div_le_div_of_nonneg_right _ hN0
      have h9 : j + 2 + 1 ≤ 9 := by omega
      calc (2 : ℝ) ^ (j + 2 + 1) ≤ 2 ^ 9 := pow_le_pow_right₀ (by norm_num) h9
        _ = 512 := by norm_num
    calc |AtLinC1 j * ((1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z)
            + AtLinC2 j * ((1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)|
        ≤ |AtLinC1 j * ((1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z)|
            + |AtLinC2 j * ((1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z)| :=
          abs_add_le _ _
      _ = |AtLinC1 j| * |(1 + z) ^ (j + 1) * Work.FTS.H2.PhiStarE.At N j z|
            + |AtLinC2 j| * |(1 + z) ^ (j + 2) * Work.FTS.H2.PhiStarE.At N (j + 1) z| := by
          simp only [abs_mul]
      _ ≤ 35280 * (256 / N) + 40320 * (512 / N) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (AtLin_absC1_le j hk6) (hb1.trans hp1) (abs_nonneg _) (by norm_num)
          · exact mul_le_mul (AtLin_absC2_le j hk6) (hb2.trans hp2) (abs_nonneg _) (by norm_num)
      _ = 29675520 / N := by ring
      _ ≤ 30000000 / N := div_le_div_of_nonneg_right (by norm_num) hN0

end Work.FTS.PhiStar
