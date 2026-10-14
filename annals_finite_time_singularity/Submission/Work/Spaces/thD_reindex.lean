import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
-- ===== merged: Submission.Work.Spaces.scoef =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.Spaces

set_option autoImplicit false

/-- `scoef n k` is the Stirling number of the second kind `S(n,k)`, defined by the
recursion `S(0,0) = 1`, `S(n+1,0) = 0` and `S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)`.
These are the coefficients of the expansion `D_z^n = ∑_k S(n,k) z^k ∂_z^k`. -/
def scoef : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * scoef n (k + 1) + scoef n k

/-- The `n`-th Bell number, i.e. the sum of the Stirling numbers of the second kind
in row `n`: `bell n = ∑_{k≤n} S(n,k)`.  This is exactly the total size of the
coefficients of the expansion `D_z^n = ∑_k S(n,k) z^k ∂_z^k`
(and `bell n = ∑_{k≤n} |S(n,k)|`, since the coefficients are nonnegative). -/
def bell (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), scoef n k

/-- `S(n,k) = 0` for `k > n`: the expansion of `D_z^n` only involves the derivatives
`∂_z^k` with `k ≤ n`. -/
theorem scoef_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → scoef n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; cases k with
    | zero => omega
    | succ m => simp [scoef]
  | succ n ih => intro k hk; cases k with
    | zero => omega
    | succ m =>
      have h1 : n < m + 1 := by omega
      have h2 : n < m := by omega
      simp [scoef, ih h1, ih h2]

/-- `scoef n (n+1) = 0`, the case of `scoef_eq_zero_of_lt` used by the reindexing. -/
theorem scoef_succ_self_eq_zero (n : ℕ) : scoef n (n + 1) = 0 :=
  scoef_eq_zero_of_lt (Nat.lt_succ_self n)

/-- The Bell numbers of the rows `0 ≤ n ≤ 4` are `1, 1, 2, 5, 15`, all of them
well below `100`. -/
theorem bell_le (n : ℕ) (hn : n ≤ 4) : bell n ≤ 100 := by
  interval_cases n <;> decide

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.sin_rpow_le_majorant_pi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Spaces

/-- Core Jordan-type estimate: for `0 < p` and `x ∈ [0, π/4]`,
`(sin (2 x)) ^ (-p) ≤ (π/4) ^ p * x ^ (-p)`.

Jordan's inequality `(2/π) y ≤ sin y` on `[0, π/2]`, applied to `y = 2 x`, gives
`sin (2 x) ≥ (4/π) x`; raising to the non-positive power `-p` reverses the
inequality and the constant `(4/π) ^ (-p)` is rewritten as `(π/4) ^ p`. -/
private lemma sin_two_mul_rpow_le_of_le_pi_div_four (p x : ℝ) (hp : 0 < p)
    (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * x)) ^ (-p) ≤ (Real.pi / 4) ^ p * x ^ (-p) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [mul_zero, Real.sin_zero, Real.zero_rpow (by linarith : (-p) ≠ 0), mul_zero]
  · have h2x0 : 0 ≤ 2 * x := by linarith
    have h2x1 : 2 * x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have hj := Real.mul_le_sin h2x0 h2x1
    have hjeq : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
    rw [hjeq] at hj
    have hpos : 0 < (4 / Real.pi) * x := by positivity
    have key := Real.rpow_le_rpow_of_nonpos hpos hj (show -p ≤ 0 by linarith)
    have hcoef : (4 / Real.pi : ℝ) ^ (-p) = (Real.pi / 4) ^ p := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
          ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) p, inv_div]
    have hmr : ((4 / Real.pi) * x) ^ (-p) = (Real.pi / 4) ^ p * x ^ (-p) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (le_of_lt h), hcoef]
    rw [hmr] at key
    exact key

/-- For `0 < p` and `θ ∈ [0, π/2]`,
`(sin (2 θ)) ^ (-p) ≤ (π/4) ^ p * (θ ^ (-p) + (π/2 - θ) ^ (-p))`.

The estimate is invariant under the reflection `θ ↦ π/2 - θ` (because
`sin (π - 2θ) = sin (2θ)`), so it suffices to treat `θ ≤ π/4`.  There Jordan's
inequality `sin (2θ) ≥ (4/π) θ` gives `(sin (2θ)) ^ (-p) ≤ (π/4) ^ p * θ ^ (-p)`,
and the positive term `(π/2 - θ) ^ (-p)` may be added freely. -/
theorem sin_rpow_le_majorant_pi (p θ : ℝ) (hp : 0 < p) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-p) ≤ (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases le_total θ (Real.pi / 4) with h | h
  · have hcore := sin_two_mul_rpow_le_of_le_pi_div_four p θ hp ⟨hθ0, h⟩
    have h1 : θ ^ (-p) ≤ θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p) :=
      le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - θ) (-p))
    have hle : (Real.pi / 4) ^ p * θ ^ (-p) ≤
        (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p)
    linarith
  · have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      have h2 : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
      rw [h2, Real.sin_pi_sub]
    have hcore := sin_two_mul_rpow_le_of_le_pi_div_four p (Real.pi / 2 - θ) hp
      ⟨by linarith, by linarith⟩
    rw [hsin]
    have h1 : (Real.pi / 2 - θ) ^ (-p) ≤ θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p) :=
      le_add_of_nonneg_left (Real.rpow_nonneg hθ0 (-p))
    have hle : (Real.pi / 4) ^ p * (Real.pi / 2 - θ) ^ (-p) ≤
        (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p)
    linarith

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.thD_reindex =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- Reindexing identity for the Leibniz/Pascal convolution:

`∑_{a} C(i,a) X(a+1) Y(i-a) + ∑_{a} C(i,a) X(a) Y(i-a+1)
  = ∑_{b} C(i+1,b) X(b) Y(i+1-b)`,

i.e. the derivative of the binomial convolution equals the sum of the two
shifted convolutions. -/
theorem thD_reindex (i : ℕ) (X Y : ℕ → ℝ) :
    (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a))
      + (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X a * Y ((i - a) + 1))
    = ∑ b ∈ Finset.range (i + 1 + 1), (Nat.choose (i + 1) b : ℝ) * X b * Y (i + 1 - b) := by
  have hA : (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a))
      = (∑ a ∈ Finset.range i, (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a)) + X (i+1) * Y 0 := by
    rw [Finset.sum_range_succ]
    congr 1
    simp [Nat.choose_self]
  have hB : (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X a * Y ((i - a) + 1))
      = (∑ a ∈ Finset.range i, (Nat.choose i (a+1) : ℝ) * X (a + 1) * Y (i - a)) + X 0 * Y (i+1) := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      have ha' : a < i := Finset.mem_range.mp ha
      have h : i - (a+1) + 1 = i - a := by omega
      simp [h]
    · simp [Nat.choose_zero_right]
  have hS1 : (∑ b ∈ Finset.range (i + 1 + 1), (Nat.choose (i + 1) b : ℝ) * X b * Y (i + 1 - b))
      = (∑ b ∈ Finset.range (i+1), (Nat.choose (i + 1) (b+1) : ℝ) * X (b+1) * Y (i + 1 - (b+1))) + X 0 * Y (i+1) := by
    rw [Finset.sum_range_succ']
    have h0 : (Nat.choose (i + 1) 0 : ℝ) * X 0 * Y (i + 1 - 0) = X 0 * Y (i+1) := by
      simp [Nat.choose_zero_right]
    rw [h0]
  have hS2 : (∑ b ∈ Finset.range (i+1), (Nat.choose (i + 1) (b+1) : ℝ) * X (b+1) * Y (i + 1 - (b+1)))
      = (∑ b ∈ Finset.range i, (Nat.choose (i + 1) (b+1) : ℝ) * X (b+1) * Y (i - b)) + X (i+1) * Y 0 := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      have ha' : a < i := Finset.mem_range.mp ha
      have h : i + 1 - (a+1) = i - a := by omega
      simp [h]
    · simp [Nat.choose_self]
  have hJ : (∑ a ∈ Finset.range i, (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a))
        + (∑ a ∈ Finset.range i, (Nat.choose i (a+1) : ℝ) * X (a + 1) * Y (i - a))
      = (∑ a ∈ Finset.range i, (Nat.choose (i+1) (a+1) : ℝ) * X (a + 1) * Y (i - a)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.choose_succ_succ']
    push_cast
    ring
  rw [hA, hB, hS1, hS2]
  linarith [hJ]

end Work.Spaces
end
