import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

/-- Pure real-algebra binomial estimate: if the coefficients are bounded by `D` and the
`x`-factors by `K`, then the square of the binomial sum is controlled by `((i+1)·D·K)²` times
the sum of squares of the `y`-factors.

This is the Cauchy–Schwarz step used to bound one Leibniz summand of `HkIntegrand`; it has no
analysis in it.  Note `0 ≤ D` follows from `hc` at `b = 0` (since `i.choose 0 = 1`), so it is
not a hypothesis; `0 ≤ K` is.

ROUTE.  Write `S := ∑ b ∈ Finset.range (i+1), ↑(i.choose b) * (x b * y (i-b))`.
1. `|S| ≤ (D*K) * ∑ b ∈ range (i+1), |y (i-b)|` from `Finset.abs_sum_le_sum_abs`, `abs_mul`,
   `abs_of_nonneg` on `↑(i.choose b)`, `hx`, `hc`.
2. `(∑ b ∈ range (i+1), |y (i-b)|)^2 ≤ (i+1) * ∑ b ∈ range (i+1), (y (i-b))^2` by
   `sq_sum_le_card_mul_sum_sq` (root namespace, Mathlib/Algebra/Order/Chebyshev.lean) and
   `sq_abs`.
3. `∑ b ∈ range (i+1), (y (i-b))^2 = ∑ m ∈ range (i+1), (y m)^2` by `Finset.sum_range_reflect`.
4. `(i+1)*((D*K) * (…))^2 ≤ ((i+1)*D*K)^2 * (…)` since `1 ≤ i+1`.

Only `Mathlib` is needed. -/
theorem binom_sum_sq_le {i : ℕ} {D K : ℝ} (hK : 0 ≤ K)
    {x y : ℕ → ℝ} (hx : ∀ b, b ≤ i → |x b| ≤ K)
    (hc : ∀ b, b ≤ i → |((i.choose b : ℕ) : ℝ)| ≤ D) :
    (∑ b ∈ Finset.range (i + 1), ((i.choose b : ℕ) : ℝ) * (x b * y (i - b))) ^ 2
      ≤ ((i + 1 : ℝ) * D * K) ^ 2 * ∑ m ∈ Finset.range (i + 1), (y m) ^ 2 := by
  -- `0 ≤ D`: evaluate `hc` at `b = 0`, where `i.choose 0 = 1`.
  have hD : 0 ≤ D := by
    have h := hc 0 (Nat.zero_le i)
    rw [Nat.choose_zero_right, Nat.cast_one, abs_one] at h
    exact le_trans zero_le_one h
  have hDK : 0 ≤ D * K := mul_nonneg hD hK
  set T : ℝ := ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℕ) : ℝ) * (x b * y (i - b)) with hT
  set A : ℝ := ∑ b ∈ Finset.range (i + 1), |y (i - b)| with hA
  set Q : ℝ := ∑ m ∈ Finset.range (i + 1), (y m) ^ 2 with hQ
  have hQnn : 0 ≤ Q := by
    rw [hQ]; exact Finset.sum_nonneg (fun m _ => sq_nonneg _)
  have hAnn : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg (fun b _ => abs_nonneg _)
  -- Step 1: `|T| ≤ D * K * A`.
  have h1 : |T| ≤ D * K * A := by
    rw [hT, hA]
    calc |∑ b ∈ Finset.range (i + 1), ((i.choose b : ℕ) : ℝ) * (x b * y (i - b))|
        ≤ ∑ b ∈ Finset.range (i + 1), |((i.choose b : ℕ) : ℝ) * (x b * y (i - b))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℕ) : ℝ) * |x b| * |y (i - b)| := by
          apply Finset.sum_congr rfl
          intro b _
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i.choose b))]
          ring
      _ ≤ ∑ b ∈ Finset.range (i + 1), D * K * |y (i - b)| := by
          apply Finset.sum_le_sum
          intro b hb
          have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hch : ((i.choose b : ℕ) : ℝ) ≤ D := by
            have h := hc b hbi
            rwa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i.choose b))] at h
          have hle : ((i.choose b : ℕ) : ℝ) * |x b| ≤ D * K :=
            mul_le_mul hch (hx b hbi) (abs_nonneg _) hD
          exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      _ = D * K * ∑ b ∈ Finset.range (i + 1), |y (i - b)| :=
          (Finset.mul_sum _ _ _).symm
  -- Step 2: Cauchy–Schwarz on the `A`-sum.
  have h2 : A ^ 2 ≤ (i + 1 : ℝ) * ∑ b ∈ Finset.range (i + 1), (y (i - b)) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range (i + 1)) (f := fun b => |y (i - b)|)
    rw [Finset.card_range] at h
    simp only [sq_abs] at h
    rw [hA]
    push_cast at h
    exact h
  -- Step 3: reindex `b ↦ i - b` on `range (i+1)`.
  have h3 : ∑ b ∈ Finset.range (i + 1), (y (i - b)) ^ 2 = Q := by
    rw [hQ]
    simpa using Finset.sum_range_reflect (fun m => (y m) ^ 2) (i + 1)
  have h2Q : A ^ 2 ≤ (i + 1 : ℝ) * Q := by
    rw [h3] at h2
    exact h2
  -- Combine.
  have hA2 : (D * K * A) ^ 2 ≤ (D * K) ^ 2 * ((i + 1 : ℝ) * Q) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h2Q (sq_nonneg (D * K))
  have hT2 : T ^ 2 = |T| ^ 2 := (sq_abs T).symm
  have hstep1 : T ^ 2 ≤ (D * K * A) ^ 2 := by
    rw [hT2]
    exact pow_le_pow_left₀ (abs_nonneg T) h1 2
  -- Final arithmetic: `(i+1) ≤ (i+1)^2` since `1 ≤ i+1`.
  have hone : (1 : ℝ) ≤ (i + 1 : ℝ) := by
    have : (1 : ℕ) ≤ i + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero i)
    exact_mod_cast this
  have hsq : (i + 1 : ℝ) ≤ (i + 1 : ℝ) ^ 2 := by nlinarith [hone]
  have hfin : (D * K) ^ 2 * ((i + 1 : ℝ) * Q)
      ≤ ((i + 1 : ℝ) * D * K) ^ 2 * Q := by
    calc (D * K) ^ 2 * ((i + 1 : ℝ) * Q)
        = (i + 1 : ℝ) * ((D * K) ^ 2 * Q) := by ring
      _ ≤ (i + 1 : ℝ) ^ 2 * ((D * K) ^ 2 * Q) :=
          mul_le_mul_of_nonneg_right hsq (mul_nonneg (sq_nonneg (D * K)) hQnn)
      _ = ((i + 1 : ℝ) * D * K) ^ 2 * Q := by ring
  exact le_trans hstep1 (le_trans hA2 hfin)

end Work.FTS.CoercivityFix.E2Bound
