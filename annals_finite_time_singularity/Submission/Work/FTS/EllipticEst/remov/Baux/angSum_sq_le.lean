import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.remov.Baux.SliceAngRoomDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `angSum_sq_le`

A binomial-convolution square bound.  With `c_j = (k+1).choose j` and
`d_j = sin^{(k+1-j)}(θ)` (the `k+1-j`-st iterated derivative of `sin` at `θ`),
Cauchy–Schwarz gives

  `(Σ_j c_j d_j x_j)² ≤ (Σ_j (c_j d_j)²)·(Σ_j x_j²)`,

and since `|sin^{(m)}(θ)| ≤ 1` for every `m` (`Real.abs_iteratedDeriv_sin_le_one`) and
`Σ_j c_j² ≤ (Σ_j c_j)² = (2^{k+1})²` (binomial theorem, all terms nonnegative) this is

  `(Σ_j c_j d_j x_j)² ≤ (2^{k+1})²·(Σ_j x_j²) ≤ (2^{k+1})²·(k+2)·(Σ_j x_j²)`,

which is the statement.
-/

namespace Work.FTS.EllipticEst.remov.Baux

theorem angSum_sq_le (k : ℕ) (x : ℕ → ℝ) (θ : ℝ) :
    (∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
        * iteratedDeriv (k + 1 - j) Real.sin θ * x j) ^ 2
      ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2)
          * ∑ j ∈ Finset.range (k + 2), (x j) ^ 2 := by
  classical
  set t := Finset.range (k + 2) with ht
  -- The binomial sum `Σ_j (k+1).choose j = 2^{k+1}`.
  have hrange : Finset.range (k + 1 + 1) = t := by rw [ht]
  have hchoose : ∑ j ∈ t, ((k + 1).choose j : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [← hrange, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  -- Pointwise: `(c_j·d_j)² ≤ c_j²` since `|d_j| ≤ 1`.
  have hterm : ∀ j ∈ t, (((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2
      ≤ ((k + 1).choose j : ℝ) ^ 2 := by
    intro j hj
    rw [mul_pow]
    have hd : (iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (Real.abs_iteratedDeriv_sin_le_one _ _)
    simpa using mul_le_mul_of_nonneg_left hd (sq_nonneg ((k + 1).choose j : ℝ))
  -- `Σ_j c_j² ≤ (2^{k+1})²`.
  have hsum_sq :
      ∑ j ∈ t, (((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2
        ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsingle : ∀ j ∈ t, ((k + 1).choose j : ℝ) ^ 2
        ≤ ((k + 1).choose j : ℝ) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) := by
      intro j hj
      have hle : ((k + 1).choose j : ℝ) ≤ ∑ i ∈ t, ((k + 1).choose i : ℝ) :=
        Finset.single_le_sum (f := fun i => ((k + 1).choose i : ℝ))
          (fun i _ => Nat.cast_nonneg _) hj
      calc ((k + 1).choose j : ℝ) ^ 2
          = ((k + 1).choose j : ℝ) * ((k + 1).choose j : ℝ) := by ring
        _ ≤ ((k + 1).choose j : ℝ) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) :=
            mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    calc ∑ j ∈ t, ((k + 1).choose j : ℝ) ^ 2
        ≤ ∑ j ∈ t, ((k + 1).choose j : ℝ) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) :=
          Finset.sum_le_sum hsingle
      _ = (∑ j ∈ t, ((k + 1).choose j : ℝ)) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) := by
          rw [Finset.sum_mul]
      _ = ((2 : ℝ) ^ (k + 1)) ^ 2 := by rw [hchoose]; ring
  have hX : 0 ≤ ∑ j ∈ t, (x j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hk2 : (1 : ℝ) ≤ (k : ℝ) + 2 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- Cauchy–Schwarz and the small bookkeeping for the factor `k+2 ≥ 1`.
  calc (∑ j ∈ t, ((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ * x j) ^ 2
      ≤ (∑ j ∈ t, (((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2)
          * ∑ j ∈ t, (x j) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq t _ x
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ∑ j ∈ t, (x j) ^ 2 :=
        mul_le_mul_of_nonneg_right hsum_sq hX
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * (((k : ℝ) + 2) * ∑ j ∈ t, (x j) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ j ∈ t, (x j) ^ 2 = (∑ j ∈ t, (x j) ^ 2) * 1 := by ring
          _ ≤ (∑ j ∈ t, (x j) ^ 2) * ((k : ℝ) + 2) := mul_le_mul_of_nonneg_left hk2 hX
          _ = ((k : ℝ) + 2) * ∑ j ∈ t, (x j) ^ 2 := by ring
    _ = ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * ∑ j ∈ t, (x j) ^ 2 := by ring

end Work.FTS.EllipticEst.remov.Baux
