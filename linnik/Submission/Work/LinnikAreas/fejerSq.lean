import Mathlib
import Submission.Work.LinnikAreas.TFDefs
import Submission.Work.LinnikAreas.cosSinMulSum
import Submission.Work.LinnikAreas.rangeIccSplit

/-!
# Non-negativity of the Fejér kernel at `r = 1`

`Kfun r θ N = 1 + 2 * Σ_{1 ≤ m ≤ N-1} (1 - m/N) * r^m * cos (mθ)` is the real form of the
Fejér kernel.  Here we prove the classical fact that at `r = 1` it is non-negative:

  `N * Kfun 1 θ N = (Σ_{m<N} cos mθ)^2 + (Σ_{m<N} sin mθ)^2`   (`N ≥ 1`),

which exhibits `Kfun 1 θ N` as `1/N` times a sum of two squares.  The identity is obtained by
induction on `N`; the inductive step is the addition formula
`cos mθ cos Nθ + sin mθ sin Nθ = cos ((N-m)θ)` (`cosSinMulSum`) together with the reflection
`m ↦ N - m` of the summation index.
-/

namespace Work.LinnikAreas

/-- Key sum-of-squares identity for the Fejér kernel at `r = 1`:
`2 * Σ_{m<N} (N-m) * cos (mθ) - N = (Σ_{m<N} cos mθ)^2 + (Σ_{m<N} sin mθ)^2`. -/
theorem fejerKey (θ : ℝ) : ∀ N : ℕ,
    2 * (∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ)) - (N : ℝ)
      = (∑ m ∈ Finset.range N, Real.cos ((m : ℝ) * θ)) ^ 2
        + (∑ m ∈ Finset.range N, Real.sin ((m : ℝ) * θ)) ^ 2 := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    -- Peel off the last term of the weighted sum and split off the linear part.
    have hstep : (∑ m ∈ Finset.range n, ((↑(n + 1) : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ))
        = (∑ m ∈ Finset.range n, ((n : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ))
          + (∑ m ∈ Finset.range n, Real.cos ((m : ℝ) * θ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      have h1 : ((↑(n + 1) : ℝ) - (m : ℝ)) = ((n : ℝ) - (m : ℝ)) + 1 := by push_cast; ring
      rw [h1, add_mul, one_mul]
    have htop : ((↑(n + 1) : ℝ) - (↑n : ℝ)) = 1 := by push_cast; ring
    have hcast : ((↑(n + 1) : ℝ)) = (↑n : ℝ) + 1 := by push_cast; ring
    rw [hstep, htop, one_mul, hcast]
    -- The telescoping identity `Σ_{m<n} cos ((m+1)θ) + 1 = Σ_{m<n} cos mθ + cos nθ`.
    have hTc : (∑ m ∈ Finset.range n, Real.cos (((m + 1 : ℕ) : ℝ) * θ)) + 1
        = (∑ m ∈ Finset.range n, Real.cos ((m : ℝ) * θ)) + Real.cos ((n : ℝ) * θ) := by
      have h := Finset.sum_range_succ (fun k : ℕ => Real.cos ((k : ℝ) * θ)) n
      rw [Finset.sum_range_succ'] at h
      simpa using h
    have hmul := cosSinMulSum θ n
    nlinarith [Real.cos_sq_add_sin_sq ((n : ℝ) * θ)]

/-- **The Fejér kernel at `r = 1` is non-negative.** -/
theorem fejerSq (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) :
    0 ≤ Kfun 1 θ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbridge := rangeIccSplit θ N hN
  have hkey := fejerKey θ N
  -- `N * (1 - m / N) = N - m`, so `N` times the `Icc` sum is the weighted range sum.
  have h2 : ∀ m : ℕ, (N : ℝ) * (1 - (m : ℝ) / N) = (N : ℝ) - (m : ℝ) := fun m => by
    field_simp
  have hA : (N : ℝ) * (1 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1),
        (1 - (m : ℝ) / N) * 1 ^ m * Real.cos ((m : ℝ) * θ))
      = (N : ℝ) + 2 * ∑ m ∈ Finset.Icc 1 (N - 1),
          ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ) := by
    rw [mul_add, mul_one]
    congr 1
    rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [one_pow, mul_one, ← h2 m]
    ring
  have hB : (N : ℝ) + 2 * ∑ m ∈ Finset.Icc 1 (N - 1),
        ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ)
      = 2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ)
        - (N : ℝ) := by
    rw [hbridge]; ring
  have hNK : (N : ℝ) * Kfun 1 θ N
      = 2 * (∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * Real.cos ((m : ℝ) * θ))
        - (N : ℝ) := by
    unfold Kfun
    rw [hA, hB]
  have hnn : (0 : ℝ) ≤ (N : ℝ) * Kfun 1 θ N := by
    rw [hNK, hkey]
    positivity
  exact nonneg_of_mul_nonneg_right hnn hNpos

end Work.LinnikAreas
