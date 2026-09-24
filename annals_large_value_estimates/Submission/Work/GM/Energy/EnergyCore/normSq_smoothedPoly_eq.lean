import Mathlib
import Submission.Work.GM.Energy.Defs

/-!
# `‖D(u)‖²` expanded as a double sum (GM §11)

Writing `D = smoothedPoly N b`, the square of the modulus of `D(u)` is the double sum
over `n₁, n₂ ∈ [N,2N]` of the coefficients times `(n₁/n₂)^{iu}`:

`normSq (D u) = (∑_{n₁} ∑_{n₂} w(n₁/N) w(n₂/N) b_{n₁} conj(b_{n₂}) (n₁/n₂)^{iu}).re`.

This is the algebraic identity used to pass from `|D|²` to the exponential sums `R(n₁/n₂)`
in the energy estimates of §11.
-/

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Energy.EnergyCore

/-- The elementary complex-power identity behind the expansion of `normSq (D u)`:
`m^{iu} · conj(n^{iu}) = (m/n)^{iu}` for natural `m, n`. -/
lemma cpow_mul_conj_cpow (m n : ℕ) (u : ℝ) :
    (m : ℂ) ^ (Complex.I * (u : ℂ)) * (starRingEnd ℂ) ((n : ℂ) ^ (Complex.I * (u : ℂ)))
      = (((m : ℝ) / (n : ℝ)) : ℂ) ^ (Complex.I * (u : ℂ)) := by
  rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n]
  have harg : (((n : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  have hcj : (starRingEnd ℂ) (Complex.I * (u : ℂ)) = -(Complex.I * (u : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  have hconj : (starRingEnd ℂ) (((n : ℝ) : ℂ) ^ (Complex.I * (u : ℂ)))
      = (((n : ℝ) : ℂ) ^ (-(Complex.I * (u : ℂ)))) := by
    have h := Complex.cpow_conj (((n : ℝ) : ℂ)) (Complex.I * (u : ℂ)) harg
    simp only [Complex.conj_ofReal] at h
    rw [hcj] at h
    exact h.symm
  rw [hconj, Complex.cpow_neg, ← div_eq_mul_inv,
      ← Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
        (Complex.I * (u : ℂ))]

theorem normSq_smoothedPoly_eq (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (u : ℝ) :
    Complex.normSq (Submission.LargeValues.smoothedPoly N b u)
      = (∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
          ((Submission.LargeValues.bumpW ((n1 : ℝ) / (N : ℝ))) : ℂ)
            * ((Submission.LargeValues.bumpW ((n2 : ℝ) / (N : ℝ))) : ℂ)
            * b n1 * (starRingEnd ℂ) (b n2)
            * (((n1 : ℝ) / (n2 : ℝ)) : ℂ) ^ (Complex.I * (u : ℂ))).re := by
  rw [Submission.LargeValues.smoothedPoly]
  set S := ∑ n ∈ Finset.Icc N (2 * N),
      ((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ))) : ℂ) * b n
        * (n : ℂ) ^ (Complex.I * (u : ℂ)) with hS
  have hnorm : Complex.normSq S = (S * (starRingEnd ℂ) S).re := by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [hnorm]
  have hmain : S * (starRingEnd ℂ) S
      = ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
          ((Submission.LargeValues.bumpW ((n1 : ℝ) / (N : ℝ))) : ℂ)
            * ((Submission.LargeValues.bumpW ((n2 : ℝ) / (N : ℝ))) : ℂ)
            * b n1 * (starRingEnd ℂ) (b n2)
            * (((n1 : ℝ) / (n2 : ℝ)) : ℂ) ^ (Complex.I * (u : ℂ)) := by
    rw [hS, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n1 _ => Finset.sum_congr rfl fun n2 _ => ?_
    rw [map_mul, map_mul, Complex.conj_ofReal, ← cpow_mul_conj_cpow]
    ring
  rw [hmain]

end Work.GM.Energy.EnergyCore
