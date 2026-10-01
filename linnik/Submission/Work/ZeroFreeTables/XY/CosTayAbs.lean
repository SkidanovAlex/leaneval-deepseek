import Mathlib
import Submission.Work.ZeroFreeTables.XY.SupGridDefs

open scoped BigOperators

namespace Work.ZeroFreeTables.XY

/-- The partial Taylor sum of `cos` is even in `θ`. -/
lemma cosTaySumNeg (θ : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * (-θ)^(2*k)/((2*k).factorial))
      = ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [Even.neg_pow (show Even (2*k) from ⟨k, by ring⟩)]

/-- `taylorWithinEval` of `cos` at the even order `2*N` is the partial Maclaurin sum,
the terms of odd order vanishing at `0`. -/
lemma cosTayEven (θ : ℝ) (hθ : 0 < θ) (N : ℕ) :
    taylorWithinEval Real.cos (2*N) (Set.Icc 0 θ) 0 θ
      = ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial) := by
  induction N with
  | zero => simp
  | succ N ih =>
      show taylorWithinEval Real.cos (2 * (N + 1)) (Set.Icc 0 θ) 0 θ
        = ∑ k ∈ Finset.range ((N + 1) + 1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)
      rw [Finset.sum_range_succ]
      rw [show 2 * (N + 1) = (2*N+1)+1 from by omega]
      rw [taylorWithinEval_succ]
      rw [taylorWithinEval_succ]
      rw [ih]
      have hodd : iteratedDerivWithin (2*N+1) Real.cos (Set.Icc 0 θ) 0 = 0 := by
        rw [Real.iteratedDerivWithin_cos_Icc (2*N+1) hθ ⟨le_refl 0, hθ.le⟩,
            Real.iteratedDeriv_odd_cos]
        simp
      have heven : iteratedDerivWithin ((2*N+1)+1) Real.cos (Set.Icc 0 θ) 0 = (-1:ℝ)^(N+1) := by
        rw [Real.iteratedDerivWithin_cos_Icc ((2*N+1)+1) hθ ⟨le_refl 0, hθ.le⟩]
        rw [show (2*N+1)+1 = 2*(N+1) from by omega]
        rw [Real.iteratedDeriv_even_cos]
        simp
      have hfac : ((↑(2*N+1) : ℝ) + 1) * ↑((2*N+1).factorial) = ↑((2*(N+1)).factorial) := by
        have h2 : (2*(N+1)).factorial = ((2*N+1)+1) * (2*N+1).factorial := by
          rw [show (2*N+1)+1 = 2*(N+1) from by omega]
          exact Nat.factorial_succ (2*N+1)
        rw [h2]
        push_cast
        ring
      rw [hodd, heven]
      simp only [smul_eq_mul, sub_zero]
      rw [show (2*N+1)+1 = 2*(N+1) from by omega, hfac, div_eq_mul_inv]
      ring

/-- `taylorWithinEval` of `cos` at the odd order `2*N+1` is the same partial Maclaurin sum. -/
lemma cosTayOdd (θ : ℝ) (hθ : 0 < θ) (N : ℕ) :
    taylorWithinEval Real.cos (2*N+1) (Set.Icc 0 θ) 0 θ
      = ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial) := by
  rw [taylorWithinEval_succ]
  rw [cosTayEven θ hθ N]
  have hodd : iteratedDerivWithin (2*N+1) Real.cos (Set.Icc 0 θ) 0 = 0 := by
    rw [Real.iteratedDerivWithin_cos_Icc (2*N+1) hθ ⟨le_refl 0, hθ.le⟩,
        Real.iteratedDeriv_odd_cos]
    simp
  rw [hodd]
  simp [smul_eq_mul]

theorem CosTayAbs (θ : ℝ) (N : ℕ) :
    |Real.cos θ - ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)|
      ≤ |θ|^(2*N+2)/((2*N+2).factorial) := by
  suffices h : ∀ θ : ℝ, 0 < θ →
      |Real.cos θ - ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)|
        ≤ |θ|^(2*N+2)/((2*N+2).factorial) by
    rcases lt_trichotomy θ 0 with hlt | heq | hgt
    · have h' := h (-θ) (by linarith)
      simpa [Real.cos_neg, cosTaySumNeg] using h'
    · rw [heq]
      have hS : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * (0:ℝ)^(2*k)/((2*k).factorial)) = 1 := by
        have h0 : ∀ k ∈ Finset.range (N+1), k ≠ 0 →
            (-1:ℝ)^k * (0:ℝ)^(2*k)/((2*k).factorial) = 0 := by
          intro k _ hk0
          rw [zero_pow (by omega : 2*k ≠ 0), mul_zero, zero_div]
        have hmem : (0:ℕ) ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.succ_pos N)
        rw [Finset.sum_eq_single (0:ℕ) h0 (fun hh => absurd hmem hh)]
        simp
      rw [hS, Real.cos_zero, sub_self, abs_zero]
      rw [zero_pow (by omega : (2:ℕ)*N+2 ≠ 0), zero_div]
    · exact h θ hgt
  intro θ hθ
  obtain ⟨x', hx'mem, hx'eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.cos) (x := θ) (x₀ := 0) (n := 2*N+1) (ne_of_lt hθ) Real.contDiff_cos.contDiffOn
  rw [Set.uIcc_of_le hθ.le] at hx'eq
  rw [show (2*N+1)+1 = 2*N+2 from by omega, sub_zero] at hx'eq
  rw [← cosTayOdd θ hθ N, hx'eq]
  have hpos : (0:ℝ) < ((2*N+2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2*N+2)
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos]
  have hd : |iteratedDeriv (2*N+2) Real.cos x'| ≤ 1 := Real.abs_iteratedDeriv_cos_le_one _ _
  calc |iteratedDeriv (2*N+2) Real.cos x'| * |θ|^(2*N+2) / ((2*N+2).factorial : ℝ)
      = |iteratedDeriv (2*N+2) Real.cos x'| * (|θ|^(2*N+2) / ((2*N+2).factorial : ℝ)) :=
        mul_div_assoc _ _ _
    _ ≤ 1 * (|θ|^(2*N+2) / ((2*N+2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
    _ = |θ|^(2*N+2) / ((2*N+2).factorial : ℝ) := by rw [one_mul]

end Work.ZeroFreeTables.XY
