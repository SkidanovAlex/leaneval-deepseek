import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval

namespace Commons.NumberTheory.Polynomial

/-- The integers lying in the closed real interval with (real) endpoints `⌈-r⌉`
and `⌊r⌋` are exactly those whose absolute value is at most `r`. -/
lemma fmcl_aux_mem_Icc_int {z : ℤ} {r : ℝ} (h : |(z : ℝ)| ≤ r) :
    z ∈ Finset.Icc ⌈-r⌉ ⌊r⌋ := by
  rw [Finset.mem_Icc]
  exact ⟨Int.ceil_le.mpr (abs_le.mp h).1, Int.le_floor.mpr (abs_le.mp h).2⟩

/-- For any real `r` there are only finitely many integers whose absolute value
is at most `r`. -/
lemma fmcl_aux_finite_int_abs_le (r : ℝ) : {z : ℤ | |(z : ℝ)| ≤ r}.Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc ⌈-r⌉ ⌊r⌋))
  intro z hz
  exact fmcl_aux_mem_Icc_int hz

/-- The set of monic integer polynomials of fixed degree `n` whose coefficients
`0, …, n` are bounded in absolute value by prescribed real bounds `B` is
finite. -/
theorem finite_monic_poly_coeff_le {n : ℕ} (B : ℕ → ℝ) :
    {P : Polynomial ℤ | P.Monic ∧ P.natDegree = n ∧
      ∀ i ≤ n, |((P.coeff i : ℤ) : ℝ)| ≤ B i}.Finite := by
  -- For each `i : Fin (n+1)` the possible values of the `i`-th coefficient.
  set F : Fin (n + 1) → Finset ℤ := fun i => Finset.Icc ⌈-(B i)⌉ ⌊B i⌋ with hF
  -- The target set injects (via its coefficient vector) into the finite product
  -- `Fintype.piFinset F`.
  refine Set.Finite.subset
    (Finset.finite_toSet (Finset.image
      (fun q : Fin (n + 1) → ℤ => ∑ i, Polynomial.C (q i) * Polynomial.X ^ (i : ℕ))
      (Fintype.piFinset F))) ?_
  intro P hP
  rw [Finset.mem_coe]
  rcases hP with ⟨hmonic, hdeg, hbound⟩
  refine Finset.mem_image.mpr ⟨fun i => P.coeff (i : ℕ), ?_, ?_⟩
  · -- The coefficient vector of `P` lies in the product of the bounded sets.
    rw [Fintype.mem_piFinset]
    intro i
    exact fmcl_aux_mem_Icc_int (hbound (i : ℕ) (Nat.lt_succ_iff.mp i.isLt))
  · -- Since `P.natDegree = n`, `P` is recovered from its first `n+1` coefficients.
    show (∑ i : Fin (n + 1), Polynomial.C (P.coeff (i : ℕ)) * Polynomial.X ^ (i : ℕ)) = P
    have h := _root_.Polynomial.as_sum_range_C_mul_X_pow P
    rw [hdeg] at h
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (P.coeff i) * Polynomial.X ^ i) (n + 1)]
    exact h.symm

end Commons.NumberTheory.Polynomial