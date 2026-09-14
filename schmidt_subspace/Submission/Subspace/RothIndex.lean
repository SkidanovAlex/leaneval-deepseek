import Mathlib
import Submission.Subspace.Index
import Submission.Subspace.IndexDet

/-!
# Index estimates for the Wronskians of Roth's lemma

This file contains the *index* half of the proof of the classical multivariate Roth lemma
(survey arXiv:2502.00731, §"Roth's lemma"); the height half lives in the commons.

The two ingredients are

* `index_det_pderivIter_ge`: the index of a `k × k` determinant whose `(i,j)`-entry is
  `C (cst i j) * ∂^{ν i j} P` is at least `∑ j, (Ind P - q j)`, where `q j` is any upper bound
  for `∑ₜ νᵢⱼₜ/rₜ` (this is Schmidt's "index of a Wronskian" bound, obtained from
  `index_det_ge_min` together with the differentiation inequality);

* `index_det_wronskian_ge`: the specialisation used in the proof, where
  `ν i j = μᵢ + j·e_m`; then `q j = B + j/r m`.
-/

open scoped BigOperators

namespace Submission.Subspace

open Commons.Algebra.MvPolynomial (indexWt indexTay indexSet pderivIter)

variable {σ : Type*} [Fintype σ]

/-- **The index of a determinant of iterated derivatives.**  If every entry of the `j`-th column
of a `k × k` matrix has the form `C (cst i j) * ∂^{ν i j} P` with `cst i j ≠ 0` and
`∑ₜ νᵢⱼₜ/rₜ ≤ q j`, and if the determinant does not vanish, then
`∑ j, (Ind P - q j) ≤ Ind (det)`. -/
theorem index_det_pderivIter_ge {K : Type*} [Field K] [CharZero K] {k : ℕ}
    (α : σ → K) (r : σ → ℕ) (P : MvPolynomial σ K)
    (ν : Fin k → Fin k → σ →₀ ℕ) (cst : Fin k → Fin k → K)
    (hcast : ∀ i j, cst i j ≠ 0) (q : Fin k → ℝ)
    (hq : ∀ i j, indexWt r (ν i j) ≤ q j)
    (hdet : (Matrix.of fun i j => MvPolynomial.C (cst i j) * pderivIter (ν i j) P).det ≠ 0) :
    ∑ j, (index α r P - q j) ≤
      index α r (Matrix.of fun i j => MvPolynomial.C (cst i j) * pderivIter (ν i j) P).det := by
  classical
  set A : Matrix (Fin k) (Fin k) (MvPolynomial σ K) :=
    Matrix.of (fun i j => MvPolynomial.C (cst i j) * pderivIter (ν i j) P) with hA
  have hdetA : A.det ≠ 0 := hdet
  refine index_det_ge_min A hdetA (fun j => index α r P - q j) fun i j hne => ?_
  have h1 : pderivIter (ν i j) P ≠ 0 := fun h0 => hne (by rw [hA, Matrix.of_apply, h0, mul_zero])
  have h2 : index α r (A i j) = index α r (pderivIter (ν i j) P) := by
    rw [hA, Matrix.of_apply]
    exact index_C_mul α r _ (hcast i j) _ h1
  rw [h2]
  have h3 := index_sub_indexWt_le_index_pderivIter α r (ν i j) P h1
  linarith [hq i j]

/-- The weighted value of the single monomial `t · e_m`. -/
lemma indexWt_smul_single (r : σ → ℕ) (m : σ) (t : ℕ) :
    indexWt r (t • Finsupp.single m 1) = (t : ℝ) / (r m : ℝ) := by
  rw [indexWt]
  rw [Finset.sum_eq_single m]
  · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro i _ hi
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hi, smul_zero, Nat.cast_zero, zero_div]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- The weighted value of `μ + t · e_m`. -/
lemma indexWt_add_smul_single (r : σ → ℕ) (m : σ) (μ : σ →₀ ℕ) (t : ℕ) :
    indexWt r (μ + t • Finsupp.single m 1) = indexWt r μ + (t : ℝ) / (r m : ℝ) := by
  rw [indexWt_add, indexWt_smul_single]

/-- **Index of the Wronskian of a decomposition.**  Specialisation of
`index_det_pderivIter_ge` to the differential operators `ν i j = μᵢ + j·e_m`, which is the
matrix appearing in the proof of Roth's lemma. -/
theorem index_det_wronskian_ge {K : Type*} [Field K] [CharZero K] {k : ℕ}
    (α : σ → K) (r : σ → ℕ) (P : MvPolynomial σ K) (m : σ)
    (μ : Fin k → σ →₀ ℕ) (B : ℝ) (hμ : ∀ i, indexWt r (μ i) ≤ B)
    (cst : Fin k → Fin k → K) (hcst : ∀ i j, cst i j ≠ 0)
    (hdet : (Matrix.of (fun i j => MvPolynomial.C (cst i j) *
        pderivIter (μ i + (j : ℕ) • Finsupp.single m 1) P)).det ≠ 0) :
    ∑ j : Fin k, (index α r P - B - (j : ℝ) / (r m : ℝ)) ≤
      index α r (Matrix.of (fun i j => MvPolynomial.C (cst i j) *
        pderivIter (μ i + (j : ℕ) • Finsupp.single m 1) P)).det := by
  have h := index_det_pderivIter_ge α r P
    (fun i j => μ i + (j : ℕ) • Finsupp.single m 1) cst hcst
    (fun j => B + (j : ℝ) / (r m : ℝ)) (fun i j => by
      rw [indexWt_add_smul_single]; linarith [hμ i]) hdet
  refine le_trans ?_ h
  refine Finset.sum_le_sum fun j _ => ?_
  rw [sub_sub]

end Submission.Subspace

namespace Submission.Subspace

open Commons.Algebra.MvPolynomial (indexWt indexTay indexSet pderivIter)

variable {σ : Type*} [Fintype σ]

/-- If `∂^m P ≠ 0` then `m i ≤ degreeOf i P` for every variable `i`: the support of an iterated
partial derivative is contained in the translate of the support of `P`. -/
lemma le_degreeOf_of_pderivIter_ne_zero {R : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) (P : MvPolynomial σ R) (h : pderivIter m P ≠ 0) (i : σ) :
    m i ≤ P.degreeOf i := by
  classical
  obtain ⟨n, hn⟩ := MvPolynomial.support_nonempty.mpr h
  rw [MvPolynomial.mem_support_iff, Commons.Algebra.MvPolynomial.coeff_pderivIter] at hn
  have h1 : MvPolynomial.coeff (n + m) P ≠ 0 := fun h0 => hn (by rw [h0, zero_mul])
  have h2 : (∏ j : σ, ((n + m) j).descFactorial (m j)) ≠ 0 :=
    fun h0 => hn (by rw [h0, Nat.cast_zero, mul_zero])
  have h3 : ((n + m) i).descFactorial (m i) ≠ 0 :=
    fun h0 => h2 (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have h4 : m i ≤ (n + m) i := by
    by_contra hlt
    exact h3 (Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_le hlt))
  have h5 : (n + m) ∈ P.support := MvPolynomial.mem_support_iff.mpr h1
  calc m i ≤ (n + m) i := h4
    _ ≤ P.degreeOf i := MvPolynomial.monomial_le_degreeOf i h5

/-- **The index is at most the weighted total degree** (survey, §"Index", the remark
`Ind ≤ m`). -/
lemma index_le_sum_degree_div {K : Type*} [Field K] [CharZero K]
    (α : σ → K) (r : σ → ℕ) (P : MvPolynomial σ K) :
    index α r P ≤ ∑ i, (P.degreeOf i : ℝ) / (r i : ℝ) := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · rw [index_zero]
    exact Finset.sum_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨m, hm, hEq, -⟩ := index_eq_indexWt_of_min α r P hP
  have hmdeg : ∀ i, m i ≤ P.degreeOf i := by
    intro i
    have hcoeff : MvPolynomial.coeff m (indexTay α P) ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    have hder : pderivIter m P ≠ 0 := by
      intro h0
      have h1 : MvPolynomial.coeff 0 (pderivIter m (indexTay α P)) ≠ 0 := by
        rw [Commons.Algebra.MvPolynomial.coeff_pderivIter]
        simp only [zero_add]
        refine mul_ne_zero hcoeff ?_
        exact Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun j _ => by
          rw [Nat.descFactorial_self]
          exact Nat.factorial_ne_zero (m j)))
      have h2 : pderivIter m (indexTay α P) ≠ 0 := fun h0 =>
        h1 (by rw [h0, MvPolynomial.coeff_zero])
      rw [← Commons.Algebra.MvPolynomial.indexTay_pderivIter α m P, h0] at h2
      exact h2 (by simp [Commons.Algebra.MvPolynomial.indexTay])
    exact le_degreeOf_of_pderivIter_ne_zero m P hder i
  rw [hEq, indexWt]
  exact Finset.sum_le_sum fun i _ =>
    div_le_div_of_nonneg_right (by exact_mod_cast hmdeg i) (Nat.cast_nonneg _)

end Submission.Subspace
