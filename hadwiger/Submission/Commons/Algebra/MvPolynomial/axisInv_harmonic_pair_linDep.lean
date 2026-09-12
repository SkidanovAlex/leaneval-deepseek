import Mathlib
import Submission.Commons.Algebra.MvPolynomial.axisInv_homogeneous_structure
import Submission.Commons.Algebra.MvPolynomial.zonal_harmonic_pair_linDep

noncomputable section
open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

/-- Axis-invariant (invariance under every rotation fixing the `0`-coordinate
axis), homogeneous, harmonic polynomials of a fixed degree `k` in `n ≥ 2`
variables form a space of dimension at most one: any two of them are linearly
dependent.

Indeed, axis-invariance forces the zonal (profile) structure
`P = ∑ⱼ cⱼ • X₀^(k-2j) · (∑_{i≠0} Xᵢ²)ʲ` (`axisInv_homogeneous_structure`),
and among such zonal polynomials harmonicity leaves a single degree of
freedom (`zonal_harmonic_pair_linDep`). -/
theorem axisInv_harmonic_pair_linDep
    {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (P Q : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hQ : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapP : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0)
    (hlapQ : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0)
    (hIP : ∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        MvPolynomial.eval (fun i : Fin n => (L x) i) P =
          MvPolynomial.eval (fun i : Fin n => x i) P)
    (hIQ : ∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        MvPolynomial.eval (fun i : Fin n => (L x) i) Q =
          MvPolynomial.eval (fun i : Fin n => x i) Q) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • P + b • Q = 0 := by
  classical
  rcases axisInv_homogeneous_structure (n := n) (k := k) hn2 P hP hIP with ⟨cP, hPz⟩
  rcases axisInv_homogeneous_structure (n := n) (k := k) hn2 Q hQ hIQ with ⟨cQ, hQz⟩
  exact zonal_harmonic_pair_linDep (n := n) (k := k) hn2 P Q ⟨cP, hPz⟩ ⟨cQ, hQz⟩ hlapP hlapQ

end Commons.Algebra.MvPolynomial
