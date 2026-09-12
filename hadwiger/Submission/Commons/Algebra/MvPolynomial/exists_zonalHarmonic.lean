import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Algebra.MvPolynomial.homogeneous_decompose
import Submission.Commons.Algebra.MvPolynomial.harmonic_X2_intersection

open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

/-- The linear form `a · x` is homogeneous of degree one. -/
private lemma linearForm_isHomogeneous_one {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) :
    ((∑ i : Fin n, (MvPolynomial.C (a i)) * (MvPolynomial.X i)) :
      MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
  classical
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i : Fin n => (MvPolynomial.C (a i)) * (MvPolynomial.X i)) 1 ?_
  intro i hi
  exact MvPolynomial.IsHomogeneous.mul (MvPolynomial.isHomogeneous_C (Fin n) (a i))
    (MvPolynomial.isHomogeneous_X ℝ i)

theorem exists_zonalHarmonic
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)] (a : EuclideanSpace ℝ (Fin n)) :
    ∃ (Z : MvPolynomial (Fin n) ℝ) (R : MvPolynomial (Fin n) ℝ),
      Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Z)) = 0 ∧
      R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) ∧
      ((∑ i : Fin n, (MvPolynomial.C (a i)) * (MvPolynomial.X i)) ^ k) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R := by
  classical
  let L : MvPolynomial (Fin n) ℝ :=
    ∑ i : Fin n, (MvPolynomial.C (a i)) * (MvPolynomial.X i)
  have hL1 : L.IsHomogeneous 1 := by
    dsimp [L]
    exact linearForm_isHomogeneous_one a
  have hmem : L ^ k ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa using hL1.pow k
  rcases homogeneous_decompose (n := n) (k := k) (P := L ^ k) hmem with
    ⟨Z, R, hZ, hR, hlZ, hEq⟩
  refine ⟨Z, R, hZ, hlZ, hR, ?_⟩
  dsimp [L] at hEq
  exact hEq

end Commons.Algebra.MvPolynomial