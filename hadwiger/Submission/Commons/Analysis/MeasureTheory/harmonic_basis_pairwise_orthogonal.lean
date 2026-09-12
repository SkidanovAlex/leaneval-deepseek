import Mathlib
import Submission.Commons.Analysis.MeasureTheory.harmonic_cross_degree_orthogonal

namespace Commons.Analysis.MeasureTheory

/-- Two harmonic homogeneous polynomials of different degrees are orthogonal on
the unit sphere (proved in `harmonic_cross_degree_orthogonal`).  Consequently,
an orthonormal family of harmonic polynomials organized by degree is pairwise
orthogonal across distinct degrees: for `k ≠ l` the integral of `Y k i · Y l j`
over the sphere vanishes. -/
theorem harmonic_basis_pairwise_orthogonal
    {n : ℕ} [Nonempty (Fin n)]
    (d : ℕ → ℕ) (Y : ∀ k : ℕ, Fin (d k) → MvPolynomial (Fin n) ℝ)
    (hY : ∀ k : ℕ,
      (∀ j : Fin (d k), Y k j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (Y k j))) = 0) ∧
      (∀ i j : Fin (d k),
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k i) *
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j)
          ∂MeasureTheory.volume.toSphere) = if i = j then 1 else 0)) :
    ∀ k l : ℕ, k ≠ l → ∀ i : Fin (d k), ∀ j : Fin (d l),
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          MvPolynomial.eval (fun m : Fin n => (θ : EuclideanSpace ℝ (Fin n)) m) (Y k i) *
          MvPolynomial.eval (fun m : Fin n => (θ : EuclideanSpace ℝ (Fin n)) m) (Y l j)
        ∂MeasureTheory.volume.toSphere) = 0 := by
  intro k l hkl i j
  have hk := (hY k).1 i
  have hl := (hY l).1 j
  exact harmonic_cross_degree_orthogonal hkl (Y k i) (Y l j) hk.1 hl.1 hk.2 hl.2

end Commons.Analysis.MeasureTheory
