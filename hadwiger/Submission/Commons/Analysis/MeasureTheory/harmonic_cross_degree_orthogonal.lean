import Mathlib
import Submission.Commons.Algebra.MvPolynomial.lapIter_mul_eq_zero_of_harmonic
import Submission.Commons.Analysis.MeasureTheory.homogeneous_even_sphere_integral_eq_const_laplacian_pow
import Submission.Commons.Analysis.MeasureTheory.odd_degree_homogeneous_sphere_integral_zero

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Commons.Analysis.MeasureTheory

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev S (n : ℕ) := Metric.sphere (0 : E n) 1

/-- Harmonic homogeneous polynomials of different degrees are orthogonal on the
unit sphere: if `P` is harmonic homogeneous of degree `k` and `Q` harmonic
homogeneous of degree `l` with `k ≠ l`, then the integral of `P · Q` over the
sphere vanishes.

Proof outline: the product `P·Q` is homogeneous of degree `k + l`.  If that
total degree is odd, the integral vanishes by parity.  Otherwise
`k + l = 2m`, and the Pizzetti formula
(`homogeneous_even_sphere_integral_eq_const_laplacian_pow`) reduces the
integral to `c • (Δ^[m] (P·Q)) (0)`.  The algebraic lemma
`Commons.Algebra.MvPolynomial.lapIter_mul_eq_zero_of_harmonic` shows
`Δ^[m] (P·Q) = 0` outright (the iterated Laplacian over-differentiates the
lower-degree harmonic factor), whence the integral is zero. -/
theorem harmonic_cross_degree_orthogonal
    {n : ℕ} {k l : ℕ} [Nonempty (Fin n)] (hkl : k ≠ l)
    (P Q : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hQ : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ l)
    (hlapP : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0)
    (hlapQ : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P) *
        (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) Q)
      ∂MeasureTheory.volume.toSphere) = 0 := by
  classical
  have hnpos : 0 < n := by
    have hc : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)›
    simpa using hc
  let R : MvPolynomial (Fin n) ℝ := P * Q
  have hReval : (fun θ : S n =>
        (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P) *
        (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) Q)) =
      fun θ : S n => MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) R := by
    funext θ
    simp [R, MvPolynomial.eval_mul]
  rw [hReval]
  have hR : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k + l) := by
    dsimp [R]
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.IsHomogeneous.mul
      (by rwa [MvPolynomial.mem_homogeneousSubmodule] at hP)
      (by rwa [MvPolynomial.mem_homogeneousSubmodule] at hQ)
  by_cases hodd : Odd (k + l)
  · exact odd_degree_homogeneous_sphere_integral_zero hodd R hR
  · have hEven : Even (k + l) := Nat.not_odd_iff_even.mp hodd
    obtain ⟨m, hm⟩ := hEven
    have hm' : k + l = 2 * m := by omega
    have hR2m : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) := by
      simpa [hm'] using hR
    obtain ⟨c, hc⟩ := homogeneous_even_sphere_integral_eq_const_laplacian_pow
      (n := n) (m := m) hnpos
    have hint := hc R hR2m
    have hz : ((fun X : MvPolynomial (Fin n) ℝ =>
          ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i X))^[m]) R = 0 := by
      dsimp [R]
      exact Commons.Algebra.MvPolynomial.lapIter_mul_eq_zero_of_harmonic P Q hP hQ hlapP hlapQ hm' hkl
    calc
      (∫ θ : S n, MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) R
          ∂MeasureTheory.volume.toSphere)
          = c * MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
              ((fun X : MvPolynomial (Fin n) ℝ =>
                  ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i X))^[m] R) := hint
      _ = c * 0 := by rw [hz]; simp
      _ = 0 := by ring

end Commons.Analysis.MeasureTheory
