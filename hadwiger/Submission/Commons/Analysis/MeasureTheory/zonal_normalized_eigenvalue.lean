import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Submission.Commons.Analysis.MeasureTheory.pole_value_eigenvalue

noncomputable section
open scoped BigOperators Classical

set_option linter.style.haveILetI false

namespace Commons.Analysis.MeasureTheory

theorem zonal_normalized_eigenvalue
    {n : ℕ} {k : ℕ} (i : Fin n) (c : ℝ)
    (Z : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hsc : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
          ∂MeasureTheory.volume.toSphere) = c * MvPolynomial.eval (fun j : Fin n => (u : EuclideanSpace ℝ (Fin n)) j) Z)
    (hZne : MvPolynomial.eval (fun j : Fin n => ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j) Z ≠ 0) :
    c = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
          ∂MeasureTheory.volume.toSphere) /
        MvPolynomial.eval (fun j : Fin n => ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j) Z := by
  classical
  let eS : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨EuclideanSpace.single i (1 : ℝ), by
      rw [mem_sphere_zero_iff_norm]
      simp [EuclideanSpace.single]⟩
  have hA : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
          ∂MeasureTheory.volume.toSphere) =
        c * MvPolynomial.eval (fun j : Fin n => ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j) Z := by
    simpa [eS] using hsc eS
  rw [hA]
  field_simp [hZne]

end Commons.Analysis.MeasureTheory