import Mathlib
import Submission.Commons.Analysis.MeasureTheory.cosine_harmonic_scalar

noncomputable section
open scoped BigOperators Classical

set_option linter.style.haveILetI false

namespace Commons.Analysis.MeasureTheory

theorem pole_value_eigenvalue
    {n : ℕ} {k : ℕ} (i : Fin n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hdec : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) * (MvPolynomial.X j)) ^ k) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    ∃ c : ℝ,
      (∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
          ∂MeasureTheory.volume.toSphere) = c * MvPolynomial.eval (fun j : Fin n => (u : EuclideanSpace ℝ (Fin n)) j) Z) ∧
      ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
          ∂MeasureTheory.volume.toSphere) =
        c * MvPolynomial.eval (fun j : Fin n => ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) Z) := by
  classical
  haveI : Nonempty (Fin n) := ⟨i⟩
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ := fun θ =>
    MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
  have hg : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) = 0 ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g θ = MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) P := by
    refine ⟨Z, hZmem, hlapZ, ?_⟩
    intro θ
    rfl
  rcases cosine_harmonic_scalar (n := n) (k := k) (g := g) hg with ⟨c, hmain⟩
  refine ⟨c, ?_, ?_⟩
  · intro u
    have hu := hmain u
    simpa [g] using hu
  · let eS : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨EuclideanSpace.single i (1 : ℝ), by
        rw [mem_sphere_zero_iff_norm]
        simp [EuclideanSpace.single]⟩
    have he := hmain eS
    simpa [g, eS] using he

end Commons.Analysis.MeasureTheory
