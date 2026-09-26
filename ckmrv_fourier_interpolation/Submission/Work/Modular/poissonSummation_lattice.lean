import Mathlib
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.Poisson.Main

/-!
# Poisson summation for a lattice in `ℝⁿ`
-/

namespace Work.Modular

open Work.Modular
open scoped FourierTransform SchwartzMap

/-- **Poisson summation for a lattice**: for a discrete lattice `Λ ⊆ ℝⁿ` spanning `ℝⁿ` and a
Schwartz function `f`,
`∑_{x ∈ Λ} f x = (1 / vol Λ) ∑_{y ∈ Λ*} f̂ y`,
where `Λ*` is the dual lattice `{y | ⟪y, x⟫ ∈ ℤ ∀ x ∈ Λ}`, `vol Λ` is the covolume of `Λ`, and
`f̂` is the Fourier transform with `f̂ (y) = ∫ x, exp (-2 π i ⟪y, x⟫) f x`. -/
theorem poissonSummation_lattice {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∑' x : L, f x = (covolume L)⁻¹ *
      ∑' y : dualLattice L, FourierTransform.fourierCLM ℂ
        (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f y := by
  simpa only [FourierTransform.fourierCLM_apply] using poissonSummation_lattice_gen L hspan f

end Work.Modular
