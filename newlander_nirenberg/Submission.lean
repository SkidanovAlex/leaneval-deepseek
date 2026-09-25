import ChallengeDeps
import Submission.Helpers
import Submission.Crux
import Submission.Work.Complex.standardForm

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

theorem newlander_nirenberg {n : ℕ} {U : Set (E n)} (_hU : IsOpen U)
    (J : E n → E n →L[ℝ] E n) (_hJ : IsAlmostComplexOn J U)
    (_hN : NijenhuisVanishesOn J U) {x : E n} (_hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (EuclideanSpace ℂ (Fin n)),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → EuclideanSpace ℂ (Fin n)) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : EuclideanSpace ℂ (Fin n) → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → EuclideanSpace ℂ (Fin n)) y (J y v)
          = Complex.I • fderiv ℝ (φ : E n → EuclideanSpace ℂ (Fin n)) y v := by
  have hstd : ∃ T : E n ≃L[ℝ] F n, ∀ v, T (J x v) = Complex.I • T v :=
    Work.Complex.standardForm (J x) (_hJ.2 x _hx)
  obtain ⟨V, hVopen, hxV, hVU, u, hu, hhol, hinv⟩ := nn_core _hU _hJ _hN _hx hstd
  exact exists_chart_of_holomorphic hVopen hVU J hxV u hu hhol hinv

end Submission
