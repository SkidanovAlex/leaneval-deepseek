/-
# The `n = 1` Newlander--Nirenberg theorem

This file assembles the `n = 1` case of the Newlander--Nirenberg theorem from

* `Work.Beltrami.localHolInput_of_cauchyEstimates` (the local Beltrami solution, via
  `Work.Beltrami.exists_hol_of_beltrami_global` and the standard-form reduction), and
* `Work.Beltrami.newlander_nirenberg_one_of_hol` (the passage from a local `J`-holomorphic
  function with nonvanishing differential to the required chart, in `Main.lean`).

The result is stated exactly in the form of the challenge statement for `n = 1`, including the
Nijenhuis hypothesis (which is redundant in real dimension two and is simply ignored).
-/
import Mathlib
import Submission.Work.Beltrami.LocalInput
import Submission.Work.Beltrami.Main

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff

noncomputable section

/-- **The `n = 1` Newlander--Nirenberg theorem**, given the analytic estimates
`CauchyEstimates` (Schauder estimates for the Beurling transform, the Pompeiu formula and the
regularity of the fixed point of the Beltrami equation). -/
theorem newlander_nirenberg_one_of_cauchy (H : CauchyEstimates)
    {U : Set (E 1)} (hU : IsOpen U) (J : E 1 → E 1 →L[ℝ] E 1) (hJ : IsAlmostComplexOn J U)
    (_hN : NijenhuisVanishesOn J U) {x : E 1} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E 1) (EuclideanSpace ℂ (Fin 1)),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : EuclideanSpace ℂ (Fin 1) → E 1) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E 1,
        fderiv ℝ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) y (J y v)
          = Complex.I • fderiv ℝ (φ : E 1 → EuclideanSpace ℂ (Fin 1)) y v :=
  newlander_nirenberg_one_of_hol (localHolInput_of_cauchyEstimates H) hU J hJ hx

end

end Work.Beltrami
