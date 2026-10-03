import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Work.SimplyConnected.Basic
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusFinal
import Submission.Lib.Unif2.Work.Potential.normalize_green_function

/-!
# Wiring the parallel subprojects into the simply connected case

`Work.SC.uniformization_of_simplyConnected_of_inputs` reduces the deliverable to three statements.
This module discharges two of them from the parallel subprojects, leaving only

* `hlog`/`hrem` : Bôcher's theorem and the removable-singularity theorem for a positive harmonic
  function on `X \ {z₀}` (`Work.Potential`, `Submission.LogCoefficientInput` /
  `Submission.RemovableInput`), which with `Work.Potential.normalize_green_function` normalise the
  logarithmic pole of a weak Green function;
* `hcov` : the projection of the modulus bundle of a strong Green function is a covering map
  (`Work.SC.isCoveringMap_branchProj`), which with
  `Work.SC.exists_holomorphic_modulus_of_hasGreenFunctionE` produces the holomorphic modulus (this
  is the alternative to the classical "periods are multiples of `2π`" route: the monodromy is
  trivial because `X` is simply connected);
* `hC` : the parabolic branch (`Work.Parabolic`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Normalisation of the logarithmic pole**, from the two potential-theoretic inputs
(`Work.Potential.normalize_green_function`). -/
theorem exists_hasGreenFunctionE_of_hasGreenFunctionWeak (hX : ¬ CompactSpace X)
    (hlog : ∀ z₀ : X, Submission.LogCoefficientInput (X := X) z₀)
    (hrem : ∀ z₀ : X, Submission.RemovableInput (X := X) z₀)
    {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionWeak z₀ E) :
    ∃ E' : X → ℝ, Submission.HasGreenFunctionE z₀ E' :=
  Work.Potential.normalize_green_function hX (hlog z₀) (hrem z₀) hE

/-- **The simply connected, non-compact case of uniformization**, with the two potential-theoretic
inputs (`hlog`, `hrem`), the covering property of the modulus bundle (`hcov`) and the parabolic
branch (`hC`) as hypotheses. -/
theorem uniformization_of_simplyConnected_of_inputs' [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X)
    (hlog : ∀ z₀ : X, Submission.LogCoefficientInput (X := X) z₀)
    (hrem : ∀ z₀ : X, Submission.RemovableInput (X := X) z₀)
    (hcov : ∀ {z₀ : X} {E : X → ℝ}, Submission.HasGreenFunctionE z₀ E →
      @IsCoveringMap (ModulusBundle z₀ E) X (modulusBundleTopology z₀ E) _
        (branchProj z₀ E))
    (hC : (∀ (z₀ : X) (E : X → ℝ), ¬ Submission.HasGreenFunctionWeak z₀ E) →
      Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ)) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Work.SC.uniformization_of_simplyConnected_of_inputs hX
    (fun hE => exists_hasGreenFunctionE_of_hasGreenFunctionWeak hX hlog hrem hE)
    (fun hE => exists_holomorphic_modulus_of_hasGreenFunctionE hE (hcov hE))
    hC

end Work.SC
