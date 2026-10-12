import ChallengeDeps
import Submission.Closure2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the thermodynamic limit, closed under Ingredient 1.

Composition of the machine-verified chain

    `gcExcess_witness_aux v ρmax ρ` at every `ρ ∈ (0,ρmax)`
        ⟹  `gcSup_upper v ρmax`                        (Closure2.gcSup_upper_of_excess)
        ⟹  convergence of the box densities along the
            joint filter at every small density         (GCPressure.eventually_hconv_of_gcSup_upper)

So the whole of Layer 2 (the hypothesis `hconv` of
`Endgame.lhy_bound_of_convergence_and_box` and
`ThermoLimit.e_ge_of_eventually_box_ge`) follows from Ingredient 1 — the
T = 0 equivalence of ensembles (`gcExcess_witness_aux`, `Submission.Excess`),
the single remaining classical input of the thermodynamic limit.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Ingredient 1 at every density of `(0,ρmax)` gives the thermodynamic-limit
convergence of the box-energy densities (`hconv`). -/
theorem layer2_hconv_of_excess {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) {ρmax : ℝ}
    (hρmax : 0 < ρmax) (haux : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → gcExcess_witness_aux v ρmax ρ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ, Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) := by
  exact eventually_hconv_of_gcSup_upper (v := v) (ρmax := ρmax) hv hv1 hρmax hR hsupp
    (gcSup_upper_of_excess hv hv1 hR hsupp hρmax haux)

end BoseGases

end Submission
