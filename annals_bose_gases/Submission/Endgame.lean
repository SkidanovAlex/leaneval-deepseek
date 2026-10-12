import ChallengeDeps
import Submission.Rhs
import Submission.ThermoLimit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
The endgame interface: from thermodynamic-limit convergence and an eventual
box lower bound to the Lee--Huang--Yang inequality for `e ρ v`.

The second conjunct of `theorem_1_2` (in `Submission.lean`) is

    ∀ᶠ ρ in 𝓝[>] 0,  lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1/2 + η) ρ ≤ e ρ v

(with the constants `η`, `𝓒` of `Submission.lean`).  By
`ThermoLimit.e_ge_of_eventually_box_ge` this follows from exactly two inputs,
here stated as hypotheses of `lhy_bound_of_convergence_and_box`:

  * `hconv` — the thermodynamic-limit convergence of the box-energy densities
    along the joint filter at every small density (Layer 2; derived from
    Ingredient 1 via `Closure2.gcSup_upper_of_excess` +
    `GCPressure.eventually_hconv_of_gcSup_upper`);
  * `hbox`  — the eventual finite-box lower bound `lhyRhs A K s (N/L³) ≤
    boxDensity` (Layer 5, the Fournais--Solovej box bound, `A := a v`,
    `K := 𝓒 (𝓡 v) (R/a v)`, `s := 1/2 + η`).

Everything else (continuity of the right-hand side as a function of the
density, the filter lifting) is proved here.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Endgame lifting: convergence of the box densities (`hconv`) together with
an eventual box lower bound (`hbox`) gives the pointwise lower bound on the
energy density. -/
theorem lhy_bound_of_convergence_and_box (v : ℝ³ → ℝ) {A K s : ℝ}
    (hs : 0 < s)
    (hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ, Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x))
    (hbox : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs A K s ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), lhyRhs A K s ρ ≤ e ρ v := by
  exact e_ge_of_eventually_box_ge (v := v) (φ := fun ρ : ℝ => lhyRhs A K s ρ)
    (lhyRhs_eventually_continuousAt (A := A) (K := K) (s := s) (le_of_lt hs))
    hconv hbox

end BoseGases

end Submission
