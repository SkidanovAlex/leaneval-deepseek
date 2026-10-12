import ChallengeDeps
import Submission.Work.BoseB1Cube.countWindowOfNominal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomAprioriDefs` — the **nominal a-priori rows** as a `Prop`

FS `eq:aprioriRn+` at the *nominal* (sharp indicator-count) density of
`Work.BoseB1Cube.NomDefs`, in the `J`-uniform shape needed by the particle-window bridge:

    ∃ C_A ε_A, 0 < C_A ∧ 0 < ε_A ∧ ∀ J μ, Adm v ε_A μ → J ≤ K_B³ →
      ∀ n Φ, 0 < ‖Φ‖² → IsLowB v h J μ n Φ →
        nomRPsi h μ Φ ≤ C_A·(μ²(a v)ℓ³κ)·‖Φ‖²
        ∧ (b/(2ℓ²))·⟨n₊⟩ ≤ C_A·(μ²(a v)ℓ³κ)·‖Φ‖² .

with `κ = K_B³(μ(a v)³)^{1/2}` (`Work.BoseB1Cube.kappa`) and `ℓ = sideAt μ (a v)`.

This is the nominal twin of `Work.BoseFixB1S.AprioriUnif` (which reads the *smooth* remainder
`Work.BoseFixB1.RPsi`).  It is the input of the nominal particle-window bridge
(`Work.BoseB1Cube.nomWindowBridgeMu`), which is a verbatim re-run of the smooth
`Work.BoseFixB1.windowBridgeUnif_holds` at the nominal objects
(`nomDens`, `nomSig`, `wbUSharp`).

The definition lives in its own module because it is shared by

* `Submission.Work.BoseB1Cube.nomCleanRows` — the derivation of this `Prop` from
  `Work.BoseB1Cube.PerBoxFNomMu` (FS `thm:smallbox` at the sliding box, nominal spelling);
* `Submission.Work.BoseB1Cube.particleWindowMu` — the particle window built on it.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS `eq:aprioriRn+` at the nominal (sharp indicator-count) density**, uniformly in the low-state
threshold `J ≤ K_B³` — the nominal twin of `Work.BoseFixB1S.AprioriUnif`.

`Work.BoseB1Cube.kappa v μ = K_B³(μ(a v)³)^{1/2}` is FS's a-priori error scale, and
`nomRPsi`/`nomSig` are the nominal remainder and averaged density of `NomDefs.lean`. -/
def NomAprioriUnif (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ C_A ε_A : ℝ, 0 < C_A ∧ 0 < ε_A ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε_A μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
          nomRPsi h μ (Φ : X n → ℝ)
              ≤ C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
                  * normB v μ n (Φ : X n → ℝ)
          ∧ ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
                * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
              ≤ C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
                  * normB v μ n (Φ : X n → ℝ)

end Work.BoseB1Cube
