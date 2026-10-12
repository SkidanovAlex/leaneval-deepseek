import ChallengeDeps
import Submission.Work.BoseB1Cube.Defs
import Submission.Work.BoseFixB1B.sectorCountBox_of_smallN
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeSmallNArb` — the honest residual of the cube per-box chapter

Read `Submission/Work/BoseB1Cube/FINDING_cubeCrudeBand_session3.md` §9 first.

FS's `thm:smallbox` is proved by **grouping**: for `n > C_n μ|B|` write `n = m·n' + n''` and apply
*state-independent* per-size bounds to the blocks.  The corpus formalises this at the *frozen*
(ball-cutoff) word as `Work.BoseFixB1B.SmallNBounds`
(`Submission/Work/BoseFixB1B/sectorCountBox_of_smallN.lean:57`) with the PROVED consumption
`sectorCountSmallboxBox_of_smallN`, and the count-window consequence at the *frozen* word is the
chain `SectorCountSmallboxBox ⟹ LowStateCountCapB1` (`BoseFixB1S/LowStateCountCapB1.lean`).

Two facts make the **cube twin** the honest residual of this chapter:

1. **the per-size bounds must be *state-independent*** (constants times `∫Ψ²`): a prover of
   `BoseB1Cube/denseDeadRow_of_countWindow` returned `declare_false` on the alternative with the
   argument that a *state-dependent* row cannot be linear-chained into the descent (`m` copies are
   added, so any term not multiplied by the density is paid `m` times —
   `FINDING_perBoxFTotalAt_session4.md` §3);
2. **the states must be arbitrary `ContDiff` in-box states, NOT `BoxState`s**: the descent's slices
   are not permutation-invariant, so a `BoxState`-quantified row cannot feed the descent.  This is
   why `Work.BoseB1Cube.CubeSmallNBounds` (`cubeSmallboxLower.lean:44`) cannot serve as stated.

`CubeSmallNArb` below is the **verbatim cube twin of `SmallNBounds`** (`sbWord ↦ sbWordCube`, the
`InBox` hypothesis = the descent's a.e. box-support).  The PROVED
`Work.BoseB1Cube.sbWordCube_descent_atSizes` consumes its items 1 and 2 directly; item 3 is the
`m = 0` branch of the same descent.  It is a `Prop` and is **not** proved here.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.BoseBox Work.UBB
  Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The state-independent cube per-size bounds** — the verbatim cube twin of
`Work.BoseFixB1B.SmallNBounds` at the single cube cutoff.

With `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`,
`V = boxMass ℓ d u`, `A = dlBox ℓ d u`, `W₁ = boxM1 ℓ A (wSmall1Pair h M ℓ d u)` and
`Γ = PBΓ v μ`, the three items are

* **(1)** for `Cn·μ·V ≤ n' < (Cn+1)·μ·V`:  `(1/18)·μ·(n'/V)·W₁·∫Ψ² ≤ sbWordCube v h μ u Ψ`;
* **(2)** for `n'' ≤ 2·Cn·μ·V`:
  `(¼(n''/V − μ)²W₁ − ½μ²W₁ − C·(μ²aΓW₁ + μa))·∫Ψ² ≤ sbWordCube v h μ u Ψ`;
* **(3)** for `n < Cn·μ·V`:  `boxLHS h (1/20) C μ n u·∫Ψ² ≤ sbWordCube v h μ u Ψ`,

each for every `Ψ : X n → ℝ` with `ContDiff ℝ ⊤ Ψ` and `InBox v μ u Ψ`. -/
def CubeSmallNArb (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (Cn C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (∀ {n' : ℕ}, Cn * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ) →
            (n' : ℝ) < (Cn + 1) * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Ψ : X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → Work.BoseFixB1B.InBox v μ u Ψ →
              (1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u) * Work.BoseFixB1B.PBW h μ u
                  * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
        ∧ (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Ψ : X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → Work.BoseFixB1B.InBox v μ u Ψ →
              ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2 * Work.BoseFixB1B.PBW h μ u
                  - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
                  - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBW h μ u
                      + μ * (_root_.BoseGases.a v)))
                  * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
        ∧ (∀ {n : ℕ}, (n : ℝ) < Cn * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Ψ : X n → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → Work.BoseFixB1B.InBox v μ u Ψ →
              Work.BoseFixB1B.boxLHS h (1 / 20) C μ n u
                  * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)

/-- **`CubeSmallNArb` at a prescribed diluteness threshold is antitone in `C` after a threshold
shrink** — recorded as an interface note only (the constants are existential in every consumer). -/
def CubeSmallNArbEx (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ Cn C : ℝ, 2 ≤ Cn ∧ 0 ≤ C ∧ CubeSmallNArb v h Cn C

end Work.BoseB1Cube
