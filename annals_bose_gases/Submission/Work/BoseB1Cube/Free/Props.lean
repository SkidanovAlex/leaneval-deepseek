import ChallengeDeps
import Submission.Work.BoseFixB1B.matchedWindowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Free.Props` — the **holder-free** copies of the node's `Prop`s

Holder: `Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean` (session 10).

## Why this module exists

The node's file is the *holder*: its statement `Work.BoseB1Cube.NomRowLinWindowRow` must be proved
**inside** it, i.e. from modules that do **not** (transitively) import it.  The whole fleet-side
chain of the node, however, lives in modules that *do*: `smallWinDefs.lean` — which is a
*definitions-only* module — gratuitously imports the holder, and every arm of the small-window case
(`smallWinGapArmGen`, `flatArm37RowNode`, `LargeWinNode`, `SmallWinNode`, `smallWinHolePD`, …)
imports `smallWinDefs`.

This module breaks the tangle in the only way that leaves every colleague's file untouched: it
**re-declares** the node's case-splitting `Prop`s under fresh (`…F`) names in a *holder-free* cone,
with **bodies copied verbatim** from `smallWinDefs.lean` and the holder
(`Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean`, `NormNode`).  The `…F` suffixes are not
cosmetic: a module that imported both this file and `smallWinDefs` would otherwise carry a
duplicate declaration.

The three `Prop`s (`SmallWinPropF`, `LargeWinPropF`, `NormNodeF`) are the small-window case, the
large-window case and the normalised node; `normNodeF_of_winF` is the (ten-line) dichotomy that
assembles the first two into the third.  `NormNodeF v h R` is *definitionally* the clause the
holder's own PROVED `nomRowLinWindowRow_of_normNode` consumes (the bodies of `NormNode` and
`NormNodeF` are character-for-character the same), so a caller writes

    nomRowLinWindowRow_of_normNode' … hNormNodeF

see `Submission/Work/BoseB1Cube/Free/NodeF.lean` and the holder.

⚠ **Do not add an `import Submission.Work.BoseB1Cube.smallWinDefs` (or any holder-downstream
module) to this file** — that would re-taint the whole cone and defeat the purpose.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Holder-free copy of `Work.BoseB1Cube.SmallWinProp`** (`smallWinDefs.lean`): the node's row
with the extra hypothesis `μ · bW v h μ u ≤ a v` (branch 1 of the PROVED
`Work.BoseB1Cube.windowShiftDichotomy`). -/
def SmallWinPropF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **Holder-free copy of `Work.BoseB1Cube.LargeWinProp`** (`smallWinDefs.lean`): the node's row
with the extra hypothesis `¬ (μ · bW v h μ u ≤ a v)` (branch 2 of the PROVED
`Work.BoseB1Cube.windowShiftDichotomy`). -/
def LargeWinPropF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ¬ (μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v) →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **Holder-free copy of `Work.BoseB1Cube.NormNode`** (the holder's own definition): the node
restricted to **normalised** states. -/
def NormNodeF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The window dichotomy at the holder-free copies**: `NormNodeF` follows from the small-window
case and the large-window case (the ten-line split of `normNodeOfPort`,
`Submission/Work/BoseB1Cube/normNodeOfPort.lean`). -/
theorem normNodeF_of_winF {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hS : SmallWinPropF v h R) (hL : LargeWinPropF v h R) : NormNodeF v h R := by
  intro Cn hCn
  obtain ⟨εs, hεs, hSc⟩ := hS Cn hCn
  obtain ⟨εl, hεl, hLc⟩ := hL Cn hCn
  refine ⟨min εs εl, lt_min hεs hεl, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hI hnlo hnhi
  by_cases hw : μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v
  · exact hSc μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)) n Ψ u hu hw hΨ hsupp hI
      hnlo hnhi
  · exact hLc μ (Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)) n Ψ u hu hw hΨ hsupp hI
      hnlo hnhi

end Work.BoseB1Cube
