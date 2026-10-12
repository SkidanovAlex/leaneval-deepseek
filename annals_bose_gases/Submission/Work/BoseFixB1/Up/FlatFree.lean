import ChallengeDeps
import Submission.Work.BoseFixB1.Up.FreeGap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.FlatFree` — the flat (condensed) branch, free threshold: the single residual

This module states the **one analytic obligation** to which the target
`Work.BoseFixB1.perBoxFWeight_holds` is reduced:

    `∃ γ > 0, PerBoxFlatFree v h R γ`

i.e. there is *some* positive threshold `γ` such that `PerBoxF` holds at the good set on the
*thick* boxes whose sliding-box excited count is below `γ·n·‖Φ‖²`, with the coefficient and the
error constant existentially quantified.

This is the **weakest known form** of the corpus's flat-branch atom — the prover chooses `γ` and
`c₁` — and it is exactly the residual held by the sibling agent as
`Work.BoseFixB1S.flatBranchFree_exists` / `Work.BoseFixB1.flatBranchAtom`
(`Submission/Work/BoseFixB1S/perBoxFWeightB1.lean`, `Submission/Work/BoseFixB1/flatBranchAtom.lean`),
which cannot be imported into the target because they (transitively) import it.

Why the *free* threshold matters.  At FS's parameters the particle number in the sliding box is
`n ≈ μ|B(u)| ≈ X^{-148}` with `X = (μa³)^{1/323}` — astronomically large.  With the *fixed*
threshold `γ = 10^{-100}` the flat band `n₊ ≤ γ·n‖Φ‖²` still contains states with a *single fully
excited slot* (`n₊ ≈ ‖Φ‖²`, since `γn ≫ 1` for `μa³` tiny): those are **not** mean-field states
(they are paid by the kinetic word, not by the pair term), so a prover of the fixed-threshold atom
must handle them.  With a *free* threshold one takes `γ ≪ 1/n`, and the flat band becomes
`n₊ ≪ ‖Φ‖²` — genuinely box-constant states, the regime the mean-field ledger of FS §5–§11 is
designed for.  The gap branch is available at every threshold (`Up.gapAtAll`, proved), so there is
no threshold-matching obstruction.

Everything else of the target is PROVED and axiom-clean in this cone:

* the gap branch at every threshold — `Up.gapAtAll` (`Up/FreeGap.lean`);
* the thin (degenerate-box) case — `Up.perBoxF_thin_holds` (`Up/Core.lean`);
* the three-way assembly — `Up.perBoxFWeight_of_flatFree` (`Up/FreeGap.lean`).

The fleet's route to the residual is the *sharp flat ledger*
`Work.BoseFixB1S.perBoxF_of_ledger_sharp` (`flatLedgerSharpB1.lean`, proved) together with its
rows (Fsharp), (fib), (PQ₂) and the budget; see
`Submission/Work/BoseFixB1S/FINDING_flatLedgerSharpB1.md`.

**This file contains a `sorry` by design**: it is the residual, not a proof.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The flat-branch residual** (free threshold, free constants). -/
def FlatFreeResidual (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ PerBoxFlatFree v h R γ

/-- **The fixed-threshold atom as a `Prop`** — the shape of the corpus's
`Work.BoseFixB1.flatBranchAtom` (`Submission/Work/BoseFixB1/flatBranchAtom.lean`) and of the
hypothesis of `Up.perBoxF_thick_of_flatBranch`.  It is *stronger* than `FlatFreeResidual`
(its band `n₊ ≤ 10^{-100}n‖Φ‖²` is larger than the free-threshold prover would choose), and it is
the shape in which the sibling agent's atom is stated. -/
def FlatAtomShape (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u

/-- **The fixed-threshold atom implies the free-threshold residual** (take `γ = 10^{-100}`):
`FlatAtomShape ⟹ FlatFreeResidual`.  So a proof of the corpus's `Work.BoseFixB1.flatBranchAtom`
closes this file as well. -/
theorem flatFreeResidual_of_flatAtomShape {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {R : ℝ} (hA : FlatAtomShape v h R) : FlatFreeResidual v h R := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, H⟩ := hA
  exact ⟨(1 / 10 : ℝ) ^ (100 : ℕ), by norm_num, ε₀, c₁, C, hε₀, hc₁, hC,
    fun μ hAdm n Φ u hu hthin hlt => H μ hAdm n Φ u hu hthin (le_of_lt hlt)⟩

/-! **The residual has moved.**  The theorem

    `Work.BoseFixB1.Up.flatFreeResidual :
       FlatFreeResidual v h R`   (the flat/condensed branch of FS `thm:smallbox`)

is now a *dispatched target* at `Submission/Work/BoseFixB1/Up/flatFreeResidual.lean`
(module `Submission.Work.BoseFixB1.Up.flatFreeResidual`), which imports this file for
the definitions `PerBoxFlatFree`, `FlatFreeResidual`, `FlatAtomShape`.  Nothing in this
file is a `sorry`. -/

end Work.BoseFixB1.Up
