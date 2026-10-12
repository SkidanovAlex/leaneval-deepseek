import ChallengeDeps
import Submission.Work.BoseB1Cube.Free.FlatArmF
import Submission.Work.BoseB1Cube.Free.GapArmF
import Submission.Work.BoseB1Cube.Free.Props
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Free.SmallWinRoute` — the fleet's **live** small-window target
# suffices for the node, holder-free

Holder: `Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean` (session 10, continuation).

The fleet's hole-row file `Submission/Work/BoseB1Cube/smallWinHoleRow.lean` carries a target
(`Work.BoseB1Cube.smallWinHoleRow`) that is *strictly weaker* than `SmallWinProp` — it adds the two
state hypotheses `bQ < c₀` (`c₀` ours, uniform in `Cn`) and `¬ FlatArm37` and drops nothing else:

    ∃ c₀ > 0, ∀ Cn ≥ 4, ∃ ε₀ > 0, ∀ μ (Adm), ∀ u ∈ goodSet, ∀ Ψ (in-box, ContDiff, ∫Ψ² = 1),
      μ·bW ≤ a v →  Cn·μ·|B| ≤ n ≤ 2Cn·μ·|B| →  bQ < c₀ →  ¬ FlatArm37  →  D ≤ sbWordCube .

This module re-states it, verbatim, as the holder-free `Prop` **`SmallWinHoleRowF`** and proves the
short reduction

    **`smallWinPropF_of_smallWinHoleRowF : SmallWinHoleRowF v h R → SmallWinPropF v h R`**

by the dichotomy on `bQ` at the threshold `c₀`:

* `bQ ≥ c₀` — the **gap arm** (`Free/GapArmF.lean`, `smallWinGapArmGenF`, PROVED for *every*
  prescribed threshold) pays the row;
* `bQ < c₀ ∧ FlatArm37` — the **flat arm** (`Free/FlatArmF.lean`, `flatArm37RowNodeF`, PROVED)
  pays it, at its own threshold `min c₀ 10⁻⁶`;
* `bQ < c₀ ∧ ¬ FlatArm37` — the fleet's row.

So the node's small-window case closes as soon as the fleet's *live* target does: copy the proof of
`Work.BoseB1Cube.smallWinHoleRow` (`Submission/Work/BoseB1Cube/smallWinHoleRow.lean`, a module whose
cone is holder-downstream only through the gratuitous `import …smallWinDefs`) into this cone with the
`…F` renamings, plug it into `holeLeaf2` of the holder, and the node follows.
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

/-- **The fleet's live hole-row target, holder-free** — the verbatim statement of
`Work.BoseB1Cube.smallWinHoleRow` (`Submission/Work/BoseB1Cube/smallWinHoleRow.lean`), with the
declaration renamed.  (`R` is unused by the body, but kept for uniformity with the node.) -/
def SmallWinHoleRowF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v →
          ContDiff ℝ (⊤ : ℕ∞) Ψ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
            Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
          (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
          Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
          (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
          Work.BoseFixB1.bQ v μ Ψ u < c₀ →
          ¬ Work.BoseB1Cube.FlatArm37 v h μ n Ψ u →
          (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The fleet's live target implies the node's small-window case** (gap arm at `c₀`, flat arm at
`min c₀ 10⁻⁶`, then the fleet's row). -/
theorem smallWinPropF_of_smallWinHoleRowF {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hrow : SmallWinHoleRowF v h R) : Work.BoseB1Cube.SmallWinPropF v h R := by
  obtain ⟨c₀, hc₀, hrow'⟩ := hrow
  intro Cn hCn
  set c₁ : ℝ := min c₀ (1 / 10 ^ 6) with hc₁def
  have hc₁pos : 0 < c₁ := lt_min hc₀ (by norm_num)
  have hc₁c₀ : c₁ ≤ c₀ := min_le_left _ _
  obtain ⟨εf, hεf, hflat⟩ :=
    Work.BoseB1Cube.flatArm37RowNodeF (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn
  obtain ⟨εg, hεg, hgap⟩ :=
    Work.BoseB1Cube.smallWinGapArmGenF (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn c₁ hc₁pos
  obtain ⟨εh, hεh, hhole⟩ := hrow' Cn hCn
  refine ⟨min (min εf εg) εh, lt_min (lt_min hεf hεg) hεh, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
  have hAf : Work.BoseBoxFix.Adm v εf μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAh : Work.BoseBoxFix.Adm v εh μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  by_cases hQ : Work.BoseFixB1.bQ v μ Ψ u < c₁
  · by_cases hF : Work.BoseB1Cube.FlatArm37 v h μ n Ψ u
    · -- the flat arm (its own hard-wired threshold is `bQ < 10⁻⁶`)
      exact hflat μ hAf n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
        (lt_of_lt_of_le hQ (min_le_right _ _)) hF
    · exact hhole μ hAh n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
        (lt_of_lt_of_le hQ hc₁c₀) hF
  · exact hgap μ hAg n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 (le_of_not_gt hQ)

end Work.BoseB1Cube
