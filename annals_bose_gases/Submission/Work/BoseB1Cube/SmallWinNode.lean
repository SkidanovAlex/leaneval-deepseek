import ChallengeDeps
import Submission.Work.BoseB1Cube.swhEdgeSplit
import Submission.Work.BoseB1Cube.swhRegSR2Node_holds
import Submission.Work.BoseB1Cube.swhSR2LocalNode_holds
import Submission.Work.BoseB1Cube.swhThinNodeProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.SmallWinNode` — the small-window case of `NormNode`

Holder file.  The target `Work.BoseB1Cube.SmallWinProp v h R` (the row

    (1/18)·μ·(n/|B(u)|)·∬w_{1,B(u)}  ≤  sbWordCube v h μ u Ψ

on the small window `μ·∬w_{1,B(u)} ≤ (a v)`, the count window `Cn·μ|B| ≤ n ≤ 2Cn·μ|B|` with
`Cn ≥ 4`, and the in-box smooth normalised state) is proved here from a **three-arm case split**:

* **gap arm** — PROVED: `Work.BoseB1Cube.smallWinGapArmGen` (`smallWinGapArmGen.lean`): for every
  prescribed `c₀ > 0` and every `Cn ≥ 4` there is `ε₀ > 0` such that on the small window, the count
  window and `c₀ ≤ bQ`, the row holds.
* **flat arm** — `Work.BoseB1Cube.FlatArmRow v h R c₀` below: the row for the near-condensate,
  *pair-condensed* states `bQ < c₀ ∧ FlatArm37`.  Requested as
  `Work.BoseB1Cube.flatArm37RowNode`; the blueprint is the *cyclic* `flatArm37RowOneGood` ledger
  (`Submission/Work/BoseB1Cube/flatArm37RowOneGood.lean`, whose `[4μ|B|, 5μ|B|)` window
  hypothesis is unused in its proof), adapted to this node's window in
  `Submission/Work/BoseB1Cube/flatArm37NodeRow.lean`; see
  `Submission/Work/BoseB1Cube/BRIEF_flatArm37NodeRow.md`.
* **hole arm** — `Work.BoseB1Cube.HoleRow v h R c₀` below: the row for the near-condensate,
  *pair-non-condensed* states `bQ < c₀ ∧ ¬ FlatArm37`.  This is the fleet's standing residual
  (`cubeHoleArms37.HoleRowOne` at this node's window) and it is the *only* open input of the node.
  Per the project lead's end-of-session ruling it **needs N4** (the edge-box case, a localised
  Dyson bound) and is therefore *research*; the project was switched to the reviewed fallback
  `SmallWinPropE` (vanishing slack: add `μ((a v)·chiMass − κ·w1MassB)_+·n/|B|` to piece C and to
  the descent), dispatched as `BoseSWE`.  See `FINDING_SmallWinNode_session3.md` §0bis, §3, §4.

The reduction `smallWinProp_of_arms` below is PROVED and is the whole content of this file.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The flat arm**: the node's row for the near-condensate (`bQ < c₀`), pair-condensed
(`FlatArm37`) states. -/
def FlatArmRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) (c₀ : ℝ) : Prop :=
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
        Work.BoseFixB1.bQ v μ Ψ u < c₀ →
        Work.BoseB1Cube.FlatArm37 v h μ n Ψ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The hole arm**: the node's row for the near-condensate (`bQ < c₀`), pair-non-condensed
(`¬ FlatArm37`) states — the fleet's standing residual at this node's window, and the node's only
open input. -/
def HoleRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) (c₀ : ℝ) : Prop :=
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
        Work.BoseFixB1.bQ v μ Ψ u < c₀ →
        ¬ Work.BoseB1Cube.FlatArm37 v h μ n Ψ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The two arms are downward-closed in the threshold `c₀`** (a smaller threshold is a weaker
hypothesis on the state). -/
theorem FlatArmRow_mono {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} {c c' : ℝ}
    (hc : c ≤ c') (hf : FlatArmRow v h R c') : FlatArmRow v h R c :=
  fun Cn hCn => by
    obtain ⟨ε₀, hε₀, hf'⟩ := hf Cn hCn
    exact ⟨ε₀, hε₀, fun μ hAdm n Ψ u hu h1 h2 h3 h4 h5 h6 hQ hF =>
      hf' μ hAdm n Ψ u hu h1 h2 h3 h4 h5 h6 (lt_of_lt_of_le hQ hc) hF⟩

/-- The hole arm is downward-closed in `c₀`. -/
theorem HoleRow_mono {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} {c c' : ℝ}
    (hc : c ≤ c') (hf : HoleRow v h R c') : HoleRow v h R c :=
  fun Cn hCn => by
    obtain ⟨ε₀, hε₀, hf'⟩ := hf Cn hCn
    exact ⟨ε₀, hε₀, fun μ hAdm n Ψ u hu h1 h2 h3 h4 h5 h6 hQ hF =>
      hf' μ hAdm n Ψ u hu h1 h2 h3 h4 h5 h6 (lt_of_lt_of_le hQ hc) hF⟩

/-- **The three-arm reduction of the node.**  The gap arm is the PROVED
`Work.BoseB1Cube.smallWinGapArmGen`; the two remaining arms are the `Prop`s above, and the two
thresholds (`c₀` for the gap/flat-hole split, `10⁻⁶` for the flat/hole split inside the
near-condensate class) are merged with `min`. -/
theorem smallWinProp_of_arms {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hflat : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 10 ^ 6 ∧ FlatArmRow v h R c₀)
    (hhole : ∃ c₀ : ℝ, 0 < c₀ ∧ HoleRow v h R c₀) :
    Work.BoseB1Cube.SmallWinProp v h R := by
  obtain ⟨c₁, hc₁, hc₁6, hflat'⟩ := hflat
  obtain ⟨c₂, hc₂, hhole'⟩ := hhole
  set c : ℝ := min c₁ c₂ with hc
  have hcpos : 0 < c := lt_min hc₁ hc₂
  intro Cn hCn
  obtain ⟨εg, hεg, hgap⟩ :=
    Work.BoseB1Cube.smallWinGapArmGen (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn c hcpos
  obtain ⟨εf, hεf, hf⟩ := hflat' Cn hCn
  obtain ⟨εh, hεh, hh⟩ := hhole' Cn hCn
  refine ⟨min (min εg εf) εh, lt_min (lt_min hεg hεf) hεh, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
  have hAdmg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmf : Work.BoseBoxFix.Adm v εf μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmh : Work.BoseBoxFix.Adm v εh μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  by_cases hQ : c ≤ Work.BoseFixB1.bQ v μ Ψ u
  · exact hgap μ hAdmg n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQ
  · have hQ1 : Work.BoseFixB1.bQ v μ Ψ u < c₁ :=
      lt_of_lt_of_le (lt_of_not_ge hQ) (min_le_left _ _)
    have hQ2 : Work.BoseFixB1.bQ v μ Ψ u < c₂ :=
      lt_of_lt_of_le (lt_of_not_ge hQ) (min_le_right _ _)
    by_cases hF : Work.BoseB1Cube.FlatArm37 v h μ n Ψ u
    · exact hf μ hAdmf n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQ1 hF
    · exact hh μ hAdmh n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQ2 hF

/-- The node's target `Work.BoseB1Cube.SmallWinProp v h R`, through the lead's merged hole node
`Work.BoseB1Cube.SmallWinHolePD v h` (`smallWinHolePD.lean`, reduction
`Work.BoseB1Cube.smallWinProp_of_holePD` PROVED) and the box-region split of
`smallWinNodes.lean` + `swhEdgeSplit.lean`:

* N1 `swhSR2LocalNode` — `Work.BoseB1Cube.swhSR2LocalNode_holds` (PROVED);
* N2 `swhRegSR2Node` — `Work.BoseB1Cube.swhRegSR2Node_holds` (PROVED);
* N3 `swhThinNode` — `Work.BoseB1Cube.swhThinNodeProved` (PROVED);
* N4 `swhEdgeNode` — `Work.BoseB1Cube.swhEdgeNode_of_corner_cap` (PROVED) from the two remaining
  open leaves `swhCornerNode` (`μ·bV < 1000`) and `swhCapNode` (`1000 ≤ μ·bV` with the cap-mass
  threshold failing — equivalently, by `swhMassRowsProved`, the big boxes where `swhRegular` fails),
  delegated as `swhCornerNode_proved` / `swhCapNode_proved`.

So the file's `sorry`s are exactly those **two** named leaves. -/
theorem SmallWinNode {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.SmallWinProp v h R := by
  have hN1 : Work.BoseB1Cube.swhSR2LocalNode v h :=
    Work.BoseB1Cube.swhSR2LocalNode_holds (v := v) h hv hv1 hvrad hR hv_supp hav
  have hN2 : Work.BoseB1Cube.swhRegSR2Node v h :=
    Work.BoseB1Cube.swhRegSR2Node_holds (v := v) h hv hv1 hvrad hR hv_supp hav
  -- THE leaf N3: `Work.BoseB1Cube.swhThinNode v h` (delegated as `swhThinNodeProved`).
  have hN3 : Work.BoseB1Cube.swhThinNode v h :=
    Work.BoseB1Cube.swhThinNodeProved (v := v) h hv hv1 hvrad hR hv_supp hav
  -- THE leaf N4a: the small-volume corner `Work.BoseB1Cube.swhCornerNode v h`.
  have hcorner : Work.BoseB1Cube.swhCornerNode v h := by sorry
  -- THE leaf N4b: the big-box cap `Work.BoseB1Cube.swhCapNode v h R`.
  have hcap : Work.BoseB1Cube.swhCapNode v h R := by sorry
  have hedge : Work.BoseB1Cube.swhEdgeNode v h :=
    Work.BoseB1Cube.swhEdgeNode_of_corner_cap (v := v) h hv hv1 hvrad hR hv_supp hav
      hN1 hN2 hcorner hcap
  exact Work.BoseB1Cube.smallWinProp_of_holePD (v := v) h hv hv1 hvrad hR hv_supp hav
    (Work.BoseB1Cube.swhSmallWinHolePD_of_nodes h hN1 hN2 hN3 hedge)

end Work.BoseB1Cube
