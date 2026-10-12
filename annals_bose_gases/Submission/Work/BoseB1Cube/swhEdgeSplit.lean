import ChallengeDeps
import Submission.Work.BoseB1Cube.swhMassRowsProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.swhEdgeSplit` — N4 split by the mass rows

Holder: `Submission/Work/BoseB1Cube/smallWinNodes.lean` (the target `Work.BoseB1Cube.SmallWinNode`
lives one level above; this module only sharpens its single open node `swhEdgeNode`).

## What is proved here

`Work.BoseB1Cube.swhMassRowsProved` (`swhMassRowsProved.lean`, PROVED) packages FS
`lm:w2>w1` at the corpus cutoff: **if the cap-mass threshold**

    (1/δ)·R²·(C·chiSupAbs·(1/ℓ + 1/(ℓ·d)))²·(ℓ·d)³  ≤  chiMass M ℓ d u

holds, then both mass rows hold with loss `(1−δ)`.  At `δ = 1/50` those are **verbatim** the first
two clauses of `swhRegular`, so on a box with `1000 ≤ μ·bV`:

    swhRegular  ⟺  the cap-mass threshold      (⟸ is `swhMassRowsProved` at `δ = 1/50`)

Consequently `¬ swhRegular` on a **big box** (`1000 ≤ μ·bV`) is exactly the *failing* of that
threshold, i.e. the quantitative cap-smallness `chiMass < swhCapBound R C …`.  This module splits
`swhEdgeNode` into the two honest cases (`swhCornerNode` = the corner `μ·bV < 1000`;
`swhCapNode` = the big box with the threshold failing) and proves the assembly

    **`swhEdgeNode_of_corner_cap`** :  N1 → N2 → swhCornerNode → swhCapNode → swhEdgeNode .

The three `N4`-hypotheses that the design's case split already excludes (`¬swhRegular`,
`¬(swhThin ∧ η·a·χ_m ≤ W)`) are carried verbatim by both sub-nodes, so the assembly is a pure
case split plus one application of `swhMassRowsProved`.
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

/-- The **cap-mass threshold** of `Work.BoseB1Cube.swhMassRowsProved` at `δ = 1/50`
(the loss that makes the mass rows verbatim `swhRegular`'s first two clauses). -/
noncomputable def swhCapBound (R C ℓ d : ℝ) : ℝ :=
  (1 / (1 / 50)) * R ^ 2 * (C * Submission.BoseGases.chiSupAbs * (1 / ℓ + 1 / (ℓ * d))) ^ 2
    * (ℓ * d) ^ 3

/-- Its negation at the box `u` — the **cap-smallness** that `¬ swhRegular` forces on a big box. -/
def swhCapSmall (v : E3 → ℝ) (R C : ℝ) (μ : ℝ) (u : E3) : Prop :=
  ¬ (swhCapBound R C (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ)
        ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u)

/-- **The corner sub-node of N4** — the N4 row on the *corner* `μ·bV < 1000`
(`1 ≤ μ·bV` is free from `goodSet`, `Work.BoseFixB1.one_le_mu_boxMassGood`; the ledger's other
rows need `μ·bV ≳ 32`, so this is the genuinely small-volume corner). -/
def swhCornerNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∀ η : ℝ, 0 < η → ∃ c₀ ε₀ : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
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
        swhPairDead v h μ Ψ u →
        ¬ swhRegular v h μ u →
        ¬ (swhThin v μ u ∧ η * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u
            ≤ Work.BoseFixB1.bW v h μ u) →
        μ * Work.BoseFixB1.bV v μ u < 1000 →
        swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The big-box cap sub-node of N4** — the N4 row on the big box `1000 ≤ μ·bV` whose cap-mass
threshold (at the proof's own constant `C`) fails.  Equivalently, by
`Work.BoseB1Cube.swhMassRowsProved`, the boxes of `¬ swhRegular` on which the mass rows really
cannot be had. -/
def swhCapNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∀ C : ℝ, 0 < C → ∀ η : ℝ, 0 < η → ∃ c₀ ε₀ : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
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
        swhPairDead v h μ Ψ u →
        ¬ swhRegular v h μ u →
        ¬ (swhThin v μ u ∧ η * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u
            ≤ Work.BoseFixB1.bW v h μ u) →
        1000 ≤ μ * Work.BoseFixB1.bV v μ u →
        swhCapSmall v R C μ u →
        swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The split of `swhEdgeNode`.**  With N1 and N2 as hypotheses, the corner and cap sub-nodes
give `swhEdgeNode`: on the corner use the corner node; on a big box either the cap-mass threshold
holds — then `swhMassRowsProved` at `δ = 1/50` gives the two mass rows, i.e. `swhRegular`, and
N2 + N1 close the row — or it fails, which is exactly `swhCapSmall`. -/
theorem swhEdgeNode_of_corner_cap {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (h1 : swhSR2LocalNode v h) (h2 : swhRegSR2Node v h)
    (hc : swhCornerNode v h) (hcap : swhCapNode v h R) : swhEdgeNode v h := by
  intro Cn hCn
  obtain ⟨εm, Cm, hεm, hCm, hmass⟩ :=
    swhMassRowsProved (v := v) h hv hv1 hvrad hR hv_supp hav (1 / 50) (by norm_num)
  obtain ⟨ε₂, C₂, hε₂, hC₂, hrow₂⟩ := h2 Cn hCn
  obtain ⟨ε₁, hε₁, hrow₁⟩ := h1 Cn hCn C₂ hC₂
  obtain ⟨c₁, εc, hc₁, hεc, hcorner⟩ := hc Cn hCn 1 (by norm_num)
  obtain ⟨c₂, εd, hc₂, hεd, hcap'⟩ := hcap Cn hCn Cm hCm 1 (by norm_num)
  refine ⟨1, min c₁ c₂, min (min (min ε₁ ε₂) εm) (min εc εd),
    by norm_num, lt_min hc₁ hc₂, lt_min (lt_min (lt_min hε₁ hε₂) hεm) (lt_min hεc hεd), ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQ hF hpd hRge hT
  have hA₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
      (min_le_left _ _))
  have hA₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
      (min_le_right _ _))
  have hAm : Work.BoseBoxFix.Adm v εm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAc : Work.BoseBoxFix.Adm v εc μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAd : Work.BoseBoxFix.Adm v εd μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  by_cases hcor : μ * Work.BoseFixB1.bV v μ u < 1000
  · exact hcorner μ hAc n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
      (lt_of_lt_of_le hQ (min_le_left _ _)) hF hpd hRge hT hcor
  · have h1000 : 1000 ≤ μ * Work.BoseFixB1.bV v μ u := le_of_not_gt hcor
    by_cases hthr : swhCapBound R Cm (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ)
        ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
    · obtain ⟨hm1, hm2⟩ := hmass μ hAm u hu (by simpa only [swhCapBound] using hthr)
      have h1' : (49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u ≤ Work.BoseFixB1.bW v h μ u := by
        have hc : (1 : ℝ) - 1 / 50 = 49 / 50 := by norm_num
        rwa [hc] at hm1
      have h2' : (49 / 50) * Submission.BoseGases.g0w0Mass h
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u := by
        have hc : (1 : ℝ) - 1 / 50 = 49 / 50 := by norm_num
        rwa [hc] at hm2
      have hreg : swhRegular v h μ u := ⟨h1', h2', h1000⟩
      exact hrow₁ μ hA₁ n Ψ u hu hΨc hsupp hnorm hn1 hn2
        (hrow₂ μ hA₂ n Ψ u hu hΨc hsupp hnorm hn1 hn2 hreg)
    · exact hcap' μ hAd n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
        (lt_of_lt_of_le hQ (min_le_right _ _)) hF hpd hRge hT h1000
        (fun hle => hthr hle)

end Work.BoseB1Cube
