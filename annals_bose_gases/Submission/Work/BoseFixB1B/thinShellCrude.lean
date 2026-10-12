import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.qLHSwordB_ge_neg_bandS
import Submission.Work.BoseFixB1S.PerBoxFibreB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.thinShellCrude` — the crude per-box bound on the thin shell

FS `final_v2.tex` l.4081–4100 (`eq:badset`): on the `μ ↦ 4μ` band the small box `B(u)` has
shortest side `≤ 2μ^{-1/3}`, and the crude per-box estimate on it is the error term that the
`I₋ → ℝ³` bookkeeping of the a-priori chapter consumes.

## The trichotomy (copied from `Work.BoseFixB1B.perBoxCrudeLower`)

For a box state `Φ`, `u`, put `CNT = Σᵢ∫Φ²1_{B(u)}(xᵢ)`, `N₀ = Σᵢ∫Φ²(boxPInd)²`,
`n₊ = cnPlusBoxInd` (so that `CNT = N₀ + n₊`, the *proved* `Work.BoseFixR.SlabCountSplit`),
`occChi = ∫Φ²Σᵢχ_{B(u)}(xᵢ)` (the `χ`-count, definitionally `Work.BoseFixB1.chiSum`) and
`crudeThreshold K = K(μ·chiMass(u) + 1)‖Φ‖²`:

* **excited arm** (`Work.BoseFixB1B.excitedArm`, PROVED): `½CNT ≤ n₊` ⟹ `sbWord ≥ 0`;
* **low-occupancy arm** (`Work.BoseFixB1B.lowArm`, PROVED): `occChi ≤ crudeThreshold K` ⟹
  the fibre line is within the allowance;
* **condensed arm** — the one input that is *not* available in the corpus
  (`Work.BoseFixR.SlabCondensedHalf` is `sorry`-tainted, and *without* the band restriction it is
  FALSE: the corner witness of `FINDING_perBoxCrudeB1.md`, which lives outside the band):
  `½CNT ≤ N₀` *and* `crudeThreshold K ≤ occChi` ⟹ the bound, **restricted to `u ∈ bandSet` and to
  low states**.

This file proves the reduction `thinShellCrude_of_condensed`: the requested `thinShellCrude`
follows from that (band-restricted, low-state) condensed arm, by exactly the trichotomy of
`perBoxCrudeLower`.

## Note on the import cycle

`Submission.Work.BoseFixB1B.perBoxCrudeLower` is imported here for its two **proved** arms
(`lowArm`, `excitedArm`) and the constants `kav`, `chiCs`; its own final theorem is *not* used.
The import closure of this module does **not** contain `Work.BoseFixB1B.trimOffInterior` (nor
`Work.BoseFixB1.smallBoxCollectedC_holds`), so `trimOffInterior` may import this file — see
`Submission/Work/BoseFixB1B/FINDING_trimOffInterior_gate.md` §4.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
  Work.SmallBoxSliding Work.BoseFixB1 Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The band-restricted condensed arm** (the single non-corpus input of `thinShellCrude`).

It is `Work.BoseFixR.SlabCondensedHalf` restricted to the `μ ↦ 4μ` band (`u ∈ bandSet`) and to
*low* states (`IsLowB`), with the two extra hypotheses of the trichotomy left visible:
`crudeThreshold K ≤ occChi` (high `χ`-occupancy) and `½CNT ≤ N₀` (half condensed).  The
delegated theorem `Work.BoseFixB1B.thinShellCondensedBand` proves exactly this content. -/
def ThinShellCondensedArm (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) (J : ℝ)
    (hJ : Work.UBB.lhyC ≤ J) : Prop :=
  ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u : E3,
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ) →
          (1 / 2 : ℝ) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                    (fun _ => (1 : ℝ)) (x i))
            ≤ (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Work.UBBInputs8.boxPInd
                  (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i
                  (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) →
          -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- The same arm, universally quantified over the data (the shape in which the reduction below
consumes it). -/
def CondArmAll : Prop :=
  ∀ {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J),
    ThinShellCondensedArm v h hv hv1 hvrad R hR hv_supp hav J hJ

/-- **The `χ`-count cap on the band** (the alternative single input).  For low states the
`χ_{B(u)}`-weighted count on the band is at most the allowance `μ·chiMass(u) + 1` times `‖Φ‖²`:
the `μ ↦ 4μ` band is where `χ_{B(u)} ≤ bandS`, and the state is spread out (`IsLowB`).

This is *weaker content* than `ThinShellCondensedArm` (it is a statement about the counts only,
not about the word) and it closes `thinShellCrude` **directly**: the PROVED core inequality
`Work.BoseFixB1B.sbCore` gives `sbWord ≥ −μ·kav·(a v)·occChi`.  The delegated theorem is
`Work.BoseFixB1B.thinShellChiCap`. -/
def ThinShellChiCapArm (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) (J : ℝ)
    (hJ : Work.UBB.lhyC ≤ J) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u : E3,
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-- The cap, universally quantified over the data. -/
def ChiCapAll : Prop :=
  ∀ {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J),
    ThinShellChiCapArm v h hv hv1 hvrad R hR hv_supp hav J hJ

/-- **The reduction from the `χ`-cap**: `thinShellCrude` follows from `ChiCapAll` through the
PROVED core inequality `Work.BoseFixB1B.sbCore` (`sbWord ≥ −μ·kav·(a v)·χ-count`), the cap, and
the identity `μ·kav·(a v)·(μ·chiMass + 1) = kav·(μ²(a v)·chiMass + μ(a v))`. -/
theorem thinShellCrude_of_chiCap (hcap : ChiCapAll)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u : E3,
            u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            u ∉ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εc, hεc, hcapb⟩ := hcap h hv hv1 hvrad hR hv_supp hav hJ
  obtain ⟨εs, hεs, hsb⟩ := sbCore (v := v) h hv hv1 hvrad hR hv_supp hav 0 (le_refl 0)
  refine ⟨min εc εs, kav, lt_min hεc hεs, kav_nonneg, ?_⟩
  intro μ hAdm hJK n Φ hlow u hu_band hu_notgood
  have hAdmc : Work.BoseBoxFix.Adm v εc μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdms : Work.BoseBoxFix.Adm v εs μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hμ : 0 ≤ μ := (Work.BoseFixB1.adm_mu_pos hAdm).le
  have hcap' : Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    hcapb μ hAdmc hJK n Φ hlow u hu_band
  have hcore : -μ * kav * (_root_.BoseGases.a v)
      * Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    have h := hsb μ hAdms n Φ u
    have h0 : (0 : ℝ) ^ 2 * μ * (_root_.BoseGases.a v)
        * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
      ring
    linarith [h, h0]
  have hchain : -μ * kav * (_root_.BoseGases.a v)
      * Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    simpa only [Work.BoseFixR.occChi, Work.BoseFixB1.chiSum] using hcore
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  have hbound : -μ * kav * (_root_.BoseGases.a v)
      * ((μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ -μ * kav * (_root_.BoseGases.a v)
        * Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ) := by
    have hcoef : 0 ≤ μ * kav * (_root_.BoseGases.a v) :=
      mul_nonneg (mul_nonneg hμ kav_nonneg) ha
    nlinarith [hcap', hcoef]
  have hgoal : -(kav * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v)))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = -μ * kav * (_root_.BoseGases.a v)
        * ((μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
    ring
  rw [hgoal]
  exact le_trans hbound hchain

/-- **The reduction.**  The requested `thinShellCrude` follows from the band-restricted,
low-state condensed arm, by the trichotomy of `Work.BoseFixB1B.perBoxCrudeLower`. -/
theorem thinShellCrude_of_condensed (hcond : CondArmAll)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u : E3,
            u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            u ∉ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εL, hεL, hlow⟩ := lowArm (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εA, hεA, harmA⟩ := excitedArm (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εB, KB, CB, hεB, hKB, hCB, harmB⟩ := hcond h hv hv1 hvrad hR hv_supp hav hJ
  obtain ⟨CL, hCL, hlowK⟩ := hlow (max 1 KB) (le_trans zero_le_one (le_max_left _ _))
  refine ⟨min (min εL εA) εB, max CB CL, lt_min (lt_min hεL hεA) hεB,
    le_trans hCB (le_max_left _ _), ?_⟩
  intro μ hAdm hJK n Φ hlow_state u hu_band hu_notgood
  have hAdmL : Work.BoseBoxFix.Adm v εL μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmA : Work.BoseBoxFix.Adm v εA μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmB : Work.BoseBoxFix.Adm v εB μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  set Jn : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hJndef
  set Chm : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hChmdef
  set XX : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * Chm + μ * (_root_.BoseGases.a v) with hXXdef
  set N0 : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i
        (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 with hN0def
  set Np : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hNpdef
  set CNT : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
          (fun _ => (1 : ℝ)) (x i) with hCNTdef
  have hsplit : CNT = N0 + Np := by
    rw [hCNTdef, hN0def, hNpdef]
    exact Work.BoseFixR.SlabCountSplit hℓ hd u hΦc
  have hXX0 : 0 ≤ XX := by
    rw [hXXdef, hChmdef]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _))
      (mul_nonneg (le_of_lt hμ) ha)
  have hJ0 : 0 ≤ Jn := by
    rw [hJndef]
    exact Work.BoseFixB1.normB_nonneg _
  -- gluing: a smaller constant gives a smaller lower bound
  have hglue : ∀ {C' : ℝ}, C' ≤ max CB CL →
      -(C' * XX) * Jn ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) →
      -(max CB CL * XX) * Jn ≤
        Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    intro C' hC' hb
    have h1 : C' * XX * Jn ≤ max CB CL * XX * Jn :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hXX0) hJ0
    nlinarith [hb, h1]
  by_cases hex : (1 / 2 : ℝ) * CNT ≤ Np
  · -- excited arm: `sbWord ≥ 0`
    refine le_trans ?_ (harmA μ hAdmA n Φ u (by simpa only [hCNTdef, hNpdef] using hex))
    have hmax0 : 0 ≤ max CB CL := le_trans hCB (le_max_left _ _)
    have h1 : 0 ≤ max CB CL * XX * Jn :=
      mul_nonneg (mul_nonneg hmax0 hXX0) hJ0
    nlinarith [h1]
  · -- condensed half: `n₀ ≥ cnt/2`
    have hnp : Np ≤ (1 / 2 : ℝ) * CNT := le_of_lt (not_le.mp hex)
    have hN0 : (1 / 2 : ℝ) * CNT ≤ N0 := by linarith [hsplit]
    by_cases hthr : Work.BoseFixR.crudeThreshold v (max 1 KB) μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
    · -- condensed arm (`lm:appinteractionestimate` at the sliding box, on the band)
      refine hglue (le_max_left _ _) (harmB μ hAdmB hJK n Φ hlow_state u hu_band ?_ ?_)
      · refine le_trans ?_ hthr
        simp only [Work.BoseFixR.crudeThreshold]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 KB) ?_) hJ0
        have hc0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ
            (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
          Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
        linarith [mul_nonneg (le_of_lt hμ) hc0]
      · simpa only [hCNTdef, hN0def] using hN0
    · -- low-occupancy arm
      refine hglue (le_max_right _ _) ?_
      refine hlowK μ hAdmL n Φ u ?_
      have hocc : Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixR.crudeThreshold v (max 1 KB) μ
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) := le_of_lt (not_le.mp hthr)
      simpa only [Work.BoseFixR.occChi, Work.BoseFixB1.chiSum] using hocc

theorem thinShellCrude {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u : EuclideanSpace ℝ (Fin 3),
            u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            u ∉ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  exact thinShellCrude_of_condensed (fun {v} h hv hv1 hvrad R hR hv_supp hav J hJ =>
    by
      -- PLACEHOLDER: the delegated input `Work.BoseFixB1B.thinShellCondensedBand`
      sorry)
    h hv hv1 hvrad hR hv_supp hav hJ

end Work.BoseFixB1B
