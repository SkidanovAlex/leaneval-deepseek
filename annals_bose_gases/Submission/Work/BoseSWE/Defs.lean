import ChallengeDeps
import Submission.Work.BoseB1Cube.LargeWinNode
import Submission.Work.BoseB1Cube.nodeB1B_of_perBoxFNomMu
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.Defs` — the vocabulary of the **small-window hole-free (`E`) route** to
# `Work.BoseBoxFix.NodeB1B`

Subproject `BoseSWE` (curric-46 lead request).  The frozen small-window chapter rests on the single
open node `Work.BoseB1Cube.SmallWinHolePD` (the *edge* boxes, N4 of the design
`sources/boseSWE/bose_smallwinholepd.md`), which is not closable with the box-global instruments.
The reviewed fallback (`sources/boseSWE/bose_smallwinholepd_REVIEW.md` §3–§4) instead moves a
**vanishing slack** into the small-window row itself:

    Dem v h μ n u − C·(a v)·μ·n·(bD v μ)^80 ≤ sbWordCube v h μ u Ψ            (`SmallWinPropE`)

and then threads that slack through the *existing* downstream chain
(`NormNode → piece C → the `n = m n₀ + n''` descent → `PerBoxFNomMu → ledgerNom → NodeB1B`),
where it is absorbed by the ledger's already-present `E·μ(a v)κ·n‖Φ‖²` slot.

## The two facts that make this safe

* every box is either **light** (`χ_m < d^108(ℓd)³`, where the slack `∝ aμn d^80` dominates the
  whole demand, `d`-powers beating `d^{108}` in `|B|`) or **massive**, and a massive box is
  `Regular`, where the PROVED port `Work.BoseB1Cube.cubeBogPortRefinedR3` pays the row with **no**
  slack at all;
* the slack is proportional to `n`, so the descent `n = m n₀ + n''` sums it as
  `Σ_j C a μ n_j d^80 ≤ C a μ n d^80` — it does *not* get multiplied by the group count.

## Contents

Definitions (all bodies copied from the reviewed design file; `Dem`, `ErrE`, `SR2Rhs`,
`SR2LocalNode`, `RegularSR2Node`, `MassiveRegularNode`, `LightBoxENode`, `SmallWinPropE`,
`NormNodeE`, `NomRowLinWindowRowE`, `PerBoxFNomE`, `PerBoxFNomMuE`, `PerBoxFNomSlotsE`) and the two
assemblies that are pure logic:

* `Work.BoseSWE.smallWinPropE_of_nodes` — N1 + N2 + N2′ + E give `SmallWinPropE`;
* `Work.BoseSWE.normNodeE_of_smallWinPropE` — the PROVED `LargeWinNode` + `SmallWinPropE` give
  `NormNodeE` (the `μ·bW ≤ a v` case is the slack row, the rest is the PROVED large-window arm).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The demand and the slack -/

/-- The demand `D = (1/18)·μ·(n/|B(u)|)·W` of the small-window row. -/
def Dem (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ) (u : E3) : ℝ :=
  (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u

/-- The fallback slack `E = C·(a v)·μ·n·d^80` (`d^80 = (μ(a v)³)^{480/323}`): `n`-proportional
with a coefficient that vanishes in the diluteness. -/
def ErrE (v : E3 → ℝ) (C μ : ℝ) (n : ℕ) : ℝ :=
  C * _root_.BoseGases.a v * μ * (n : ℝ) * (Work.BoseFixB1.bD v μ) ^ 80

/-! ## 2. The strong row `SharpRow2`'s right-hand side, and its per-point form (N1) -/

/-- The right side of `Work.BoseB1Cube.SharpRow2` at slack constant `C` (same expression as in
`nomRowLinWindowRow.lean`). -/
def SR2Rhs (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (C μ : ℝ) {n : ℕ}
    (Ψ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
      (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
    + Work.BoseFixB1.bA2 v h μ Ψ u
    + Work.BoseFixB1S.bSpectralCube v μ Ψ u
    + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
          - Work.BoseFixB1.bW v h μ u)
        / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
    + C * (_root_.BoseGases.a v) * μ
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ

/-- **Node N1 (`SR2LocalNode`)** — the per-point form of the PROVED
`Work.BoseB1Cube.normNode_of_sharpRow2` (its proof uses `SharpRow2` only at the point). -/
def SR2LocalNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∀ C : ℝ, 0 ≤ C → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        Dem v h μ n u ≤ SR2Rhs v h C μ Ψ u →
        Dem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-! ## 3. The box dichotomy: regular boxes (N2), which boxes are regular (N2′), and light boxes (E) -/

/-- **Regular box**: the `w₁`-mass and the `w₂ − w₁` mass comparisons of FS `eq:w1>`/`eq:w>g` at
loss `1/50` (what the PROVED AUTOCORR chain `w1MassB_ge_of_autocorr` /
`boxM2_sub_boxM1_ge_of_autocorr` delivers) and a large box (`μ|B| ≥ 1000`). -/
def Regular (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) : Prop :=
  (49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
    ≤ Work.BoseFixB1.bW v h μ u
  ∧ (49 / 50) * Submission.BoseGases.g0w0Mass h
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
    ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u
  ∧ 1000 ≤ μ * Work.BoseFixB1.bV v μ u

/-- **Node N2 (`RegularSR2Node`)** — on regular boxes the `SharpRow2` inequality holds for every
state of the window (PROVED port `cubeBogPortRefinedR3` + the scalar ledger of the design md §2.3,
margin `f(4) = 1.187` in units of `μ²W`). -/
def RegularSR2Node (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        Regular v h μ u →
        Dem v h μ n u ≤ SR2Rhs v h C μ Ψ u

/-- **Node N2′ (`MassiveRegularNode`)** — a *massive* box (`χ_m ≥ d^108·(ℓd)³`) is regular. -/
def MassiveRegularNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ u : E3,
      u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
      (Work.BoseFixB1.bD v μ) ^ 108 * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
        ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u →
      Regular v h μ u

/-- **Node E (`LightBoxENode`)** — on a light box (`χ_m < d^108(ℓd)³`) the slack pays everything:
`μ·fibSum` and the demand are `≤ C·a·μ·n·χ_m/|B|`-small, `pairSum ≥ 0` and `cubeSpectral ≥ 0`, and
`χ_m/|B| ≤ d^31·(d^80)`-type arithmetic closes against the gate. -/
def LightBoxENode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
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
        Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
          < (Work.BoseFixB1.bD v μ) ^ 108 * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 →
        Dem v h μ n u - ErrE v C μ n ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-! ## 4. `SmallWinPropE`: the small-window row with the vanishing slack -/

/-- **`SmallWinPropE`** — `SmallWinProp` with the slack `ErrE`: the small-window row of
`Work.BoseB1Cube.SmallWinProp` with `Dem` relaxed to `Dem − C(a v)μn d^80`. -/
def SmallWinPropE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
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
        Dem v h μ n u - ErrE v C μ n ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **PROVED assembly** (pure case logic): N1 + N2 + N2′ + E give the fallback row. -/
theorem smallWinPropE_of_nodes {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v)
    (h1 : SR2LocalNode v h) (h2 : RegularSR2Node v h) (h2' : MassiveRegularNode v h)
    (hE : LightBoxENode v h) : SmallWinPropE v h := by
  intro Cn hCn
  obtain ⟨εE, CE, hεE, hCE, hlight⟩ := hE Cn hCn
  obtain ⟨ε2, C, hε2, hC, hreg⟩ := h2 Cn hCn
  obtain ⟨ε1, hε1, hloc⟩ := h1 Cn hCn C hC
  obtain ⟨εm, hεm, hmass⟩ := h2'
  refine ⟨min (min ε1 ε2) (min εm εE), CE, lt_min (lt_min hε1 hε2) (lt_min hεm hεE), hCE, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
  have hm1 : Work.BoseBoxFix.Adm v ε1 μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hm2 : Work.BoseBoxFix.Adm v ε2 μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmm : Work.BoseBoxFix.Adm v εm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmE : Work.BoseBoxFix.Adm v εE μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  by_cases hM : (Work.BoseFixB1.bD v μ) ^ 108
        * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
      ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
  · have hrow := hloc μ hm1 n Ψ u hu hΨc hsupp hnorm hn1 hn2
      (hreg μ hm2 n Ψ u hu hΨc hsupp hnorm hn1 hn2 (hmass μ hmm u hu hM))
    have hE0 : 0 ≤ ErrE v CE μ n := by
      unfold ErrE
      have hd : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by positivity
      have hμ : 0 ≤ μ := le_of_lt hAdm.1
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCE hav.le) hμ) hn) hd
      simpa [mul_assoc] using this
    linarith
  · exact hlight μ hmE n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 (lt_of_not_ge hM)

/-! ## 5. `NormNodeE`: the node at normalised states, downstream of `SmallWinPropE` -/

/-- `NormNode` (the normalised small-window row) with the slack. -/
def NormNodeE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        Dem v h μ n u - ErrE v C μ n ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **F1 (PROVED)**: `SmallWinPropE` + the PROVED `LargeWinNode` give `NormNodeE`.  The
`μ·bW ≤ a v` branch is the slack row, the complementary branch is the PROVED large-window arm
(which needs no slack, so `ErrE ≥ 0` only helps). -/
theorem normNodeE_of_smallWinPropE {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hE : SmallWinPropE v h) : NormNodeE v h := by
  intro Cn hCn
  obtain ⟨εs, C, hεs, hC, hS⟩ := hE Cn hCn
  obtain ⟨εl, hεl, hL⟩ :=
    Work.BoseB1Cube.LargeWinNode (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn
  refine ⟨min εs εl, C, lt_min hεs hεl, hC, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hI hnlo hnhi
  by_cases hw : μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v
  · exact hS μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)) n Ψ u hu hw hΨ hsupp hI hnlo hnhi
  · have hrow := hL μ (Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)) n Ψ u hu hw hΨ hsupp hI
      hnlo hnhi
    have hE0 : 0 ≤ ErrE v C μ n := by
      unfold ErrE
      have hμ : 0 ≤ μ := le_of_lt hAdm.1
      have hd : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by positivity
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hav.le) hμ)
        (Nat.cast_nonneg n)) hd
      simpa [mul_assoc] using this
    show Dem v h μ n u - _ ≤ _
    unfold Dem
    linarith

/-! ## 6. The downstream vocabulary (normalised row, piece C, the two-slot per-box row) -/

/-- Piece C (`Work.BoseB1Cube.NomRowLinWindowRow`) with the slack: the linear count-windowed row
for in-box `ContDiff` states, `(Dem − ErrE)·∫Ψ² ≤ sbWordCube`. -/
def NomRowLinWindowRowE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : X n' → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          Ψ x ≠ 0 → ∀ i : Fin n', x i ∈ Submission.BoseGases.dlBox
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        Cn * μ * Work.BoseB1Cube.nomV v μ u ≤ (n' : ℝ) →
        (n' : ℝ) ≤ 2 * Cn * μ * Work.BoseB1Cube.nomV v μ u →
        ((1 / 18) * μ * ((n' : ℝ) / Work.BoseB1Cube.nomV v μ u) * Work.BoseB1Cube.nomW v h μ u
            - ErrE v C μ n')
            * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- `Work.BoseB1Cube.PerBoxFNom` with the slack `CE·(a v)·μ·n·d^80·‖Φ‖²` on its left side (the
total particle number `n`). -/
def PerBoxFNomE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C CE : ℝ) (μp μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (u : E3) :
    Prop :=
  c₁ * (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μp
              (Work.BoseB1Cube.boxIndCount (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
                / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)))
    - (1 / 2) * μp ^ 2 * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * (μp ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                  * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + μp * (_root_.BoseGases.a v) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    - ErrE v CE μ n * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- The single-slot (slot `μ`) form of `PerBoxFNomE`. -/
def PerBoxFNomMuE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C CE : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧ 0 ≤ CE ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        PerBoxFNomE v h R c₁ C CE μ μ n Φ u

/-- The two-slot form of `PerBoxFNomE` (slots `μ` and `4μ`), i.e. the E-twin of
`Work.BoseB1Cube.PerBoxFNomSlots`.  This is the shape the ledger `ledgerNom`/`countWindowOfNominal`
consume. -/
def PerBoxFNomSlotsE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C CE : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧ 0 ≤ CE ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ∀ μp : ℝ, (μp = μ ∨ μp = 4 * μ) →
          PerBoxFNomE v h R c₁ C CE μp μ n Φ u

/-! ## 7. Consistency checks (this module is `sorry`-free; these are definitional identities) -/

/-- At `CE = 0` the E-row is the corpus row, definitionally. -/
example (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C μp μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (u : E3) :
    PerBoxFNomE v h R c₁ C 0 μp μ n Φ u ↔ Work.BoseB1Cube.PerBoxFNom v h R c₁ C μp μ n Φ u := by
  unfold PerBoxFNomE Work.BoseB1Cube.PerBoxFNom ErrE
  simp

end Work.BoseSWE

#print axioms Work.BoseSWE.smallWinPropE_of_nodes
#print axioms Work.BoseSWE.normNodeE_of_smallWinPropE
