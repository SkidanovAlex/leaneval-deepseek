import ChallengeDeps
import Submission.Work.BoseB1Cube.smallWinHolePD
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.smallWinNodes` — the box-region split of the single Bose leaf

Installation of the project lead's design (`sources/boseCubeEndgame/bose_cube_endgame.md` and
`sources/boseSWE/bose_smallwinholepd.{md,lean}`) into this area, in the node's own vocabulary, and
**reusing the `Work.BoseSWE` definitions verbatim** (so that a proof of the corresponding `BoseSWE`
node `Prop` is *definitionally* a proof of the node here — the two are related by `id`).

The leaf `Work.BoseB1Cube.SmallWinHolePD v h` (`smallWinHolePD.lean`) — `SmallWinNode`'s only open
input — is split by the box `u` into four regions:

* `Work.BoseSWE.SR2LocalNode` (N1) — the **per-point form** of the PROVED
  `Work.BoseB1Cube.normNode_of_sharpRow2`: `Dem ≤ SR2Rhs C ⟹ Dem ≤ sbWordCube`.  A pure copy of
  that proof with the global `SharpRow2` hypothesis replaced by the pointwise ledger row.
* `Work.BoseSWE.RegularSR2Node` (N2) — on **regular** boxes (`Work.BoseSWE.Regular u`) the ledger
  row `Dem ≤ SR2Rhs C` holds for **every** state of the count window, from the PROVED port
  `Work.BoseB1Cube.cubeBogPortRefinedR3` plus the box-data rows and the scalar ledger.
* `Work.BoseSWE.MassiveRegularNode` (N2′) — `χ_m ≥ d^{108}(ℓd)³` (massive box) implies `Regular`,
  through the PROVED AUTOCORR chain (`w1MassB_ge_of_autocorr`,
  `boxM2_sub_boxM1_ge_of_autocorr`).
* `swhThinNode` (N3) — **thin, non-degenerate** boxes (`χ_B² ≤ d^{79}` everywhere and
  `η·a·χ_m ≤ W`): the gap/payout dichotomy.
* `swhEdgeNode` (N4) — everything else: **the open residual**, boxes at the support edge of the
  opaque `ℓ`-bump where `χ_B` is not smooth on scale `R` over the bulk of its mass.

The assembly `swhSmallWinHolePD_of_nodes : N1 → N2 → N3 → N4 → SmallWinHolePD v h` is PROVED.

The (strictly weaker) fallback of the design — `SmallWinPropE` with the vanishing slack
`ErrE = C·a·μ·n·d^{80}` — is **not** what `SmallWinNode` states; its route is
`Work.BoseSWE.smallWinPropE_of_nodes` (N1 + N2 + N2′ + E).
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

/-- The demand `D = (1/18)·μ·(n/|B|)·W`. -/
noncomputable def swhDem (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ) (u : E3) : ℝ :=
  (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u

/-- The pair-dead hypothesis of `SmallWinHolePD`. -/
def swhPairDead (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Ψ : X n → ℝ) (u : E3) : Prop :=
  Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u Ψ
      - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u Ψ
    < swhDem v h μ n u

/-- **Regular box**: FS `eq:w1>`/`eq:w>g` at loss `1/50` (what the PROVED AUTOCORR chain
`w1MassB_ge_of_autocorr`/`boxM2_sub_boxM1_ge_of_autocorr` delivers when the autocorrelation defect
budget holds) and a large box (`μ|B| ≥ 1000`). -/
def swhRegular (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) : Prop :=
  (49 / 50) * (8 * Real.pi * _root_.BoseGases.a v)
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
    ≤ Work.BoseFixB1.bW v h μ u
  ∧ (49 / 50) * Submission.BoseGases.g0w0Mass h
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
    ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u
  ∧ 1000 ≤ μ * Work.BoseFixB1.bV v μ u

/-- **Thin box**: the cutoff is uniformly `≤ d^{79/2}` (`d^79 = (μa³)^{474/323}`), so that
`|B|·sup χ_B² ≤ a³(μa³)^{3/323}` is beaten by the gap's `X^{-13/4}`. -/
def swhThin (v : E3 → ℝ) (μ : ℝ) (u : E3) : Prop :=
  ∀ x : E3, (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u x) ^ 2 ≤ (Work.BoseFixB1.bD v μ) ^ 79

/-- The right side of `Work.BoseB1Cube.SharpRow2` at slack constant `C` (same expression as in
`nomRowLinWindowRow.lean`). -/
noncomputable def swhSR2Rhs (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (C μ : ℝ) {n : ℕ}
    (Ψ : X n → ℝ) (u : E3) : ℝ :=
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
`Work.BoseB1Cube.normNode_of_sharpRow2` (its proof uses `SharpRow2` only at the point; copy the
proof with this hypothesis in place of `hSR`).  *A theorem of this name is also being proved in the
`Work.BoseSWE` vocabulary (`Work.BoseSWE.SR2LocalNode`); a bridge is impossible inside
`SmallWinNode`'s cone (the `BoseSWE` cone carries `nomRouteCubeFree`, whose
`psiWeightFourIntegral_holds` clashes with `nominalPerBoxRow`'s), hence the local copy.* -/
def swhSR2LocalNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∀ C : ℝ, 0 ≤ C → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        swhDem v h μ n u ≤ swhSR2Rhs v h C μ Ψ u →
        swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **Node N2 (`RegularSR2Node`)** — on regular boxes the `SharpRow2` inequality holds for every
state of the window.  Proof: PROVED `cubeBogPortRefinedR3` (payer `½(1+κΓ)G·χ_m·(n+1)n/V²`,
credit `C a(μ+n/V)n₊`, band row `C a c³(n/V)χ_m`, no constant row), `Pc ≥ S²−S`, `S + n₊ = n`,
`G ≤ 8πa`, `bM2 − bW ≤ bW`, `c³/μ = X¹⁴⁵`, `Γ → 0`, and the scalar ledger of the design's md §2.3
(margin `f(4) ≥ 1.19` in units of `μ²W`).  (Local copy of `Work.BoseSWE.RegularSR2Node`; see the
note at `swhSR2LocalNode`.) -/
def swhRegSR2Node (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        swhRegular v h μ u →
        swhDem v h μ n u ≤ swhSR2Rhs v h C μ Ψ u

/-- **Node N2′ (`MassiveRegularNode`)** — which boxes are regular.  If
`χ_m ≥ d^{108}·(ℓd)³` (`= X^648·(ℓd)³`) then `swhRegular`.  Proof: the `L²` form of the PROVED
AUTOCORR defect, `χ_m − ∫χ_Bχ_B(·−z) ≤ (‖z‖²/2)·‖∇χ_B‖₂²`, with
`‖∇χ_B‖₂² ≤ 4‖D²A‖∫A c² + 2∫A²|∇c|²` (Glaeser `|∇A|² ≤ 2‖D²A‖A` for the opaque `C^∞` bump
`A = chiScale ℓ`, `‖D²A‖ = O(ℓ⁻²)`; explicit `|∇c| ≤ C c^{47/48}/(ℓd)` for the cube factor and
Hölder), i.e. `‖∇χ_B‖₂²/χ_m ≤ C(ℓ⁻²r^{-1/2} + (ℓd)⁻²r^{-1/48})`, `r = χ_m/(ℓd)³ ≥ X^648`, so
`δ = O((R/a)²X^2) → 0`; then `w1MassB_ge_of_autocorr`, `boxM2_sub_boxM1_ge_of_autocorr`,
`∫g₀ = 8πa`, `convScale ≤ 1`; and `χ_m > 0` ⇒ `B(u)` is clipped in at most one direction ⇒
`|B| ≥ μ^{-1/3}(ℓd)²` ⇒ `μ|B| ≥ X^{-98}`.  (Local copy of `Work.BoseSWE.MassiveRegularNode`.) -/
def swhMassiveRegNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ u : E3,
      u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
      (Work.BoseFixB1.bD v μ) ^ 108 * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
        ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u →
      swhRegular v h μ u

/-- **Node N3 (`ThinNondegNode`)** — thin, non-degenerate boxes: gap/payout dichotomy.  Gap
branch `n₊ ≥ q_W := 2.2·(n/V)·W/(K_g a)`; below it, `pairSum v ≥ pairSum (v ∧ K)
≥ (√A₂ᴷ − √(D̃ᴷ/2))²`, `D̃ᴷ ≤ 4K·sup χ_B²·(n−1)·n₊`, `A₂ᴷ ≥ (W − χ_m∫(g₀−K)₊)(S²−S)/(2V²)` makes
the state pair-alive (contradiction); the truncation level `K = K(η)` is fixed, and
`|B|·sup χ_B²·K ≤ θ²K_g a/9` is supplied by `swhThin` and `K_g = 0.454·X^{-13/4}`. -/
def swhThinNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
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
        swhPairDead v h μ Ψ u →
        swhThin v μ u →
        η * _root_.BoseGases.a v
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bW v h μ u →
        swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **Node N4 (`EdgeNode`) — the open residual.**  The hole row on boxes that are neither
regular nor thin-non-degenerate.  These are boxes at the support edge of the (opaque
`ContDiffBump`) ℓ-scale factor where `chiSmallB` is not smooth on scale `R` over the bulk of its
mass (the fleet's "needle", `θ = MΔ/(Gχ_m) < 1`) or is degenerate (`W < η·a·χ_m`).  Closable by
(a) an autocorrelation-sharp (`MΔ`-payer) port, (b) a localised Dyson bound, or (c) the reviewed
fallback error term.  For `v ∈ L^∞` its degenerate-thin part closes like N3 with `K = sup v`. -/
def swhEdgeNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ η c₀ ε₀ : ℝ, 0 < η ∧ 0 < c₀ ∧ 0 < ε₀ ∧
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
        swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **PROVED assembly**: N1–N4 give the leaf `Work.BoseB1Cube.SmallWinHolePD v h`. -/
theorem swhSmallWinHolePD_of_nodes {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (h1 : swhSR2LocalNode v h) (h2 : swhRegSR2Node v h) (h3 : swhThinNode v h)
    (h4 : swhEdgeNode v h) : SmallWinHolePD v h := by
  intro Cn hCn
  obtain ⟨η, c4, ε4, hη, hc4, hε4, hedge⟩ := h4 Cn hCn
  obtain ⟨c3, ε3, hc3, hε3, hthin⟩ := h3 Cn hCn η hη
  obtain ⟨ε2, C, hε2, hC, hreg⟩ := h2 Cn hCn
  obtain ⟨ε1, hε1, hloc⟩ := h1 Cn hCn C hC
  refine ⟨min c3 c4, min (min ε1 ε2) (min ε3 ε4), lt_min hc3 hc4,
    lt_min (lt_min hε1 hε2) (lt_min hε3 hε4), ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQ hF hpd
  have hm1 : Work.BoseBoxFix.Adm v ε1 μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hm2 : Work.BoseBoxFix.Adm v ε2 μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hm3 : Work.BoseBoxFix.Adm v ε3 μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm4 : Work.BoseBoxFix.Adm v ε4 μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  show swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ
  by_cases hR : swhRegular v h μ u
  · exact hloc μ hm1 n Ψ u hu hΨc hsupp hnorm hn1 hn2
      (hreg μ hm2 n Ψ u hu hΨc hsupp hnorm hn1 hn2 hR)
  · by_cases hT : swhThin v μ u ∧ η * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
      ≤ Work.BoseFixB1.bW v h μ u
    · exact hthin μ hm3 n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
        (lt_of_lt_of_le hQ (min_le_left _ _)) hpd hT.1 hT.2
    · exact hedge μ hm4 n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2
        (lt_of_lt_of_le hQ (min_le_right _ _)) hF hpd hR hT

end Work.BoseB1Cube
