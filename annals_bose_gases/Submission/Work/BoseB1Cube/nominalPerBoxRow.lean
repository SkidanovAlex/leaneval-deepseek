import ChallengeDeps
import Submission.Work.BoseB1Cube.nomRowArbState
import Submission.Work.BoseB1Cube.nomRowLinFromPort
import Submission.Work.BoseB1Cube.nomRowSqWindowRow
import Submission.Work.BoseB1Cube.psiWeight_integral_four_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nominalPerBoxRow` — the target, plus the **assembly against the
# three named pieces** the target is equivalent to (piece B PROVED; pieces A and C delegated)

The target (statement byte-identical, below) is `Work.BoseB1Cube.PerBoxFNomSlots v h R` — FS
`thm:smallbox` at the sliding box in the nominal (indicator-count) spelling, at the two
chemical-potential slots `μp = μ` and `μp = 4μ`.

This module contains, in addition,

* `Work.BoseB1Cube.nominalPerBoxRow_of_pieces` — the assembly:
  `NomRowSqWindowRow ∧ NomRowLinWindowRow ∧ NomRowArbState ⟹ PerBoxFNomSlots v h R`;
* `Work.BoseB1Cube.nominalPerBoxRow_of_AC` — the same with **piece B discharged**, i.e. the
  target from the *two in-box windowed rows* alone;
* `Work.BoseB1Cube.psiWeightFourIntegral_holds` — the integral form of the doubled-slot
  `ψ`-comparison (from the PROVED `psiWeight_integral_four_le`).

The three pieces (definitions in `Submission/Work/BoseB1Cube/nomRowPieces.lean`, so that the
pieces' files and this file cannot form an import cycle):

* **piece A** `NomRowSqWindowRow` (DELEGATED, `Submission/Work/BoseB1Cube/nomRowSqWindowRow.lean`) —
  FS's `n''`-group bound (`final_v2.tex` l.4020–4040): the `Sq`-row
  `(¼(n/|B|−μ)² − ½μ²)∬w₁∫Ψ² − E∫Ψ² ≤ sbWordCube` for **in-box `ContDiff`** states in the count
  window `n ≤ Cn·μ|B(u)|`.  Its content is FS `lm:appinteractionestimate` + the refined Bogoliubov
  `eq:refinedaprioribog` at the *relative* (instance-level) constant — the chapter's missing
  analytic instrument.
* **piece C** `NomRowLinWindowRow` (DELEGATED, `.../nomRowLinWindowRow.lean`) — FS's `n'`-group
  bound (l.4019–4026): the **linear, error-free** row
  `(1/18)μ(n'/|B|)∬w₁∫Ψ² ≤ sbWordCube` for in-box `ContDiff` states in the two-sided window
  `Cn·μ|B| ≤ n' ≤ 2·Cn·μ|B|`.  Being error-free is what lets the descent sum it over the `m`
  blocks without multiplying `C`.
* **piece B** `NomRowArbState` — **PROVED** (`Work.BoseB1Cube.nomRowArbState`,
  `Submission/Work/BoseB1Cube/nomRowArbState.lean`, axiom-clean): from the in-box row (all `n`,
  slot `μ`) to the row for **every** `BoxState`, with fresh constants.  Its proof is the
  arity/slot passage `nomArbAssembly` (the demand splits over the slot sets `{i : x_i ∈ B(u)}`, the
  word is slot-additive, and the empty slot set is the degenerate term paid by `c₁' ≤ 1/4`) — see
  `FINDING_nominalPerBoxRow.md` §1bis.

## Why these pieces and nothing else

Write `N = ∫_{abox}Φ²`, `V = |B(u)|`, `W = ∬w_{1,B(u)}`, `𝔠 = ∫χ_B²`, `E = C(μp²aΓ𝔠 + μpa)`.
`PerBoxFNom` is `perBoxRow ≤ sbWordCube`, and `perBoxRow` differs from the state-level row
`nomRow` (`NomRowDefs.lean`) only in the argument of `ψ`: the *configuration-level* indicator
density `boxIndCount(x)/V` versus the *state-level* density `n/V`.  On an **in-box** state the two
coincide a.e. (`perBoxRow_eq_nomRow`, PROVED), so the in-box case is exactly `nomRow ≤ sbWordCube`
— which is FS's theorem and is delivered by **pieces A and C + the PROVED descent**
(`nomRow_all_of_windowRows` turns the two *windowed* pieces into the in-box row at *every* `n`).
The remaining content is the quantifier over *arbitrary* `BoxState`s, i.e. **piece B**, now
PROVED.

For the slot `4μ`: `perBoxFNom_slots_of_row` (PROVED) reduces the `4μ`-row to the `μ`-row at a
quarter of `c₁`, using the pointwise `psiWeight_four_le` (PROVED) and its integral form
`psiWeight_integral_four_le` (PROVED); `perBoxFNomSlots_of_slotMu` (PROVED) packages this, so the
target follows from the single-slot form `PerBoxFNomMu`.

## Constant bookkeeping (why the pieces compose)

`sbWordCube ≥ 0` is irrelevant here; what matters is that all four statements
(`nomRow ≤ sbWordCube`, `PerBoxFNom`, `PerBoxFNomMu`, `PerBoxFNomSlots`) are *monotone the easy
way* in `(c₁, C)`: decreasing `c₁` shrinks the left-hand side (`ψ ≥ 0`, `W ≥ 0`, `∫Φ² ≥ 0`), and
increasing `C` enlarges the right-hand side (`E ≥ 0`).  Hence the pieces' existential constants can
be merged by `min`/`max`, and the extension may return *fresh* `(c₁', C')` — which it must, since
the two-component (in-box / off-box) mixture of `FINDING_sectorPassageB1_REFUTED.md` §1 is *tight*
at the flat in-box component: it forces `c₁ ≤ 1/2 + o(1)` (the arithmetic is: the mixed state's
demand is `β(c₁ − 1/2)μ²WN + o(μ²WN)` while its word is `−w μ²W N/2`, with `w + β = 1`, so the row
needs `β(c₁ − 1/2) ≤ (1−β)δ₀/2 + o(1)`, `δ₀ = (M₂−M₁)/M₁ ≥ 0` PROVED).  FS's own theorem carries
the same restriction `0 < c < 1/2` — no contradiction, and `c₁' := min c₁ (1/4)` is admissible.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseKinLoc

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- The integral form of the doubled-slot `ψ`-comparison, as a `Prop` (the shape
`Work.BoseB1Cube.PsiWeightFourIntegral` of `nomRouteCube.lean`), from the PROVED
`Work.BoseB1Cube.psiWeight_integral_four_le`. -/
theorem psiWeightFourIntegral_holds : PsiWeightFourIntegral := by
  intro ℓ d μ u n Φ hℓ hd hμ hV hΦc
  exact Work.BoseB1Cube.psiWeight_integral_four_le (ℓ := ℓ) (d := d) (μ := μ) (u := u)
    (n := n) (Φ := Φ) hℓ hd hμ hV hΦc

/-- **THE ASSEMBLY.**  The three pieces (A: the count-windowed in-box `Sq`-row for `ContDiff`
states; C: the count-windowed in-box *linear* row; B: the extension to arbitrary `BoxState`s)
imply the target
`Work.BoseB1Cube.PerBoxFNomSlots v h R`.

Proof: piece C (the linear row) at the descent's window constant `Cn = 4` and piece A (the
`Sq`-row) at `Cn = 8` give, through the PROVED descent
`nomRow_all_of_windowRows` / `perBoxFNom_inBox_of_windowRows`, the in-box row at the slot `μ` for
**every** `n` (the descent takes the group size in `[4μ|B|, 8μ|B|]` and the remainder `≤ 8μ|B|`);
piece B removes the in-box hypothesis; and the PROVED slot doubling
`perBoxFNomSlots_of_slotMu` (with `psiWeightFourIntegral_holds`) adds the `4μ` slot. -/
theorem nominalPerBoxRow_of_pieces {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hA : NomRowSqWindowRow v h R) (hC : NomRowLinWindowRow v h R) (hB : NomRowArbState v h R) :
    PerBoxFNomSlots v h R := by
  classical
  -- ## piece C: the linear windowed row at the descent's window constant `Cn = 4`
  obtain ⟨εg, hεg, hGRP₀⟩ := hC 4 (by norm_num)
  -- ## piece A: the `Sq`-row at `Cn = 8` (so that its one-sided window `8μ|B|` covers the
  --    descent's remainder window `2·4·μ|B|`)
  obtain ⟨εr, Cr, hεr, hCr, hREM₀⟩ := hA 8 (by norm_num)
  -- ## the common threshold
  set εc : ℝ := min εg εr with hεcdef
  have hεc : 0 < εc := lt_min hεg hεr
  have hεc_le_g : εc ≤ εg := min_le_left _ _
  have hεc_le_r : εc ≤ εr := min_le_right _ _
  -- ## the in-box row at the slot `μ` for every `n` (PROVED descent)
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, hIn⟩ :=
    perBoxFNom_inBox_of_windowRows (v := v) h hv hv1 hvrad hR hv_supp hav
      (Cn := 4) (ε₀ := εc) (C := Cr) (by norm_num) hεc hCr
      (fun μ hAdm n' Ψ u hu hc hloc h1 h2 =>
        hGRP₀ μ (Work.BoseFixB1.Adm.mono hAdm hεc_le_g) n' Ψ u hu hc hloc h1 h2)
      (fun μ hAdm n' Ψ u hu hc hloc h2 =>
        hREM₀ μ (Work.BoseFixB1.Adm.mono hAdm hεc_le_r) n' Ψ u hu hc hloc
          (by linarith))
  -- ## piece B: the arbitrary-state row at the slot `μ`
  obtain ⟨ε₂, c₂, C₂, hε₂, hc₂, hC₂, hArb⟩ :=
    hB ε₁ c₁ C₁ hε₁ hc₁ hC₁ hIn
  -- ## the slot doubling
  exact perBoxFNomSlots_of_slotMu (v := v) h hv hvrad hR hv_supp psiWeightFourIntegral_holds
    ⟨ε₂, c₂, C₂, hε₂, hc₂, hC₂, hArb⟩

/-- **The residual, with piece B discharged.**  Piece B (`NomRowArbState`, the passage from
in-box states to arbitrary `BoxState`s) is PROVED and axiom-clean
(`Work.BoseB1Cube.nomRowArbState`, `Submission/Work/BoseB1Cube/nomRowArbState.lean`, via the
arity/slot assembly `nomArbAssembly`), so the target now rests on the **two** in-box windowed rows:

* `NomRowSqWindowRow` (piece A, DELEGATED) — FS's `n''`-group bound for in-box `ContDiff` states;
* `NomRowLinWindowRow` (piece C, DELEGATED) — FS's `n'`-group (linear, error-free) bound.

Both are count-windowed and in-box; the PROVED descent
`perBoxFNom_inBox_of_windowRows` turns them into the in-box row for **every** `n`, piece B removes
the in-box hypothesis, and the PROVED slot doubling `perBoxFNomSlots_of_slotMu` adds the `4μ`
slot. -/
theorem nominalPerBoxRow_of_AC {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hA : NomRowSqWindowRow v h R) (hC : NomRowLinWindowRow v h R) :
    PerBoxFNomSlots v h R :=
  nominalPerBoxRow_of_pieces h hv hv1 hvrad hR hv_supp hav hA hC
    (nomRowArbState h hv hv1 hvrad hR hv_supp hav)

/-- **The residual, with pieces A and B discharged.**  Piece A (`NomRowSqWindowRow`, the in-box
count-windowed `Sq`-row) is PROVED and axiom-clean (`Work.BoseB1Cube.nomRowSqWindowRow`,
`Submission/Work/BoseB1Cube/nomRowSqWindowRow.lean`), as is piece B (`Work.BoseB1Cube.nomRowArbState`,
the passage to arbitrary `BoxState`s).  Hence the target now rests on **piece C alone**:
`NomRowLinWindowRow` (`Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean`) — FS's `n'`-group
(linear, error-free) bound for in-box `ContDiff` states in the two-sided window
`Cn·μ|B(u)| ≤ n' ≤ 2·Cn·μ|B(u)|`. -/
theorem nominalPerBoxRow_of_C {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hC : NomRowLinWindowRow v h R) :
    PerBoxFNomSlots v h R :=
  nominalPerBoxRow_of_AC h hv hv1 hvrad hR hv_supp hav
    (nomRowSqWindowRow h hv hv1 hvrad hR hv_supp hav) hC

/-- FS `thm:smallbox` (`FSsrc/final_v2.tex:3907`) at the sliding box `B(u)` of the parameter block of `μ`, in FS's own **nominal (indicator-count) spelling** `n/|B|` (`Work.BoseB1Cube.PerBoxFNom`), at the two chemical-potential slots `μp = μ` (FS's `m(u) = 1` set `I₋`) and `μp = 4μ` (FS `eq:badset`, the boundary layer `goodSet ∖ interiorSet`), with one pair of constants for all `μ`, `n`, states and `u ∈ goodSet`. This is `Work.BoseB1Cube.PerBoxFNomSlots v h R`.

It is the single analytic residual of the FS route to the assigned node `Work.BoseB1Cube.CubeCrudeBand v h`: `Work.BoseB1Cube.cubeCrudeBand_of_perBoxFNomSlots` (PROVED, axiom-clean) gives the node from it, using only the PROVED `Work.BoseB1Cube.slidingGoodCube` (FS `eq:appsliding`) and `Work.BoseB1Cube.countWindowOfNominal` (FS l.4050-4200).

Its `μp = 4μ` half is *equivalent* to its `μp = μ` half modulo `Work.BoseB1Cube.perBoxFNom_slots_of_row` + `psiWeight_four_le` (both PROVED, axiom-clean) and the delegated `Work.BoseB1Cube.psiWeight_integral_four_le`; so the honest minimal content is FS's one-slot row (`Work.BoseB1Cube.PerBoxFNomMu`, also available).

WARNINGS for the prover (`FINDING_nomRouteCube.md` of this directory, sections 2-3):
1. The word `Work.BoseFixB1B.sbWordCube` is the *matched-single-cube-cutoff* word; its potential slot `sbPot = pairSum − μ·fibSum` carries the cube bump `chiSmallB` and its kinetic slot is `sbKinCube = bGapCoeff·n₊ + Work.BoseFixB1B.cubeSpectral` with `cubeSpectral = Work.UBBInputs8.tBwordKinInd chiSmallB (sbCut μ (a v))`. The PROVED `Work.BoseB1Cube.chainA2SlidingChiSmallB` (the sharp pairing chain at `chiSmallB`), `Work.BoseFixB1S.a0A2PaymentAdm_holds` (the rung-4 payment) and `Work.BoseFixB1B.slidingBogPortCube` (the sliding Bogoliubov port, `Work.BoseFixB1B.SlidingBogPortB`) all act on exactly this word, and the PROVED `Work.BoseB1Cube.sbWordSlot_ge_payPort`/`mDeltaMassCompare` combine them into the `(Sq)`-form of the row (see `FINDING_perBoxFNom_session5.md` sections 1 and 12).
2. The arXiv source of FS displays the small-box kinetic symbol as `[√−Δ − (dsℓ)⁻¹]_+^{-2}` (eq. `eq:appTB` l.3541, and `lm:appbogolubov` l.3765/3777/3786). That exponent is a **typo**: the proof of `lm:appbogolubov` itself (`final_v2.tex:3791`) expands that very operator in the `p`-basis and obtains the diagonal coefficient `𝒜(p) = (|B|/(n+1))[|p| − (dsℓ)⁻¹]²₊ + 2K_s a` (power **+2**), which is also what the Bogoliubov completion of the square at l.3800-3830 uses. The corpus's symbol `Submission.BoseGases.fsKinCoeff c r = [r − c]₊²` is therefore the correct one, and the PROVED port `Work.BoseFixB1B.slidingBogPortCube` reproduces FS's `eq:refinedaprioribog` right-hand side term for term (`−½(1+C(R/dℓ)²)(1+C(dsℓ)⁻¹a)ĝω̂(0)((n+1)n/|B|²)∫χ_B² − …`). Do NOT rebuild the chapter on the reciprocal reading: it would make the word's kinetic slot `~1/p²` (infrared-enhanced, vanishing at high momentum), which is inconsistent with `𝒜(p)` and would make the whole pairing machinery vacuous.
3. States with all pairs separated by `≥ R` (Jastrow holes) do NOT refute the row: on the high-momentum side the slot is `[r − sbCut]₊²`, and a hole of radius `r₀ ≥ R` whose ramp has width `w` carries boundary-layer kinetic energy `~ n² r₀²/w` (`w` bounded by the inter-particle spacing), which dominates `μ²W₁·n/|B|` by a positive power of the diluteness — see `FINDING_nomRouteCube.md` section 3 and the PROVED `Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet` (the slot at `c = 0` IS the `χ_B`-windowed Dirichlet energy, so the ramp is charged at full strength). -/
theorem nominalPerBoxRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.PerBoxFNomSlots v h R :=
  -- Assembled from the two PROVED pieces and piece C from the port-rung node
  -- `Work.BoseB1Cube.normNodeOfPort` (`nomRowLinFromPort.lean`); the older residual `SharpRow2`
  -- is strictly stronger than the node and is off this path
  -- (`FINDING_cubeCrudeBand_session6.md` §2–§3).
  nominalPerBoxRow_of_AC h hv hv1 hvrad hR hv_supp hav
    (nomRowSqWindowRow h hv hv1 hvrad hR hv_supp hav)
    (nomRowLinWindowRow_of_port h hv hv1 hvrad hR hv_supp hav)

end Work.BoseB1Cube
