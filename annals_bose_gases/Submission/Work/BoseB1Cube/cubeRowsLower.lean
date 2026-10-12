import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.boxDataGatesContDiff
import Submission.Work.BoseB1Cube.cubeBogPortRefinedR3
import Submission.Work.BoseB1Cube.cubeRowsDefs
import Submission.Work.BoseB1Cube.paySurplusSlotFreeContDiff
import Submission.Work.BoseB1Cube.sbWordSlotTelescopeContDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeRowsLower` — the **lower** rung/bookkeeping layer of the node

Session 10: the declarations that *were* in the holder
`Submission/Work/BoseB1Cube/cubeSmallNArb12ExHolds.lean` above its target — the assembly rung
`payPortR3Lower`, `sbWordCube_ge_payPortR3`, `payPortR3Lower_mono_C`, `item1Surplus`,
`cubeErrSlot_nonneg`, `cubeRowsOn_anti_eps`, `cubeRowsOn_mono_C`, `cubeRowsOn_rowTwo_anti_Cn`,
`rowOneSurplusW`, `cubeRowsOn_four_of_rowTwo` — are moved here **verbatim** (same names, same
namespace, no statement changed) so that they sit *below* the holder in the import order.

**Why.**  Lean forbids import cycles: a proof of the holder's target declaration
`Work.BoseB1Cube.cubeSmallNArb12ExHolds` can only use modules that the holder imports.  Every
consumer of the holder still sees these names through the holder's import of this module, so no
consumer changes.  The holder's own cone is exactly the cone of this module.

(Historical note from the holder's docstring, kept for provenance: this chapter's residual was for
several sessions believed to be the *pointwise* shift hypothesis `χ_B ⋆ χ_B ≥ (1−θ)·chiMass`; see
`FINDING_cubeSmallNArb12ExHolds_session9.md` §4b.  Session 10 analyses it in terms of the
**weighted** deficit `∫ (χ_B(x) − χ_B(x−z))² dx ≤ η·∫ χ_B²` (η a fixed constant), which is what the
proved `Work.BoseB1Cube.chiSmallB_shift_sq_le` actually controls.  See
`FINDING_cubeSmallNArb12ExHolds_session10.md`.)

## Session-9 status (READ `FINDING_cubeSmallNArb12ExHolds_session9.md` FIRST)

⚠ **ARCHITECTURE — the holder's `sorry` can only be filled from *below*.**  Lean forbids import
cycles, so no module that imports this file can be used to prove the target declaration here; and 42
files of this area do import it.  Hence the five definitions `CubeCoreSet`, `CubeRowsOn`,
`CubeRowsCore`, `CubeRowsNonCore` and the split `cubeSmallNArb12Ex_of_rows_split` now live in the
**lower** module `Submission/Work/BoseB1Cube/cubeRowsDefs.lean` (verbatim bodies, same names; this
file imports it), and the kernel-vanishing helpers in
`Submission/Work/BoseB1Cube/wSmallPairGlobalVanish.lean`, so that `cubeRowsWindowVanish` and
`cubeRowsThinBox` are holder-free.  See §5 of the session-9 FINDING for the remaining (mechanical)
import swaps and the final three-line assembly.

⭐ **The node is now exactly the two per-window rows** — `Work.BoseB1Cube.CubeSmallWinRows v h`
(small window `μ·PBW ≤ a v`) and `Work.BoseB1Cube.CubeShiftWinRows v h R` (non-small window, with
FS's flatness/shift hypothesis, which the now PROVED `Work.BoseB1Cube.windowShiftDichotomy`
supplies automatically) — via the **PROVED, axiom-clean**
`Work.BoseB1Cube.cubeSmallNArb12Ex_of_small_shift`
(`Submission/Work/BoseB1Cube/cubeRowsNonCoreAssembly.lean`).  The three other regions are closed:
the core by `Work.BoseB1Cube.cubeRowsOnCoreFour` (the proof of `cubeRowsOnCore` runs at `Cn := 4`),
the thin boxes by `Work.BoseB1Cube.cubeRowsOn_of_thinBox`
(`Submission/Work/BoseB1Cube/cubeRowsThinBox.lean` — `IsThinBox` kills `wSmall1Pair` identically, so
`PBW = 0` and `sbWordCube ≥ 0`), and the case split itself by `windowShiftDichotomy`.  Both Props
have **sockets** (`cubeSmallWinRows_of_rowsOfSmallWindow`, `cubeShiftWinRows_of_rowsOfShiftLarge`)
taking the conclusion types of the live nodes `rowsOfSmallWindow` / `rowsOfShiftLarge`.

⚠ **The count window of the ledger is vacuous**: `holeLedger{,Inc}`'s `(n : ℝ) ≤ 3·μ·bV` is never
used, and `Work.BoseB1Cube.sbWordCube_ge_holeLedgerIncNoWindow`
(`Submission/Work/BoseB1Cube/cubeHoleRungNoWindow.lean`, PROVED) is the node's rung with that
hypothesis deleted — **the "band arm" `3μV < n ≤ 2CnμV` is gone**.  All four box-data rows of the
shift branch are now PROVED (`shiftM2m`, `shiftGle`, plus the unconditional `hM1ub`/`hGub`), so
`CubeShiftWinRows` is mechanical; `CubeSmallWinRows` is the one genuinely open obligation
(§4b/§7 of the session-9 FINDING: the port's *full-`z`* mass row is not payable on caps of depth
`h ≪ R`, where the rows are nevertheless TRUE).

## Session-8 status (READ `FINDING_cubeSmallNArb12ExHolds_session8.md` FIRST)

⭐ **The residual of sessions 3–6 is unblocked.**  Session 5's verdict that the *middle shell* is
unprovable (because `Submission.BoseGases.chiBase` is an opaque `ContDiffBump` with no derivative
control) was about *quantitative* bound; a **qualitative Lipschitz constant suffices** at FS's
parameters, since `R/ℓ = (R/a)(μa³)^{163/323}` and `R/(ℓd) = (R/a)(μa³)^{157/323}` vanish
exponentially faster than `Γ = PBΓ v μ = (μa³)^{287/646}`.  The middle-shell shift hypothesis (SH)
of FS `lm:w2>w1` is now PROVED at the coefficient `1 − PBΓ` in

    Work.BoseB1Cube.chiShiftGe_of_chiLower    (Submission/Work/BoseB1Cube/chiShiftGe_of_chiLower.lean)

for every *fixed* `c > 0` with `chi ≥ c` on the support of the `(ℓd)`-scale factor, from the proved
inputs `chiSmallB_shift_sq_le` (`L²`-difference with `L` as a hypothesis), `chi_diff_bounds`
(`∃L`, Lipschitz — three copies exist, do not re-file), `chiSmall_L2`, plus the delegated
`chiShiftGateArith`, `chiAutocorr_ge_of_shiftSq`, `chiMass_ge_of_chiLower`.  See the session-8
FINDING §1–§2 for the exponent table and §4 for the updated four-region split, §5 for why
`windowShiftDichotomy` must be a genuine *dichotomy* (the danger zone
`C/(72πμ) < chiMass < C₂R²ℓd/(2Γ)` is non-empty).

## Session-7 status

The route has changed: the instrument is `Work.BoseFixB1S.SharpAIGood` (and its augmented twin
`boxQSum_ge_sharpInc`), *not* the payment/port rung.  `hcS2` is a **theorem**
(`Work.BoseB1Cube.boxFlatCount_sq_sub_le_boxPairCount`), so the sharp instruments apply to every
normalised in-box state.  The state-level rungs are proved in this directory:
`Work.BoseB1Cube.sbWordCube_ge_holeLedger` (`cubeHoleRung.lean`) and its income-augmented twin
`Work.BoseB1Cube.sbWordCube_ge_holeLedgerInc` (`cubeHoleRungInc.lean`), the latter built on
`Work.BoseB1Cube.holeLedgerInc` (`holeLedgerInc.lean`) and `Work.BoseFixB1S.boxQSum_ge_sharpInc`
(`sharpInc.lean`) and `Work.BoseFixB1S.A0A2QJointSharpInc`.  What is left is the ledger of §2/§3 of
that FINDING (regime-split in `Q`, with the `ω²`-pair income on the near-condensate window) and the
band arm `3μV < n ≤ 2CnμV`.

Holder of `Submission/Work/BoseB1Cube/cubeSmallNArb12ExHolds.lean`
(`Work.BoseB1Cube.cubeSmallNArb12ExHolds`, i.e. the two per-size state-independent rows of FS
`thm:smallbox` at the `chiSmallB` window = items (1)+(2) of `Work.BoseB1Cube.CubeSmallNArb`).

Read `Submission/Work/BoseB1Cube/FINDING_cubeSmallNArb12ExHolds_session5.md` FIRST (it supersedes
the session-4 note's §4quater — the `boxA2`-Cauchy–Schwarz route is *refuted* there — and identifies
the residual as the **shift hypothesis** `(SH) : (1−2Γ)∫χ² ≤ ∫χ(x)χ(x−z)` for `‖z‖ ≤ R`, i.e.
FS's `l:w2>w1`, which is provable on the core (plateau) and in the *outer boundary layer*
(super-polynomial flatness `chi_boundary_taylor`) but *not* in the middle shell; see that note for
the full diagnosis).  Then `FINDING_cubeSmallNArb12ExHolds_session4.md`.

## Session-5 status

Added in this file (all PROVED, `sorry`-free): `cubeErrSlot_nonneg`, `cubeRowsOn_anti_eps`,
`cubeRowsOn_mono_C`, `cubeRowsOn_rowTwo_anti_Cn`.  Delegated and (on success) available as
`Work.BoseB1Cube.two_boxM2_v_add_boxM1_ge` (`2·M_v + W ≥ 2·M₂`, geometry-free) and
`Work.BoseB1Cube.chiMass_le_of_boundaryLayer` (the outer-layer super-polynomial smallness of
`chiMass`).

## Session-4 status (read `FINDING_cubeSmallNArb12ExHolds_session4.md` FIRST)

The session-3 4-way split (core / window-vanishes / flat / excited) is refined:

* the **flat** member is *vacuous* (`flatBox_aeZero`: a nonzero flat in-box `ContDiff` state does
  not exist), so the residual is **all nonzero in-box states**, and the hidden parameter is the
  *count deficit* `bQ = n·bI − bFlat` (`Work.BoseFixB1S.b1sCountSplit`, PROVED);
* two exact identities reduce the ledger to algebra: `bFlat + bQ = n·bI` and
  `fibSum = (W/V)·bFlat + fibCross` (`fibCross` bounded by weighted Cauchy–Schwarz — delegated as
  `BoseB1Cube/fibSum_eq_flat_add_fibCross` / `BoseB1Cube/fibCross_le`);
* the assembly rung `sbWordCube_ge_payPortR3` is below the *truth*
  `sbPot = ½M_v(t²−t/V) − μWt` by `(¼W(t−μ)² + mrow)`-worth at a flat state, where
  `mrow = ½(1+κΓ)·G·(t²+t/V)` with `G = g0w0Mass·chiMass` — and on the frozen `chiSmallB` window the
  caps give `G/W ≈ 2R/h ≫ 1`, so the port's price for paying `boxA2` exceeds the whole row scale
  there.  That is the exact mechanism of the off-core residual;
* the naive weighted-Jensen pair row `pairSum ≥ ½(M_v/V²)Pc` is **FALSE** (see the FINDING §6).

The node is now reduced to: **(P_v)** (the payment with the pair kernel `wSmallPair v`; a one-slot
mechanical modification of the PROVED `paySurplusSlotFreeContDiff`) + **a cheap row for `boxA2` on
the cap windows** (`S ≳ (1−ε)·t·V`) + the pure-real ledger of the FINDING §5 + the two delegated
fibre lemmas.  Do **not** `declare_false`.

## This file

The two target rows are the *per-size* rows, so there is no descent to run: the target is
`∃ Cn C, 2 ≤ Cn ∧ 0 ≤ C ∧ CubeSmallNArb12 v h Cn C`, i.e. for every admissible `μ`, every
`u ∈ goodSet` and every in-box `ContDiff` state `Ψ`:

* (item (1), the `n'`-row) `(1/18)·μ·(n'/V)·W·∫Ψ² ≤ sbWordCube v h μ u Ψ` for
  `Cn·μ·V ≤ n' < (Cn+1)·μ·V`, and
* (item (2), the `n''`-row) `(¼((n''/V) − μ)² W − ½μ²W − C(μ² a Γ W + μa))·∫Ψ² ≤ sbWordCube v h μ u Ψ`
  for `n'' ≤ 2·Cn·μ·V`,

where `V = |B(u)| = bV v μ u`, `W = ∬w_{1,B(u)} = bW v h μ u`, `Γ = PBΓ v μ`, `a = a v`.

## The route (see the FINDING for the ledger and the constants)

The word splits (PROVED `sbWordSlotTelescopeContDiff`) as
`sbWordCube = bGapCoeff·n₊ + bSpectralCube + boxQSum`, the pairing **payment**
(`paySurplusSlotFreeContDiff`, PROVED) bounds `boxQSum` below by
`a0MainLocBox(V,μ,W,S) + ½((M₂−W)/V²)·Pc + bA2 − C·a·(μ+S/V)·n₊`, and the **refined Bogoliubov port
with the band row `R3` kept** (`cubeBogPortRefinedR3`, PROVED) bounds `bSpectralCube + bA2` below
by `−(mrow + C·a·(μ+n/V)·n₊ + C·a·c³·(n/V)·χ)` with `mrow = ½(1+κΓ)·g0w0Mass·((n+1)n/V²)·χ`.
Adding the two, the `bA2` cancels and the telescoping gives the *assembly rung*

    payPortR3Lower … ≤ sbWordCube v h μ u Ψ                (`sbWordCube_ge_payPortR3` below)

with a single merged constant `C` (monotonicity of the two credit columns in `C`, using `n₊ ≥ 0`).
The node's remaining work is the pure-real ledger of the two target rows against this rung, plus
the box data `(B1)`–`(B8)` of the FINDING §3bis.
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
set_option maxHeartbeats 4000000

/-- **The assembly rung of the per-size node**: the lower bound on `sbWordCube` obtained by adding
the PROVED pairing payment (`paySurplusSlotFreeContDiff`) and the PROVED refined Bogoliubov port
with the band row kept (`cubeBogPortRefinedR3`), at one and the same box, state and constant `C`.

In the box vocabulary `V = bV v μ u`, `W = bW v h μ u`, `χ = chiMass M ℓ d u`, `Γ = PBΓ v μ`,
`c = sbCut μ (a v)`, `S/Pc/n₊` the three counts of `Φ`:

    a0MainLocBox(V, μ, W, S) + ½((M₂ − W)/V²)·Pc
      + (bGapCoeff v μ − C·a·(μ + S/V) − C·a·(μ + n/V))·n₊
      − ½(1 + κ·Γ)·g0w0Mass h·(((n+1)n)/V²)·χ
      − C·a·c³·(n/V)·χ .

The `bA2` of the payment and of the port cancel, which is why this combination is stated. -/
noncomputable def payPortR3Lower (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : X n → ℝ) (u : E3) (κ C : ℝ) : ℝ :=
  Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
      (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Φ)
    + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
          - Work.BoseFixB1.bW v h μ u)
        / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ
    + Work.BoseFixB1.bGapCoeff v μ
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ
    - C * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ
    - C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ
    - (1 / 2) * (1 + κ * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
        * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
    - C * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
        * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u

/-- **`payPortR3Lower` dominates `sbWordCube`** — the assembly rung (payment + refined port +
telescoping), for every admissible `μ`, every `u ∈ goodSet`, every in-box normalised `ContDiff`
state.  All three inputs are PROVED corpus lemmas; only their combination is new here. -/
theorem sbWordCube_ge_payPortR3 {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ κ C : ℝ, 0 < ε₀ ∧ 0 ≤ κ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : X n → ℝ) (u : E3),
          u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          1 ≤ n → ContDiff ℝ (⊤ : ℕ∞) Φ →
          Work.BoseFixB1.bI v μ Φ = 1 →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
            Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) →
          payPortR3Lower v h μ n Φ u κ C ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
  classical
  -- ## the four inputs
  obtain ⟨ε₀A, CA, hε₀A, hCA0, hpay⟩ :=
    Work.BoseB1Cube.paySurplusSlotFreeContDiff h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₀P, κ, CP, hε₀P, hκ0, hCP0, hport⟩ :=
    Work.BoseB1Cube.cubeBogPortRefinedR3 h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₀G, hε₀G, hgates⟩ :=
    Work.BoseB1Cube.boxDataGatesContDiff h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₀R, hε₀R, hregime⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min (min ε₀A (min ε₀P (min ε₀G ε₀R))) 1, κ, max CA CP,
    lt_min (lt_min hε₀A (lt_min hε₀P (lt_min hε₀G hε₀R))) one_pos, hκ0,
    le_trans hCA0 (le_max_left _ _), ?_⟩
  intro μ hAdm n Φ u hu hn hΦc hnorm hsupp
  -- ## the extraction of the four thresholds (and of the diluteness bound `μ a³ ≤ 1`)
  have hA_le : min (min ε₀A (min ε₀P (min ε₀G ε₀R))) 1 ≤ ε₀A :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hP_le : min (min ε₀A (min ε₀P (min ε₀G ε₀R))) 1 ≤ ε₀P :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hG_le : min (min ε₀A (min ε₀P (min ε₀G ε₀R))) 1 ≤ ε₀G :=
    le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hR_le : min (min ε₀A (min ε₀P (min ε₀G ε₀R))) 1 ≤ ε₀R :=
    le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hAdmA : Work.BoseBoxFix.Adm v ε₀A μ := Work.BoseFixB1.Adm.mono hAdm hA_le
  have hAdmP : Work.BoseBoxFix.Adm v ε₀P μ := Work.BoseFixB1.Adm.mono hAdm hP_le
  have hAdmG : Work.BoseBoxFix.Adm v ε₀G μ := Work.BoseFixB1.Adm.mono hAdm hG_le
  have hAdmR : Work.BoseBoxFix.Adm v ε₀R μ := Work.BoseFixB1.Adm.mono hAdm hR_le
  have hεR : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀R := le_trans hAdm.2.1 hR_le
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have ha0 : (0 : ℝ) ≤ _root_.BoseGases.a v := hav.le
  -- ## the box-data gates
  obtain ⟨hVpos, hWdef, hM1nn, hM2, hPcnn, hcS2⟩ := hgates μ hAdmG n Φ hΦc u hu hnorm
  have hμV : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood hav hμ hdil1 hu
  -- the excited count is nonnegative (the two credit columns are monotone in `C`)
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Φ := by
    unfold Work.BoseFixB1S.boxQCount
    exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hχnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hSnn : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Φ := by
    unfold Work.BoseFixB1S.boxFlatCount
    exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
  -- ## the payment
  have hpay' := hpay μ hAdmA μ le_rfl n Φ hΦc u hu hVpos hμV hsupp hnorm hWdef hM1nn hM2 hPcnn hcS2
  -- ## the port
  have hport' := hport μ hAdmP n Φ u hu hn hΦc hnorm
  -- the port spells the excited count as `cnPlusBoxInd`; bring it to `boxQCount`
  have hQbr : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u) Φ
      = Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Φ := rfl
  rw [hQbr] at hport'
  -- ## the telescoping and the slot identity
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hregime μ hμ hεR
  have htel' := Work.BoseB1Cube.sbWordSlotTelescopeContDiff (v := v) (h := h) (R := R)
    (μp := μ) (μ := μ) (n := n) hv_supp hR hv hvrad hv1 hℓ hd hR16 hRχ u hVpos Φ hΦc
  have hslot : Work.BoseB1Cube.sbWordSlot v h μ μ u (Φ : X n → ℝ)
      = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    have hsp := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
      hAdm hΦc.continuous u hR16 hRχ
    show Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
        + (Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Φ : X n → ℝ)
            - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (Φ : X n → ℝ))
        = Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ) + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ)
    rw [hsp]
    simp only [Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
    ring
  -- ## the two `C`-monotonicities
  have hCAn : (0 : ℝ) ≤ μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u :=
    add_nonneg hμ.le (div_nonneg hSnn hVpos.le)
  have hCPn : (0 : ℝ) ≤ μ + (n : ℝ) / Work.BoseFixB1.bV v μ u :=
    add_nonneg hμ.le (div_nonneg (Nat.cast_nonneg n) hVpos.le)
  have hcredA : CA * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
      ≤ (max CA CP) * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u) := by
    have h1 : CA * (_root_.BoseGases.a v) ≤ (max CA CP) * (_root_.BoseGases.a v) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
    have h2 := mul_le_mul_of_nonneg_right h1 hCAn
    linarith [h2]
  have hcredP : CP * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
      ≤ (max CA CP) * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u) := by
    have h1 : CP * (_root_.BoseGases.a v) ≤ (max CA CP) * (_root_.BoseGases.a v) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) ha0
    have h2 := mul_le_mul_of_nonneg_right h1 hCPn
    linarith [h2]
  -- the two credit columns, already multiplied by the (nonnegative) excited count
  have hcredAQ : CA * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ
      ≤ (max CA CP) * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ :=
    mul_le_mul_of_nonneg_right hcredA hQnn
  have hcredPQ : CP * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ
      ≤ (max CA CP) * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Φ :=
    mul_le_mul_of_nonneg_right hcredP hQnn
  have hr3le : CP * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
          * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
      ≤ (max CA CP) * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
          * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := by
    have hcpos : (0:ℝ) < Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
      Work.BoseFixB1S.sbCut_pos hμ hav
    have hpos : (0:ℝ) ≤ (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
        * ((n : ℝ) / Work.BoseFixB1.bV v μ u) :=
      mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg n) hVpos.le)
    have h1 : CP * (_root_.BoseGases.a v) ≤ (max CA CP) * (_root_.BoseGases.a v) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) ha0
    have h2 := mul_le_mul_of_nonneg_right h1 hpos
    have h3 := mul_le_mul_of_nonneg_right h2 hχnn
    linarith [h3]
  -- ## the assembly
  unfold payPortR3Lower
  linarith [hpay', hport', htel', hslot, hcredAQ, hcredPQ, hr3le]

/-- **`payPortR3Lower` is antitone in the merged constant `C`**: both credit columns and the band
row `R3` are *subtracted* from the rung, and `n₊ ≥ 0`, `χ ≥ 0`.  Hence the assembled rung may be
instantiated at **any** `C ≥` the port's constant, which is what lets the ledger's constant gates
(`hCa`, `hCred`, ...) be met: they are compared against `C` alone. -/
theorem payPortR3Lower_mono_C {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    {u : E3} {κ C C' : ℝ} (hCC : C ≤ C') (ha : 0 ≤ _root_.BoseGases.a v) (hμ : 0 ≤ μ)
    (hc : 0 ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (hV : 0 < Work.BoseFixB1.bV v μ u)
    (hS : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Φ)
    (hQ : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Φ)
    (hχ : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) :
    payPortR3Lower v h μ n Φ u κ C' ≤ payPortR3Lower v h μ n Φ u κ C := by
  have hnn : (0:ℝ) ≤ (C' - C) *
      ((_root_.BoseGases.a v)
          * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ
        + (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Φ
        + (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
          * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) := by
    refine mul_nonneg (by linarith) ?_
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg (mul_nonneg ha (add_nonneg hμ (div_nonneg hS hV.le))) hQ
    · exact mul_nonneg (mul_nonneg ha (add_nonneg hμ (div_nonneg (Nat.cast_nonneg n) hV.le))) hQ
    · have h1 : (0:ℝ) ≤ (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
          * ((n : ℝ) / Work.BoseFixB1.bV v μ u) :=
        mul_nonneg (mul_nonneg ha (pow_nonneg hc 3))
          (div_nonneg (Nat.cast_nonneg n) hV.le)
      exact mul_nonneg h1 hχ
  have hid : payPortR3Lower v h μ n Φ u κ C' - payPortR3Lower v h μ n Φ u κ C
      = -((C' - C) *
        ((_root_.BoseGases.a v)
            * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
          + (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
          + (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
            * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)) := by
    unfold payPortR3Lower
    ring
  linarith [hid, hnn]

/-- **The item-(1) surplus** (pure real): on the window `t ∈ [Cn·μ, (Cn+1)·μ]` with `Cn ≥ 3`, the
linear row `(1/18)μtM₁` is dominated by `¼(t−μ)²M₁ − ½μ²M₁`.  This is what reduces target item (1)
to the same ledger as item (2) (the bracket `C(μ²aΓM₁+μa)` is paid *within* item (2)'s LHS). -/
theorem item1Surplus {μ t M₁ Cn : ℝ} (hμ : 0 < μ) (hM1 : 0 ≤ M₁) (hCn : 3 ≤ Cn)
    (hge : Cn * μ ≤ t) (hle : t ≤ (Cn + 1) * μ) :
    (1 / 18) * μ * t * M₁ ≤ (1 / 4) * (t - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁ := by
  have hμ0 : 0 ≤ μ := hμ.le
  have ht : 0 ≤ t := le_trans (by nlinarith [hμ0, hCn]) hge
  -- the two-sided window bounds
  have hup : (1 / 18) * μ * t * M₁ ≤ ((Cn + 1) / 18) * (μ ^ 2 * M₁) := by
    have h1 : μ * t ≤ μ * ((Cn + 1) * μ) := mul_le_mul_of_nonneg_left hle hμ0
    have h3 : (0 : ℝ) ≤ (1 / 18) * M₁ := by linarith only [hM1]
    have h2 : (1 / 18) * μ * t * M₁ ≤ (1 / 18) * (μ * ((Cn + 1) * μ)) * M₁ := by
      calc (1 / 18) * μ * t * M₁ = ((1 / 18) * M₁) * (μ * t) := by ring
        _ ≤ ((1 / 18) * M₁) * (μ * ((Cn + 1) * μ)) := mul_le_mul_of_nonneg_left h1 h3
        _ = (1 / 18) * (μ * ((Cn + 1) * μ)) * M₁ := by ring
    have h4 : (1 / 18) * (μ * ((Cn + 1) * μ)) * M₁ = ((Cn + 1) / 18) * (μ ^ 2 * M₁) := by ring
    linarith only [h2, h4]
  have hsq : ((Cn - 1) ^ 2 / 4) * (μ ^ 2 * M₁) ≤ (1 / 4) * (t - μ) ^ 2 * M₁ := by
    have h1 : (Cn - 1) * μ ≤ t - μ := by
      have h2 : (Cn - 1) * μ = Cn * μ - μ := by ring
      rw [h2]; linarith only [hge]
    have h2 : (0 : ℝ) ≤ (Cn - 1) * μ := by nlinarith only [hCn, hμ]
    have h3 : ((Cn - 1) * μ) ^ 2 ≤ (t - μ) ^ 2 := pow_le_pow_left₀ h2 h1 2
    have h4 : ((Cn - 1) ^ 2 / 4) * (μ ^ 2 * M₁) = (1 / 4) * (((Cn - 1) * μ) ^ 2 * M₁) := by ring
    have h5 : (0 : ℝ) ≤ 1 / 4 * M₁ := by linarith only [hM1]
    have h6 := mul_le_mul_of_nonneg_right h3 h5
    linarith only [h4, h6]
  have hconst : (Cn + 1) / 18 ≤ (Cn - 1) ^ 2 / 4 - 1 / 2 := by nlinarith only [hCn]
  have hM1t : (0 : ℝ) ≤ μ ^ 2 * M₁ := mul_nonneg (sq_nonneg μ) hM1
  have hmul : ((Cn + 1) / 18) * (μ ^ 2 * M₁)
      ≤ ((Cn - 1) ^ 2 / 4 - 1 / 2) * (μ ^ 2 * M₁) :=
    mul_le_mul_of_nonneg_right hconst hM1t
  have hfin : ((Cn - 1) ^ 2 / 4 - 1 / 2) * (μ ^ 2 * M₁)
      ≤ ((Cn - 1) ^ 2 / 4) * (μ ^ 2 * M₁) - (1 / 2) * μ ^ 2 * M₁ := by
    have h6 : ((Cn - 1) ^ 2 / 4 - 1 / 2) * (μ ^ 2 * M₁)
        = ((Cn - 1) ^ 2 / 4) * (μ ^ 2 * M₁) - (1 / 2) * (μ ^ 2 * M₁) := by ring
    linarith only [h6]
  linarith only [hup, hmul, hfin, hsq]

/-! ## Session 5: the constant-monotonicities of `CubeRowsOn`

`CubeRowsOn v h Cn C ε₀ P` is

* **antitone in `ε₀`** (a smaller diluteness threshold only removes admissible `μ`),
* **monotone in `C`** (the error bracket `μ²aΓ·PBW + μa` is nonnegative, so raising `C` lowers the
  demand),
* and its **second row is antitone in `Cn`** (a smaller `Cn` only shrinks the count window
  `n'' ≤ 2CnμV`).

These are what let a consumer descend the *core* constants delivered by `cubeRowsOnCore` (whose
`Cn` is only known to satisfy `4 ≤ Cn`) to `Cn = 4`, and raise `C` to match a non-core row proved
at a different constant.  Note that the *first* row is **not** monotone in `Cn` (its window
`[CnμV, (Cn+1)μV)` moves), which is why the descent of row 1 needs the surplus of
`item1Surplus` together with the smallness `C·a ≤ μW` (see
`FINDING_cubeSmallNArb12ExHolds_session5.md` §3). -/

/-- **The error slot is nonnegative**: `0 ≤ μ²·a·Γ·PBW + μ·a` on the admissible range. -/
theorem cubeErrSlot_nonneg {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (u : E3) :
    0 ≤ μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBW h μ u
      + μ * (_root_.BoseGases.a v) := by
  have hμ : 0 ≤ μ := hAdm.1.le
  have ha : 0 ≤ _root_.BoseGases.a v := hav.le
  have hΓ : 0 ≤ Work.BoseFixB1B.PBΓ v μ := by
    rw [Work.BoseFixB1B.PBΓ, Work.FockBridge.dlGamma]
    exact mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3)
      (Real.rpow_nonneg (mul_nonneg hμ (pow_nonneg ha 3)) _)
  have hW : 0 ≤ Work.BoseFixB1B.PBW h μ u := by
    rw [Work.BoseFixB1B.PBW]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp
      (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) u
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hΓ) hW)
    (mul_nonneg hμ ha)

/-- **`CubeRowsOn` is antitone in the diluteness threshold `ε₀`** (a smaller threshold only
restricts the admissible `μ`). -/
theorem cubeRowsOn_anti_eps {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {Cn C ε₀ ε₀' : ℝ}
    (hε : ε₀ ≤ ε₀') {P : ℝ → E3 → Prop} (hrows : CubeRowsOn v h Cn C ε₀' P) :
    CubeRowsOn v h Cn C ε₀ P :=
  fun μ hAdm u hu hP => hrows μ (Work.BoseFixB1.Adm.mono hAdm hε) u hu hP

/-- **`CubeRowsOn` is monotone in the error constant `C`** (raising `C` lowers the item-(2) demand
by the nonnegative bracket). -/
theorem cubeRowsOn_mono_C {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {Cn C C' ε₀ : ℝ} (hCC : C ≤ C') {P : ℝ → E3 → Prop}
    (hrows : CubeRowsOn v h Cn C ε₀ P) :
    CubeRowsOn v h Cn C' ε₀ P := by
  intro μ hAdm u hu hP
  refine ⟨fun h1 h2 Ψ hΨ hIn => (hrows μ hAdm u hu hP).1 h1 h2 Ψ hΨ hIn, ?_⟩
  intro n'' h1 Ψ hΨ hIn
  have hrow := (hrows μ hAdm u hu hP).2 h1 Ψ hΨ hIn
  have hE := cubeErrSlot_nonneg h hv hvrad hR hv_supp hav hAdm u
  have hI : 0 ≤ ∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hbracket : C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
        * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v))
      ≤ C' * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
        * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)) :=
    mul_le_mul_of_nonneg_right hCC hE
  nlinarith [hrow, mul_le_mul_of_nonneg_right hbracket hI, hI]

/-- **The second row of `CubeRowsOn` is antitone in `Cn`**: for `4 ≤ Cn' ≤ Cn` the count window
`n'' ≤ 2Cn'μV` is contained in `n'' ≤ 2CnμV`. -/
theorem cubeRowsOn_rowTwo_anti_Cn {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {Cn Cn' C ε₀ : ℝ}
    (hCn' : 4 ≤ Cn') (hle : Cn' ≤ Cn) {P : ℝ → E3 → Prop}
    (hrows : CubeRowsOn v h Cn C ε₀ P) :
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ → P μ u →
        (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 2 * Cn' * μ * Work.BoseFixB1B.PBBV v μ u →
          ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
            Work.BoseFixB1B.InBox v μ u Ψ →
            ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2
                  * Work.BoseFixB1B.PBW h μ u
                - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
                - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                      * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
                * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
              ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ) := by
  intro μ hAdm u hu hP n'' h1 Ψ hΨ hIn
  have hμ0 : 0 ≤ μ := hAdm.1.le
  have hV0 : 0 ≤ Work.BoseFixB1B.PBBV v μ u :=
    (Work.BoseFixB1.boxMass_pos_of_goodSet (Work.BoseFixB1.adm_ell_pos hAdm)
      (Work.BoseFixB1.adm_d_pos hAdm) hAdm.1 hu).le
  have h2 : (n'' : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u := by
    have hfac : 2 * Cn' * μ * Work.BoseFixB1B.PBBV v μ u
        ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u := by
      have h0 : (0 : ℝ) ≤ 2 * μ * Work.BoseFixB1B.PBBV v μ u :=
        mul_nonneg (mul_nonneg (by norm_num) hμ0) hV0
      nlinarith [h0, hle]
    linarith [h1, hfac]
  exact (hrows μ hAdm u hu hP).2 h2 Ψ hΨ hIn

/-- **The row-1 surplus against the item-(2) bracket** (pure real).  On the window
`t ∈ [4μ, 5μ]` the surplus `¼(t−μ)² − ½μ² − (1/18)μt ≥ 17/36·μ²` of `item1Surplus` absorbs the
whole error bracket `C(μ²aΓW + μa)`, so **item (1) at `Cn = 4` follows from item (2) at any
`Cn ≥ 4`** at the same `(C, ε₀)` — provided the two smallness gates
`C·a·Γ ≤ 1/2` and `2C·a ≤ μ·W` hold.  (On the *core* both gates are exactly what `coreSmallA`
supplies; off the core the second one can fail, which is why `FINDING_..._session5.md` §4 records
row 1 as a separate obligation there.) -/
theorem rowOneSurplusW {μ t W a Γ C : ℝ} (hμ : 0 < μ) (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hge : 4 * μ ≤ t) (hle : t ≤ 5 * μ)
    (hterm₁ : C * a * Γ ≤ 1 / 2) (hterm₂ : 2 * C * a ≤ μ * W) :
    (1 / 18) * μ * t * W + C * (μ ^ 2 * a * Γ * W + μ * a)
      ≤ (1 / 4) * (t - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W := by
  have h2 : C * (μ * a) ≤ μ ^ 2 * W / 2 := by nlinarith only [hterm₂, hW, hμ]
  have h3 : C * (μ ^ 2 * a * Γ * W) ≤ μ ^ 2 * W / 2 := by
    have h0 : (0 : ℝ) ≤ μ ^ 2 * W := mul_nonneg (sq_nonneg μ) hW
    have he : C * (μ ^ 2 * a * Γ * W) = (μ ^ 2 * W) * (C * a * Γ) := by ring
    rw [he]
    nlinarith only [hterm₁, h0]
  have h4 : (1 / 18) * μ * t * W ≤ (5 / 18) * (μ ^ 2 * W) := by
    have h0 : (0 : ℝ) ≤ μ * W := mul_nonneg hμ.le hW
    nlinarith only [hle, h0]
  have h5 : (7 / 4) * (μ ^ 2 * W) ≤ (1 / 4) * (t - μ) ^ 2 * W := by
    have h6 : 3 * μ ≤ t - μ := by linarith only [hge]
    have h7 : (0 : ℝ) ≤ t + 2 * μ := by linarith only [hge, hμ]
    have h8 : (3 * μ) ^ 2 ≤ (t - μ) ^ 2 := by nlinarith only [h6, h7, hμ]
    nlinarith only [h8, hW]
  nlinarith only [h2, h3, h4, h5]

/-- **Row 1 at `Cn = 4` from row 2 at `Cn ≥ 4`** at the same `(C, ε₀)`: on the `Cn = 4` window
`[4μV, 5μV)` the item-(1) demand plus the error bracket is dominated by the item-(2) demand
(`rowOneSurplusW`), and item (2) at `Cn = 4` is item (2) at `Cn` (the count window only grows).
The two gates are exactly what the *core* supplies (`coreSmallA`). -/
theorem cubeRowsOn_four_of_rowTwo {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {Cn C ε₀ : ℝ} (hCn : 4 ≤ Cn) (hC0 : 0 ≤ C) {P : ℝ → E3 → Prop}
    (hrows : CubeRowsOn v h Cn C ε₀ P)
    (hgate : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ → P μ u →
        C * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ ≤ 1 / 2 ∧
        2 * C * (_root_.BoseGases.a v) ≤ μ * Work.BoseFixB1B.PBW h μ u) :
    CubeRowsOn v h 4 C ε₀ P := by
  intro μ hAdm u hu hP
  obtain ⟨hg1, hg2⟩ := hgate μ hAdm u hu hP
  have hμ : 0 ≤ μ := hAdm.1.le
  have ha : 0 ≤ _root_.BoseGases.a v := hav.le
  have hΓ : 0 ≤ Work.BoseFixB1B.PBΓ v μ := by
    rw [Work.BoseFixB1B.PBΓ, Work.FockBridge.dlGamma]
    exact mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3)
      (Real.rpow_nonneg (mul_nonneg hAdm.1.le (pow_nonneg ha 3)) _)
  have hW : 0 ≤ Work.BoseFixB1B.PBW h μ u := by
    rw [Work.BoseFixB1B.PBW]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp
      (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) u
  have hV0 : 0 ≤ Work.BoseFixB1B.PBBV v μ u :=
    (Work.BoseFixB1.boxMass_pos_of_goodSet (Work.BoseFixB1.adm_ell_pos hAdm)
      (Work.BoseFixB1.adm_d_pos hAdm) hAdm.1 hu).le
  have hrow2 : ∀ {n'' : ℕ}, (n'' : ℝ) ≤ 2 * 4 * μ * Work.BoseFixB1B.PBBV v μ u →
      ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
        Work.BoseFixB1B.InBox v μ u Ψ →
        ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2
              * Work.BoseFixB1B.PBW h μ u
            - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                  * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
            * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    intro n'' h1 Ψ hΨ hIn
    have h0 : (0 : ℝ) ≤ μ * Work.BoseFixB1B.PBBV v μ u := mul_nonneg hμ hV0
    have hfac : 2 * 4 * μ * Work.BoseFixB1B.PBBV v μ u
        ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u := by
      have hstep : 2 * 4 * μ * Work.BoseFixB1B.PBBV v μ u
          = 8 * (μ * Work.BoseFixB1B.PBBV v μ u) := by ring
      have hstep2 : 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u
          = 2 * Cn * (μ * Work.BoseFixB1B.PBBV v μ u) := by ring
      rw [hstep, hstep2]
      exact mul_le_mul_of_nonneg_right (by linarith only [hCn]) h0
    exact (hrows μ hAdm u hu hP).2 (le_trans h1 hfac) Ψ hΨ hIn
  refine ⟨?_, hrow2⟩
  intro n' h1 h2 Ψ hΨ hIn
  have hI : 0 ≤ ∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hVpos : 0 < Work.BoseFixB1B.PBBV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet (Work.BoseFixB1.adm_ell_pos hAdm)
      (Work.BoseFixB1.adm_d_pos hAdm) hAdm.1 hu
  have hge : 4 * μ ≤ (n' : ℝ) / Work.BoseFixB1B.PBBV v μ u := by
    rw [le_div_iff₀ hVpos]
    exact h1
  have hle : (n' : ℝ) / Work.BoseFixB1B.PBBV v μ u ≤ 5 * μ := by
    rw [div_le_iff₀ hVpos]
    linarith only [h2]
  have hsur := rowOneSurplusW (hμ := hAdm.1) (hW := hW) (ha := ha) (hΓ := hΓ) (hC := hC0)
    hge hle hg1 hg2
  have hn'le : (n' : ℝ) ≤ 2 * 4 * μ * Work.BoseFixB1B.PBBV v μ u := by
    have h0 : (0 : ℝ) ≤ μ * Work.BoseFixB1B.PBBV v μ u := mul_nonneg hμ hV0
    have hstep : (4 + 1) * μ * Work.BoseFixB1B.PBBV v μ u
        ≤ 2 * 4 * μ * Work.BoseFixB1B.PBBV v μ u := by
      nlinarith only [h0]
    linarith only [h2, hstep]
  have hrow := hrow2 hn'le Ψ hΨ hIn
  have hmul : ((1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u) * Work.BoseFixB1B.PBW h μ u
        + C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBW h μ u
            + μ * (_root_.BoseGases.a v)))
        * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
      ≤ ((1 / 4) * (((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2 * Work.BoseFixB1B.PBW h μ u
          - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u)
        * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2) :=
    mul_le_mul_of_nonneg_right hsur hI
  nlinarith only [hmul, hrow]

end Work.BoseB1Cube
