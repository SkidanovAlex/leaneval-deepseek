import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy
import Submission.Work.BoseB1Cube.newtonSelfEnergy
import Submission.Work.BoseB1Cube.nomPortRows
import Submission.Work.BoseB1Cube.nomRowPieces
import Submission.Work.BoseB1Cube.sbCut_cube_le_mu_gamma
import Submission.Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin
import Submission.Work.BoseFixB1.PBGamma_le_of_dilute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB1Cube/nomRowSqWindowRow` — FS `thm:smallbox`'s per-`n''`-group row
# (the nominal `Sq`-form), and the assembly that reduces it to the joint razor `RazorNom`

Holder of the node `Work.BoseB1Cube.NomRowSqWindowRow`
(`Submission/Work/BoseB1Cube/nomRowPieces.lean`).  **Read
`Submission/Work/BoseB1Cube/FINDING_nomRowSqWindowRow_cubeSpectral.md` first**: the row is TRUE
(it is FS's per-`n''`-group estimate, the residual `hREM` of the PROVED descent
`nomRow_descentStep`), and the fleet's earlier "the spectral slot cannot pay the pair-hole states"
verdicts rest on a `ℓ³`-mis-estimate of `cubeSpectral` that is refuted by the *proved* sharp rung
`Work.BoseFixB1B.sbWordCube_ge_sharpRung` and the *proved* port
`Work.BoseFixB1B.slidingBogPortPrescribedEpsSmallB`.

## The two pieces this file records

* **`sbWordCube_eq_rows`** — the *definitional* reduction of the word to the five rows the ledger
  uses: `sbWordCube = bGapCoeff·n₊ + cubeSpectral + pairSum − μ·fibSum` (from `sbPot_split` and the
  definitions of `sbWordCube`, `sbKinCube`, `boxQCount`).
* **`halfSq_arith`** — the elementary inequality `¼u² + ½u − ¼ ≤ ½u²` (`= ¼(u−1)² ≥ 0`) which is
  why the razor's payment `½·W·(n/|B|)²` at the mean-field scale covers the `Sq`-row's demand
  bracket `¼(t−μ)² − ½μ² + μ·fibSum` in the pair-dead branch (equality exactly at `t = μ`, the
  homogeneity of FS's proof).

## The remaining input

`Work.BoseB1Cube.RazorNom v h R` (`nomRazorDefs.lean`, delegated as
`Submission/Work/BoseB1Cube/nomRowRazor.lean`): the *joint* pair-or-kinetic razor, i.e.
`½·W·(n/|B|)²·I ≤ cubeSpectral + pairSum + C·(μ²aΓχ + μa)·I + C·a(μ + n/V)·n₊`.  With the PROVED
manifest fibre bound `Work.BoseFixB1S.fibSum_le_manifest`, `S + Q = n·I`
(`Work.BoseFixR.SlabCountSplit` + the in-box support), `W ≥ 0` (`w1MassB_nonneg`), and the
`ε_T`-gap gate `Work.BoseFixB1S.PerBoxGapAbsorbB1` (`bGapCoeff ≥ K·(a v)μ` for every prescribed
`K`), the target follows by the arithmetic of §2 of the FINDING (the remaining bookkeeping is the
`ε₀`-smallness that lets the gap row absorb `C·(a v)(μ + n/V)n₊` and the `β`-rows).
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseKinLoc Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open Classical

/-- **The elementary arithmetic of the `Sq`-form**: `¼u² + ½u − ¼ ≤ ½u²` for every real `u`
(equivalently `¼(u−1)² ≥ 0`).  This is the comparison that lets the razor's payment
`½·W·(n/|B|)²·I` cover the pair-dead branch of the target row. -/
theorem halfSq_arith (u : ℝ) : (1 / 4) * u ^ 2 + (1 / 2) * u - (1 / 4) ≤ (1 / 2) * u ^ 2 := by
  nlinarith [sq_nonneg (u - 1)]

/-- **The word as its five rows** (definitional, via `sbPot_split`):

    sbWordCube v h μ u Φ
      = bGapCoeff v μ · n₊(B(u)) + cubeSpectral v μ Φ u
          + pairSum v M ℓ d u Φ − μ · fibSum h M ℓ d u Φ .

`n₊(B(u))` is written as `boxQCount (nomV v μ u) (sideAt μ (a v)) (dlBox … ) Φ` (definitionally
`cnPlusBoxInd` at the sliding parameters). -/
theorem sbWordCube_eq_rows {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R εr μ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hadmr : Work.BoseBoxFix.Adm v εr μ)
    (hRd : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) (u : E3) :
    Work.BoseFixB1B.sbWordCube v h μ u Φ
      = Work.BoseFixB1.bGapCoeff v μ
          * Work.BoseFixB1S.boxQCount (nomV v μ u) (sideAt μ (a v))
              (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ
        + Work.BoseFixB1B.cubeSpectral v μ Φ u
        + Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u Φ
        - μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u Φ := by
  have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hadmr hΦc u hRd hRχ
  unfold Work.BoseFixB1B.sbWordCube
  rw [hsplit]
  simp only [Work.BoseFixB1B.sbKinCube, Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd,
    Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bV, Work.BoseFixB1.bA,
    Work.BoseFixB1.bM, Work.BoseB1Cube.nomV, Work.SmallBoxSliding.boxMass,
    Work.UBBInputs8.boxQInd]
  ring

/-- **The exact cancellation of the nominal ledger.**  The razor's payment bracket
`¼τ² + ½τμ − ¼μ²` minus the fibre's flat part `μτ` equals the `Sq`-demand's bracket
`¼(τ−μ)² − ½μ²` — *identically*, with no loss.  This is why the ledger of §5 of
`FINDING_nomRowSqWindowRow_cubeSpectral.md` closes as soon as the razor of `nomRazorDefs.lean` is
available: the two `τ²`-terms cancel and only the smallness rows (`Crz(μ²aΓχ+μa)`, the excitation
rows, the fibre's `√`-row) remain to be paid by the gap row and the error slot. -/
theorem ledger_identity (μ τ W I : ℝ) :
    ((1 / 4) * τ ^ 2 + (1 / 2) * τ * μ - (1 / 4) * μ ^ 2) * W * I - μ * (τ * W * I)
      = ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2) * W * I := by
  ring

/-- **The pure-real ledger of `FINDING_nomRowSqWindowRow_cubeSpectral.md` §7** — the *whole* of
the arithmetic that turns the joint razor plus the manifest fibre row plus the `ε_T`-gap
smallness into the target's `Sq`-row.

`τ = n/|B(u)|`, `W = nomW` (`= w1MassB`), `I = ∫_{abox}Ψ²`, `Mslot = μ²(a v)Γχ + μ(a v)` (the error
slot), `nq = boxQCount`, `cs = cubeSpectral`, `P = pairSum`, `fib = fibSum`, `Qrows` the manifest
bound's excitation rows (so that `μ·fib ≤ μτWI + μ·Qrows` holds by `fibSum_le_manifest` and
`S ≤ n·I`), `Crz` the razor's error constant, `bGapQ` the `ε_T`-gap coefficient.

Tree hypotheses are exactly the three rows the chapter supplies:

* `hraz` — the razor `RazorNom` (at the box parameters, in the displayed currency);
* `hfib` — the manifest fibre row, **multiplied by `μ`**;
* `hsmall` — the smallness row: the razor's credit and excitation rows and the fibre's `Qrows`
  are absorbed by **half** the gap row (`bGapQ·nq`) and the target's own error slot `C·Mslot·I`,
  with `C ≥ Crz`.

The conclusion is the target's inequality `(¼(τ−μ)² − ½μ²)WI − C·Mslot·I ≤ sbWordCube`. -/
theorem nRowLedger {μ τ W I C Crz bGapQ nq cs P fib Qrows Mslot a : ℝ}
    (hraz : ((1 / 4) * τ ^ 2 + (1 / 2) * τ * μ - (1 / 4) * μ ^ 2) * W * I
        ≤ cs + P + Crz * Mslot * I + Crz * a * (μ + τ) * nq)
    (hfib : μ * fib ≤ μ * (τ * W * I) + μ * Qrows)
    (hsmall : Crz * Mslot * I + Crz * a * (μ + τ) * nq + μ * Qrows
        ≤ bGapQ * nq + C * Mslot * I) :
    ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2) * W * I - C * Mslot * I
      ≤ bGapQ * nq + cs + P - μ * fib := by
  have hid := ledger_identity μ τ W I
  linarith [hid]

/-- **The *pair-alive* ledger — `cs + P` on the hypothesis side** (arm 2's display).

`nRowLedger` consumes the razor as a black box: its hypothesis is
`LHS_razor ≤ cs + P + Crz·Mslot·I + Crz·a(μ+τ)·nq`, so the slack by which the *pairing term alone*
overshoots `LHS_razor` is *thrown away* inside the hypothesis and cannot be spent on the fibre rows.
At the arm-2 extremal states (mass on a sub-box `E ⊆ B`: `pairSum ≍ β(V/|E|)·dem ≫ dem`, while
`|μ·fibQP| ≍ a·μ·√(n₊·S)`) that slack is exactly what must pay the fibre residual, so the ledger
must be stated with the *pairing displayed*:

* `hdec`, `hmain` — the **identity** `μ·fibSum = main + resid` with its main term paid by the flat
  value: `main ≤ μ·(τ·W·I)`.  (`Work.BoseFixB1.fibSumManifestIdentity` +
  `μ·(W/V)·S ≤ μ·τ·W·I` from the count split `S ≤ n·I`; so `main := μ·(W/V)·S` and
  `resid := 2μ·fibQP + μ·fibQ`.)
* `hpair` — **the pairing reaches the razor's demand with an explicit excess `R`**:
  `LHS_razor + R ≤ cs + P`.
* `hrows` — the *residual* fibre row, charged against the gap row **and the excess**:
  `resid ≤ bGapQ·nq + R + C·Mslot·I`.

Then the target's inequality follows.  ⚠ **`R` is not cosmetic.**  The pair-alive branch needs
`resid ≤ bGapQ·nq + slack + C·Mslot·I` where `slack := cs + P − LHS_razor`; the razor's black-box
form only gives `slack ≥ 0`, so `R` is exactly the lower bound on the pairing's slack that the
caller must supply (at the arm-2 extremal states, `R` is the flat/sub-box pairing excess
`≍ (β·V/|E| − λ(τ))·dem`).  Dropping `R` (i.e. taking `R = 0`) recovers the plain pair-alive row
and is *strictly weaker* — it cannot close (☆). -/
theorem nRowLedger_pairAlive {μ τ W I C bGapQ nq cs P fib main resid Mslot R : ℝ}
    (hdec : μ * fib = main + resid)
    (hmain : main ≤ μ * (τ * W * I))
    (hpair : ((1 / 4) * τ ^ 2 + (1 / 2) * τ * μ - (1 / 4) * μ ^ 2) * W * I + R ≤ cs + P)
    (hrows : resid ≤ bGapQ * nq + R + C * Mslot * I) :
    ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2) * W * I - C * Mslot * I
      ≤ bGapQ * nq + cs + P - μ * fib := by
  have hid := ledger_identity μ τ W I
  linarith [hid, hdec, hmain, hpair, hrows]

/-- **The two arms in one statement** — the form the state-level assembly consumes.

Either the pairing pays (`hpair`: arm 2, `nRowLedger_pairAlive`), or the razor pays with its credit
and excitation rows absorbed by the gate and the error slot together with the fibre residual
(arm 1).  Both branches share the identity's decomposition `μ·fib = main + resid` with
`main ≤ μ·(τ·W·I)`, so the two arms differ *only* in which rows must be shown small:

* arm 2 needs `resid ≤ bGapQ·nq + C·Mslot·I` — the fibre residual alone, paid by the gate (`K`
  free in `PerBoxGapAbsorbB1`) and the target's own error slot;
* arm 1 needs `resid + Crz·Mslot·I + Crz·a(μ+τ)·nq ≤ bGapQ·nq + C·Mslot·I` — the same, plus the
  razor's two rows, likewise gate-paid.

This is the "`hraz` display": `cs + P` is on the *hypothesis* side of the first branch, so the
pairing's slack over the razor's demand is not consumed by the razor's black-box form and can be
spent on `resid`. -/
theorem nRowLedger_dichotomy {μ τ W I C Crz bGapQ nq cs P fib Mslot main resid a R : ℝ}
    (hdec : μ * fib = main + resid)
    (hmain : main ≤ μ * (τ * W * I))
    (hcase : (((1 / 4) * τ ^ 2 + (1 / 2) * τ * μ - (1 / 4) * μ ^ 2) * W * I + R ≤ cs + P
          ∧ resid ≤ bGapQ * nq + R + C * Mslot * I)
      ∨ (((1 / 4) * τ ^ 2 + (1 / 2) * τ * μ - (1 / 4) * μ ^ 2) * W * I
            ≤ cs + P + Crz * Mslot * I + Crz * a * (μ + τ) * nq
          ∧ resid + Crz * Mslot * I + Crz * a * (μ + τ) * nq ≤ bGapQ * nq + C * Mslot * I)) :
    ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2) * W * I - C * Mslot * I
      ≤ bGapQ * nq + cs + P - μ * fib := by
  have hid := ledger_identity μ τ W I
  rcases hcase with ⟨hp, hrows⟩ | ⟨hraz, hsmall⟩
  · linarith [hid, hdec, hmain, hp, hrows]
  · -- arm 1: the razor pays, the residual row and the razor's own rows are gate/error-slot paid
    have hfib : μ * fib ≤ μ * (τ * W * I) + resid := by linarith [hdec, hmain]
    have key : ((1 / 4) * τ ^ 2 + (1 / 2) * τ * μ - (1 / 4) * μ ^ 2) * W * I
        - μ * (τ * W * I)
        ≤ bGapQ * nq + cs + P - μ * fib + C * Mslot * I := by
      linarith [hraz, hfib, hsmall]
    linarith [hid, key]

/-! ## 4. The two crux arithmetic rows of the `payPortR3`-route ledger

**Route (session 3 of this node; read `FINDING_nomRowSqWindowRow_session3.md`).**  The target is
consumed through the PROVED state-level rung `Work.BoseB1Cube.sbWordCube_ge_payPortR3`

    payPortR3Lower v h μ n Φ u κ Cr ≤ sbWordCube v h μ u Φ

for `u ∈ goodSet`, `1 ≤ n`, `ContDiff Φ`, `∫Φ² = 1` and the a.e. box support, where (with
`V = PBBV`, `W = PBW`, `χ = chiMass`, `Γ = PBΓ`, `G = g0w0Mass`, `S = boxFlatCount`,
`Pc = boxPairCount`, `Q = boxQCount`, `M₂ = boxM2(wSmallPair (g₂ v h))`, `τ = n/V`)

    payPortR3Lower = a0MainLocBox(V,μ,W,S) + ½((M₂−W)/V²)·Pc
      + bGapCoeff·Q − Cr·a(μ+S/V)Q − Cr·a(μ+n/V)Q
      − ½(1+κΓ)G·((n+1)n/V²)·χ − Cr·a·c³·τ·χ .

The two rows below are the two *quantitative* comparisons that turn this rung into the target:

* `ledger_crux` — the pairing gain `½(M₂−W)Pc/V²` pays the port's price
  `½(1+κΓ)G((n+1)n/V²)χ` **up to a `Q`-row** (gap-paid, the gate `tbGapCoeffGate` is free) and a
  residual `((2+κ)ΓGχn² + 2Gχn + κΓGχn)/V²` which the target's own credit `C(μ²aΓχ + μa)`
  dominates for a **fixed** `C`: the `Γ` cancels between the deficit (`∝ ΓGχτ²`) and the credit
  (`∝ μ²aΓχ`) once `G ≤ 8πa` (`g0w0Mass_le_eight_pi_mul_a`, PROVED) and `τ ≤ Cn·μ`;
* `ledger_branch_small` — in the branch `W ≤ C₀·a/μ` of the PROVED `windowShiftDichotomy` the
  whole demand's positive part is at most `¼(Cn−1)²C₀·μa`, hence paid by the credit's `μa`-term
  alone.

Both are pure real arithmetic; they are the *only* content of the ledger that is not a named,
already-proved corpus datum. -/

/-- **The ledger's crux** (the pairing-gain/port-price comparison).  Under the PROVED box datum
`(1 − 2Γ)Gχ ≤ M₂ − W` (branch 2 of `windowShiftDichotomy` fed into
`boxM2SubBoxM1GeConvChiMass`) and the PROVED Jensen row `S² − S ≤ Pc`, the price of the port,
`(1+κΓ)Gχ·n(n+1)`, is paid by the gain `(M₂−W)Pc` up to the row
`(2+κ)ΓGχn² + 2GχnQ + 2Gχn + κΓGχn`, whose `Q`-part is gate-paid and whose remaining part is a
fixed multiple of `ΓGχn²`.

Equivalently, rearranged: the deficit of the pairing gain against the port's price is at most a
`Q`-row plus `(2+κ)ΓGχn² + 2Gχn + κΓGχn`. -/
theorem ledger_crux {G χ M₂ W S Q Pc n Γ κp : ℝ}
    (hG : 0 ≤ G) (hχ : 0 ≤ χ) (hPc0 : 0 ≤ Pc) (hΓ : 0 ≤ Γ) (hΓ1 : Γ ≤ 1 / 4)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hn : 0 ≤ n) (hSQ : S + Q = n) (hPc : S ^ 2 - S ≤ Pc)
    (hD : (1 - 2 * Γ) * G * χ ≤ M₂ - W) :
    (1 + κp * Γ) * G * χ * (n * (n + 1))
      ≤ (M₂ - W) * Pc
        + ((2 + κp) * Γ * G * χ * n ^ 2 + 2 * G * χ * n * Q
            + 2 * G * χ * n + κp * Γ * G * χ * n) := by
  have hGχ : 0 ≤ G * χ := mul_nonneg hG hχ
  have h1m : 0 ≤ 1 - 2 * Γ := by linarith
  have hcoef : 0 ≤ (1 - 2 * Γ) * G * χ := mul_nonneg (mul_nonneg h1m hG) hχ
  -- the Jensen row multiplied into the box datum
  have hmain : (1 - 2 * Γ) * G * χ * (S ^ 2 - S) ≤ (M₂ - W) * Pc := by
    have h1 : (1 - 2 * Γ) * G * χ * (S ^ 2 - S) ≤ (1 - 2 * Γ) * G * χ * Pc :=
      mul_le_mul_of_nonneg_left hPc hcoef
    have h2 : (1 - 2 * Γ) * G * χ * Pc ≤ (M₂ - W) * Pc :=
      mul_le_mul_of_nonneg_right hD hPc0
    linarith
  -- the pure scalar inequality (the `Γ`-cancellation `4ΓnQ + Q²(1−2Γ) + n(1+2Γ) + Q ≥ 0`)
  have hkey : (1 + κp * Γ) * (n * (n + 1))
      ≤ (1 - 2 * Γ) * (S ^ 2 - S) + (2 + κp) * Γ * n ^ 2 + 2 * n * Q + 2 * n + κp * Γ * n := by
    have hS' : S = n - Q := by linarith
    rw [hS']
    nlinarith [hΓ, hΓ1, hQ, hn, sq_nonneg Q, sq_nonneg n, h1m,
      mul_nonneg hΓ hQ, mul_nonneg hΓ hn, mul_nonneg hn hQ, mul_nonneg hΓ (mul_nonneg hn hQ),
      mul_nonneg h1m (sq_nonneg Q), mul_nonneg hQ h1m]
  have hscale := mul_le_mul_of_nonneg_left hkey hGχ
  nlinarith [hmain, hscale]

/-- **The small-`W` branch of the ledger.**  In branch 1 of the PROVED `windowShiftDichotomy`
(`W ≤ C₀·a/μ`) the demand's positive part is at most `¼(Cn−1)²C₀·μa`, so the credit's `μa`-term
pays it for a fixed `C`. -/
theorem ledger_branch_small {W μ τ a Γ χ C C0 Cn : ℝ} (hμ : 0 < μ) (ha : 0 ≤ a)
    (hCn : 2 ≤ Cn) (hτ : 0 ≤ τ) (hτle : τ ≤ Cn * μ) (hW0 : 0 ≤ W) (hW : W ≤ C0 * a / μ)
    (hΓ : 0 ≤ Γ) (hχ : 0 ≤ χ) (hC0 : 0 ≤ C0) (hC : (1 / 4) * (Cn - 1) ^ 2 * C0 ≤ C) :
    ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2) * W
      ≤ C * (μ ^ 2 * a * Γ * χ + μ * a) := by
  have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hCnn : 0 ≤ C := le_trans (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hC0) hC
  have hbracket : (1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2 ≤ (1 / 4) * (Cn - 1) ^ 2 * μ ^ 2 := by
    have h1 : (τ - μ) ^ 2 ≤ (Cn - 1) ^ 2 * μ ^ 2 := by
      rcases le_or_gt τ μ with h | h
      · have h3 : (1 : ℝ) ≤ (Cn - 1) ^ 2 := by nlinarith
        nlinarith [h, hμ, hτ, h3, sq_nonneg μ, sq_nonneg (τ - μ)]
      · have h2 : τ - μ ≤ (Cn - 1) * μ := by nlinarith
        have h3 : 0 ≤ τ - μ := by linarith
        have h4 : 0 ≤ (Cn - 1) * μ := by nlinarith
        nlinarith [h2, h3, h4, hμ]
    nlinarith [h1, hμ2]
  have hquot : 0 ≤ C0 * a / μ := div_nonneg (mul_nonneg hC0 ha) hμ.le
  have hstep : ((1 / 4) * (τ - μ) ^ 2 - (1 / 2) * μ ^ 2) * W
      ≤ ((1 / 4) * (Cn - 1) ^ 2 * μ ^ 2) * (C0 * a / μ) :=
    mul_le_mul hbracket hW hW0 (by positivity)
  have hsimp : ((1 / 4) * (Cn - 1) ^ 2 * μ ^ 2) * (C0 * a / μ)
      = μ * a * ((1 / 4) * (Cn - 1) ^ 2 * C0) := by
    field_simp
  rw [hsimp] at hstep
  have hcred : μ * a ≤ μ ^ 2 * a * Γ * χ + μ * a := by
    have h0 : 0 ≤ μ ^ 2 * a * Γ * χ := by
      have h2 : (0 : ℝ) ≤ μ ^ 2 * a := mul_nonneg hμ2 ha
      have h3 : (0 : ℝ) ≤ μ ^ 2 * a * Γ := mul_nonneg h2 hΓ
      exact mul_nonneg h3 hχ
    linarith
  have hfin : μ * a * ((1 / 4) * (Cn - 1) ^ 2 * C0) ≤ C * (μ ^ 2 * a * Γ * χ + μ * a) := by
    have h1 : μ * a * ((1 / 4) * (Cn - 1) ^ 2 * C0) ≤ μ * a * C :=
      mul_le_mul_of_nonneg_left hC (mul_nonneg hμ.le ha)
    have h2 : μ * a * C ≤ C * (μ ^ 2 * a * Γ * χ + μ * a) := by
      rw [mul_comm (μ * a) C]
      exact mul_le_mul_of_nonneg_left hcred hCnn
    linarith
  linarith [hstep, hfin]

end Work.BoseB1Cube

/-! ## 5. The assembly of the target from the two window branches

**Route** (see `FINDING_nomRowSqWindowRow_session4.md`).  The target is consumed through the PROVED
state-level rung `sbWordCube_ge_payPortR3`, after the two reductions

* `nomRowI_one` (below) — the target's row at a state of boxed mass `bI = 1`;
* the scaling/normalisation `bI_const_mul` + `sbWordCube_smul`, with the degenerate cases
  `bI = 0` and `n = 0` handled by the PROVED `Work.BoseB1Cube.sbWordCube_eq_zero_of_bI_eq_zero` and
  by `sbWordCube_eq_zero_of_nat_zero`.

At `bI = 1` the two branches of the PROVED `windowShiftDichotomy` (at `C = 1`) are

* **small window** `μ·PBW h μ u ≤ (a v)`: the demand's positive part is `≤ ¼Cn²·(a v)·μ` and the
  crude lower bound `Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin` gives
  `sbWordCube ≥ −K·Cn·(a v)·μ`;
* **large window**: the box datum `(1−2Γ)Gχ ≤ M₂ − W`
  (`Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy`), the PROVED `ledger_crux` and the
  pure-real ledger `Work.BoseB1Cube.nomPortRows`.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open Classical

/-- `bI` is homogeneous of degree two in the state. -/
theorem bI_const_mul {v : E3 → ℝ} {μ : ℝ} {n : ℕ} (Ψ : X n → ℝ) (t : ℝ) :
    Work.BoseFixB1.bI v μ (fun x => t * Ψ x) = t ^ 2 * Work.BoseFixB1.bI v μ Ψ := by
  unfold Work.BoseFixB1.bI
  have h : (fun x : X n => ((fun x => t * Ψ x) x) ^ 2)
      = fun x : X n => t ^ 2 * (Ψ x) ^ 2 := by
    funext x; ring
  rw [h, MeasureTheory.integral_const_mul]

/-- **The count split at the sliding box**: at a state a.e. supported in the box,
`boxFlatCount + boxQCount = n·bI`.  From the PROVED `Work.BoseFixR.SlabCountSplit` (the per-slot
Pythagoras identity) together with the a.e. support, which turns the boxed indicator count
`Σᵢ∫Φ²·1_B(xᵢ)` into `n·∫Φ²`. -/
theorem boxFlatCount_add_boxQCount_eq_of_inBox {v : E3 → ℝ} {μ : ℝ} {n : ℕ} {Ψ : X n → ℝ}
    (hℓ : 0 < Work.BoseFixB1.bSide v μ) (hd : 0 < Work.BoseFixB1.bD v μ) (hΨc : Continuous Ψ)
    (u : E3)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
        Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) :
    Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ
      + Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ
      = (n : ℝ) * Work.BoseFixB1.bI v μ Ψ := by
  have hslab := Work.BoseFixR.SlabCountSplit (ℓ := Work.BoseFixB1.bSide v μ)
    (d := Work.BoseFixB1.bD v μ) hℓ hd u hΨc
  have hflat : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) i Ψ x) ^ 2 := rfl
  have hq : Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ
      = Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) Ψ :=
    rfl
  rw [hflat, hq, ← hslab]
  have hper : ∀ i : Fin n, (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
        (Ψ x) ^ 2 * (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u).indicator (fun _ => (1 : ℝ)) (x i))
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2 := by
    intro i
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    by_cases h0 : Ψ x = 0
    · rw [h0]; simp
    · have hmem : x i ∈ Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u := hx h0 i
      rw [Set.indicator_of_mem hmem]; ring
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]
  rfl

/-- **The word vanishes at `n = 0`**: every slot sum (`n₊`, the spectral form, the potential word)
is empty, and the fibre/pair integrals carry the empty sum as a factor. -/
theorem sbWordCube_eq_zero_of_nat_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (u : E3) (Ψ : X 0 → ℝ) : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 := by
  have hcase : (0 : ℕ) = 0 ∨ (1 ≤ (0 : ℕ) ∧ Work.BoseFixB1.bSide v μ ≤ 0) := Or.inl rfl
  have hcn : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u) Ψ = 0 :=
    Work.BoseFixB1B.cnPlusBoxInd_eq_zero_of_card_zero_or_nonpos hcase _ _ _
  have hcs : Work.BoseFixB1B.cubeSpectral v μ Ψ u = 0 := by
    rw [Work.BoseFixB1B.cubeSpectral, Work.UBBInputs8.tBwordKinInd]
    exact Work.BoseFixB1B.tBdiagFormInd_eq_zero_of_card_zero_or_nonpos hcase _ _ _ _ _
  have hpot : Work.BoseFixB1.sbPot h μ u Ψ = 0 := by
    rw [Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
    exact Work.BoseFixB1B.qLHSword_eq_zero_of_card_zero_or_nonpos hcase μ _ _ Ψ
  rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, hcn, hcs, hpot]
  ring

end Work.BoseB1Cube

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open Classical

/-- **The crux in divided form** (pure real): multiplying the crux
`(1+κΓ)Gχ·n(n+1) ≤ (M₂−W)Pc + A` by `1/(2V²)` produces the three divided rows. -/
theorem cruxDivided {κ Γ G χ n Pc M₂ W A V : ℝ} (hV : 0 < V)
    (h : (1 + κ * Γ) * G * χ * (n * (n + 1)) ≤ (M₂ - W) * Pc + A) :
    (1 / 2) * (1 + κ * Γ) * G * (((n + 1) * n) / V ^ 2) * χ
      ≤ (1 / 2) * ((M₂ - W) / V ^ 2) * Pc + A / (2 * V ^ 2) := by
  have hV2 : (0 : ℝ) < V ^ 2 := pow_pos hV 2
  have hne : V ^ 2 ≠ 0 := ne_of_gt hV2
  have hne2 : (2 * V ^ 2 : ℝ) ≠ 0 := by positivity
  have e1 : V ^ 2 * ((1 / 2) * (1 + κ * Γ) * G * (((n + 1) * n) / V ^ 2) * χ)
      = (1 / 2) * ((1 + κ * Γ) * G * χ * (n * (n + 1))) := by
    calc V ^ 2 * ((1 / 2) * (1 + κ * Γ) * G * (((n + 1) * n) / V ^ 2) * χ)
        = ((1 / 2) * (1 + κ * Γ) * G * χ) * (V ^ 2 * (((n + 1) * n) / V ^ 2)) := by ring
      _ = ((1 / 2) * (1 + κ * Γ) * G * χ) * ((n + 1) * n) := by rw [mul_div_cancel₀ _ hne]
      _ = (1 / 2) * ((1 + κ * Γ) * G * χ * (n * (n + 1))) := by ring
  have e2 : V ^ 2 * ((1 / 2) * ((M₂ - W) / V ^ 2) * Pc) = (1 / 2) * ((M₂ - W) * Pc) := by
    calc V ^ 2 * ((1 / 2) * ((M₂ - W) / V ^ 2) * Pc)
        = ((1 / 2) * Pc) * (V ^ 2 * ((M₂ - W) / V ^ 2)) := by ring
      _ = ((1 / 2) * Pc) * (M₂ - W) := by rw [mul_div_cancel₀ _ hne]
      _ = (1 / 2) * ((M₂ - W) * Pc) := by ring
  have e3 : V ^ 2 * (A / (2 * V ^ 2)) = (1 / 2) * A := by
    calc V ^ 2 * (A / (2 * V ^ 2))
        = (1 / 2) * (A * ((2 * V ^ 2) * (2 * V ^ 2)⁻¹)) := by
          rw [div_eq_mul_inv]; ring
      _ = (1 / 2) * A := by rw [mul_inv_cancel₀ hne2, mul_one]
  have hhalf : (1 / 2) * ((1 + κ * Γ) * G * χ * (n * (n + 1)))
      ≤ (1 / 2) * ((M₂ - W) * Pc) + (1 / 2) * A := by
    have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith only [hh]
  have key : V ^ 2 * ((1 / 2) * (1 + κ * Γ) * G * (((n + 1) * n) / V ^ 2) * χ)
      ≤ V ^ 2 * ((1 / 2) * ((M₂ - W) / V ^ 2) * Pc + A / (2 * V ^ 2)) := by
    have hsplit : V ^ 2 * ((1 / 2) * ((M₂ - W) / V ^ 2) * Pc + A / (2 * V ^ 2))
        = V ^ 2 * ((1 / 2) * ((M₂ - W) / V ^ 2) * Pc) + V ^ 2 * (A / (2 * V ^ 2)) :=
      mul_add (V ^ 2) ((1 / 2) * ((M₂ - W) / V ^ 2) * Pc) (A / (2 * V ^ 2))
    rw [hsplit, e1, e2, e3]
    exact hhalf
  exact le_of_mul_le_mul_left key hV2

/-- **The target's row at a state of boxed mass `bI = 1`.**  The two branches are the small-window
crude route (`Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin`) and the large-window port ledger (the
PROVED rung `sbWordCube_ge_payPortR3`, the PROVED box datum
`Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy`, the PROVED `ledger_crux`, the
pure-real `Work.BoseB1Cube.nomPortRows` and its divided form `cruxDivided`). -/
theorem nomRowI_one {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (Cn : ℝ) (hCn : 3 ≤ Cn) :
    ∃ ε₀ Ct : ℝ, 0 < ε₀ ∧ 0 ≤ Ct ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
          u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          1 ≤ n → ContDiff ℝ (⊤ : ℕ∞) Ψ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
            Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
          (n : ℝ) ≤ Cn * μ * Work.BoseFixB1.bV v μ u →
          Work.BoseFixB1.bI v μ Ψ = 1 →
          ((1 / 4) * (((n : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
              * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
            - nomE v R Ct μ u
              * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
  classical
  -- ## 1. the instruments and their thresholds
  obtain ⟨εsm, K, hεsm, hK0, hcrude⟩ :=
    Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin (v := v) h hv hv1 hvrad hR hv_supp hav Cn
      (by linarith)
  obtain ⟨εrg, κ, Cr, hεrg, hκ0, hCr0, hrung⟩ :=
    Work.BoseB1Cube.sbWordCube_ge_payPortR3 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εbx, hεbx, hbox⟩ :=
    Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy (v := v) h hv hv1 hvrad hR hv_supp
      hav 1 le_rfl
  obtain ⟨εG, hεG, hgg⟩ := Work.BoseB1Cube.boxDataGatesContDiff (v := v) h hv hv1 hvrad hR
    hv_supp hav
  obtain ⟨εrg2, hεrg2, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εgq, hεgq, hΓq⟩ := Work.BoseFixB1.PBGamma_le_of_dilute (v := v) (c := 1 / 4) (by norm_num)
  obtain ⟨εg1, hεg1, hΓ1⟩ := Work.BoseFixB1.PBGamma_le_of_dilute (v := v) (c := 1) (by norm_num)
  obtain ⟨εwm, hεwm, hwle⟩ :=
    Work.BoseB1Cube.w1MassB_le_sharp (v := v) h hv hv1 hvrad hR hv_supp hav (δ := 1) (by norm_num)
  -- the fixed window/box constant `Cs`
  set Cs : ℝ := (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 with hCsdef
  have hCs0 : 0 ≤ Cs := by rw [hCsdef]; positivity
  -- the two free constants
  set Kg : ℝ := 16 * Real.pi * Cn * Cs + 2 * Cr * (1 + Cn) with hKgdef
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; positivity
  obtain ⟨εgt, hεgt, hgate⟩ := Work.BoseB1Cube.bGapCoeff_gate (v := v) hav Kg hKg0
  set Ct : ℝ := max (8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs
      + 8 * Real.pi * Cn * Cs + 4 * Real.pi * κ * Cn * Cs + 4 * Real.pi * (2 + κ) * Cn ^ 2
      + Cr * Cn) ((1 / 4) * Cn ^ 2 + K * Cn) with hCtdef
  have hCt0 : 0 ≤ Ct := by
    rw [hCtdef]
    refine le_trans ?_ (le_max_left _ _)
    have h1 : (0 : ℝ) ≤ 8 * Real.pi * Cs * (2 * Cn + 1) := by positivity
    have h2 : (0 : ℝ) ≤ 4 * Real.pi * Cs := by positivity
    have h3 : (0 : ℝ) ≤ 8 * Real.pi * Cn * Cs := by positivity
    have h4 : (0 : ℝ) ≤ 4 * Real.pi * κ * Cn * Cs := by positivity
    have h5 : (0 : ℝ) ≤ 4 * Real.pi * (2 + κ) * Cn ^ 2 := by positivity
    have h6 : (0 : ℝ) ≤ Cr * Cn := mul_nonneg hCr0 (by linarith)
    linarith only [h1, h2, h3, h4, h5, h6]
  -- the aggregate threshold
  set ε₀ : ℝ := min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)))) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (lt_min hεsm hεrg) (lt_min hεbx (lt_min hεG (lt_min hεrg2
      (lt_min (lt_min (lt_min hεgq hεg1) (lt_min hεgt hεwm)) one_pos))))
  have hle_sm : ε₀ ≤ εsm := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εsm εrg := min_le_left _ _
      _ ≤ εsm := min_le_left _ _
  have hle_rg : ε₀ ≤ εrg := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εsm εrg := min_le_left _ _
      _ ≤ εrg := min_le_right _ _
  have hle_bx : ε₀ ≤ εbx := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ εbx := min_le_left _ _
  have hle_G : ε₀ ≤ εG := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ εG := min_le_left _ _
  have hle_rg2 : ε₀ ≤ εrg2 := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1) := min_le_right _ _
      _ ≤ εrg2 := min_le_left _ _
  have hle_gq : ε₀ ≤ εgq := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1) := min_le_right _ _
      _ ≤ min (min (min εgq εg1) (min εgt εwm)) 1 := min_le_right _ _
      _ ≤ min (min εgq εg1) (min εgt εwm) := min_le_left _ _
      _ ≤ min εgq εg1 := min_le_left _ _
      _ ≤ εgq := min_le_left _ _
  have hle_g1 : ε₀ ≤ εg1 := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1) := min_le_right _ _
      _ ≤ min (min (min εgq εg1) (min εgt εwm)) 1 := min_le_right _ _
      _ ≤ min (min εgq εg1) (min εgt εwm) := min_le_left _ _
      _ ≤ min εgq εg1 := min_le_left _ _
      _ ≤ εg1 := min_le_right _ _
  have hle_gt : ε₀ ≤ εgt := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1) := min_le_right _ _
      _ ≤ min (min (min εgq εg1) (min εgt εwm)) 1 := min_le_right _ _
      _ ≤ min (min εgq εg1) (min εgt εwm) := min_le_left _ _
      _ ≤ min εgt εwm := min_le_right _ _
      _ ≤ εgt := min_le_left _ _
  have hle_wm : ε₀ ≤ εwm := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1) := min_le_right _ _
      _ ≤ min (min (min εgq εg1) (min εgt εwm)) 1 := min_le_right _ _
      _ ≤ min (min εgq εg1) (min εgt εwm) := min_le_left _ _
      _ ≤ min εgt εwm := min_le_right _ _
      _ ≤ εwm := min_le_right _ _
  have hle_one : ε₀ ≤ 1 := by
    rw [hε₀def]
    calc min (min εsm εrg) (min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))))
      _ ≤ min εbx (min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1))) := min_le_right _ _
      _ ≤ min εG (min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1)) := min_le_right _ _
      _ ≤ min εrg2 (min (min (min εgq εg1) (min εgt εwm)) 1) := min_le_right _ _
      _ ≤ min (min (min εgq εg1) (min εgt εwm)) 1 := min_le_right _ _
      _ ≤ 1 := min_le_right _ _
  refine ⟨ε₀, Ct, hε₀pos, hCt0, ?_⟩
  intro μ hAdm n Ψ u hu hn hΨc hsupp hnwin hI
  -- ## 2. the elementary consequences of admissibility
  have hAdm_of : ∀ {e : ℝ}, ε₀ ≤ e → Work.BoseBoxFix.Adm v e μ :=
    fun hle => Work.BoseFixB1.Adm.mono hAdm hle
  have hμ : 0 < μ := hAdm.1
  have hμ0 : (0 : ℝ) ≤ μ := hAdm.1.le
  have ha0 : (0 : ℝ) ≤ _root_.BoseGases.a v := hav.le
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    Work.BoseFixB1.adm_dilute_le_one hAdm hle_one
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16 :=
    (hreg μ hμ (le_trans hAdm.2.1 hle_rg2)).1
  have hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0 :=
    (hreg μ hμ (le_trans hAdm.2.1 hle_rg2)).2
  have hVpos : 0 < Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hμV : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood hav hμ hdil1 hu
  have hIint : (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
      (Ψ x) ^ 2) = 1 := hI
  have hChin : 0 ≤ Work.BoseB1Cube.nomChi v μ u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hΓ0 : 0 ≤ Work.BoseFixB1B.PBΓ v μ := by
    rw [Work.BoseB1Cube.PBΓ_eq_fsXp hav hμ]
    exact (Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := (287 / 2))
      (by positivity)).le
  have hGam0 : 0 ≤ Work.BoseB1Cube.nomGamma v R μ := by
    have h : 0 ≤ (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
        + Work.BoseFixB1B.PBΓ v μ := by
      linarith only [hΓ0, sq_nonneg (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))]
    exact h
  have hslot0 : Ct * (μ * _root_.BoseGases.a v)
      ≤ Ct * (μ ^ 2 * _root_.BoseGases.a v * Work.BoseB1Cube.nomGamma v R μ
          * Work.BoseB1Cube.nomChi v μ u + μ * _root_.BoseGases.a v) := by
    have h1 : 0 ≤ μ ^ 2 * _root_.BoseGases.a v * Work.BoseB1Cube.nomGamma v R μ
        * Work.BoseB1Cube.nomChi v μ u :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha0) hGam0) hChin
    linarith only [mul_nonneg hCt0 h1]
  -- ## 3. the window dichotomy
  by_cases hsmall : Work.BoseFixB1B.PBW h μ u ≤ 1 * _root_.BoseGases.a v / μ
  · -- ## branch 1: small window, the crude route
    have hsw : μ * Work.BoseFixB1B.PBW h μ u ≤ _root_.BoseGases.a v := by
      have h2 := (le_div_iff₀ hμ).mp hsmall
      linarith only [h2]
    have hcr := hcrude μ (hAdm_of hle_sm) u hu hsw n Ψ hΨc hsupp hnwin
    have hcr' : -K * (Cn * _root_.BoseGases.a v * μ)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      simpa only [hIint, mul_one] using hcr
    have hW0 : 0 ≤ Work.BoseFixB1.bW v h μ u :=
      Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
    have hWle : μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v := hsw
    have hτle : (n : ℝ) / Work.BoseFixB1.bV v μ u ≤ Cn * μ := by
      rw [div_le_iff₀ hVpos]; linarith only [hnwin]
    have hτ0 : (0 : ℝ) ≤ (n : ℝ) / Work.BoseFixB1.bV v μ u :=
      div_nonneg (Nat.cast_nonneg _) hVpos.le
    have hsq : (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2 ≤ Cn ^ 2 * μ ^ 2 := by
      have h1 : ((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ ≤ Cn * μ := by
        linarith only [hτle, hμ0]
      have h2 : -(Cn * μ) ≤ ((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ := by
        nlinarith only [hτ0, hCn, hμ]
      have h3 : |((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ| ≤ Cn * μ := abs_le.mpr ⟨h2, h1⟩
      have h4 : |((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ| ≤ |Cn * μ| := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Cn * μ)]
        exact h3
      have h5 := sq_le_sq.mpr h4
      nlinarith only [h5]
    have hA2 : ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseFixB1.bW v h μ u
        ≤ (1 / 4) * Cn ^ 2 * (μ * _root_.BoseGases.a v) := by
      have h9 : (0 : ℝ) ≤ (1 / 4) * Cn ^ 2 := by positivity
      have h8 : μ ^ 2 * Work.BoseFixB1.bW v h μ u ≤ μ * _root_.BoseGases.a v := by
        nlinarith only [hWle, hμ]
      have h4 : (1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2
          ≤ (1 / 4) * Cn ^ 2 * μ ^ 2 := by
        have h5 := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 1 / 4)
        linarith only [h5]
      have h5 : (1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2
            * Work.BoseFixB1.bW v h μ u
          ≤ (1 / 4) * Cn ^ 2 * μ ^ 2 * Work.BoseFixB1.bW v h μ u :=
        mul_le_mul_of_nonneg_right h4 hW0
      have h6 : (1 / 4) * Cn ^ 2 * μ ^ 2 * Work.BoseFixB1.bW v h μ u
          ≤ (1 / 4) * Cn ^ 2 * (μ * _root_.BoseGases.a v) := by
        have h7 := mul_le_mul_of_nonneg_left h8 h9
        linarith only [h7]
      have h7 : 0 ≤ (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u := by positivity
      nlinarith only [h5, h6, h7]
    have hCtbig : (1 / 4) * Cn ^ 2 + K * Cn ≤ Ct := by
      rw [hCtdef]; exact le_max_right _ _
    have hfin : (1 / 4) * Cn ^ 2 * (μ * _root_.BoseGases.a v)
        - Ct * (μ * _root_.BoseGases.a v) ≤ -K * (Cn * _root_.BoseGases.a v * μ) := by
      have h2 : 0 ≤ (Ct - ((1 / 4) * Cn ^ 2 + K * Cn)) * (μ * _root_.BoseGases.a v) :=
        mul_nonneg (sub_nonneg.mpr hCtbig) (mul_nonneg hμ0 ha0)
      linarith only [h2]
    have hconv : ((1 / 4) * (((n : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
          * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
        - nomE v R Ct μ u
          * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
        = ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseFixB1.bW v h μ u - nomE v R Ct μ u := by
      rw [hIint]
      simp only [mul_one]
      rfl
    rw [hconv]
    have hgoalB : ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseFixB1.bW v h μ u
        - nomE v R Ct μ u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      rw [Work.BoseB1Cube.nomE]
      linarith only [hA2, hslot0, hfin, hcr']
    exact hgoalB
  · -- ## branch 2: large window, the port ledger
    have hboxd := hbox μ (hAdm_of hle_bx) u hu hsmall
    have hrung' := hrung μ (hAdm_of hle_rg) n Ψ u hu hn hΨc hI hsupp
    obtain ⟨-, hm1, hm1nn, hm1le2, hPcnn, hjens⟩ := hgg μ (hAdm_of hle_G) n Ψ hΨc u hu hIint
    -- ## the fixed `Cs`, `Kg`, `Ct` facts
    have hM48 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
      rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
    have hχV : Work.BoseB1Cube.nomChi v μ u ≤ Cs * Work.BoseFixB1.bV v μ u := by
      have h1 := Work.BoseFixB1S.chiMass_le_const_mul_boxMass
        (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM48 hℓ hd u
      have h3 : Work.BoseB1Cube.nomChi v μ u
          = Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u := rfl
      have h4 : Cs * Work.BoseFixB1.bV v μ u
          = (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) ^ 2
            * Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := by
        rw [hCsdef]; rfl
      linarith only [h1, h3, h4]
    have hWle2 : Work.BoseFixB1.bW v h μ u
        ≤ 16 * Real.pi * _root_.BoseGases.a v * Work.BoseB1Cube.nomChi v μ u := by
      have h1 : Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          ≤ (1 + 1) * (8 * Real.pi * _root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
        hwle μ (hAdm_of hle_wm) u
      have h2 : Work.BoseFixB1.bW v h μ u
          = Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := rfl
      have h3 : (1 + 1) * (8 * Real.pi * _root_.BoseGases.a v)
          = 16 * Real.pi * _root_.BoseGases.a v := by ring
      have h4 : Work.BoseB1Cube.nomChi v μ u
          = Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := rfl
      rw [h3] at h1
      rw [h2, h4]
      exact h1
    have hGle : Submission.BoseGases.g0w0Mass h ≤ 8 * Real.pi * _root_.BoseGases.a v :=
      Work.BoseB1Cube.g0w0Mass_le_eight_pi_mul_a hR hv hvrad hv_supp h
    have hG0 : 0 ≤ Submission.BoseGases.g0w0Mass h :=
      Work.SmallBoxA0.g0w0Mass_nonneg_general hR hv_supp h
    have hχ0 : 0 ≤ Work.BoseB1Cube.nomChi v μ u := hChin
    have hW0 : 0 ≤ Work.BoseFixB1.bW v h μ u := hm1 ▸ hm1nn
    have hΓ'0 : 0 ≤ Work.BoseB1Cube.nomGamma v R μ := hGam0
    have hΓle : Work.BoseFixB1B.PBΓ v μ ≤ Work.BoseB1Cube.nomGamma v R μ := by
      have h : Work.BoseFixB1B.PBΓ v μ ≤ (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + Work.BoseFixB1B.PBΓ v μ := by
        linarith only [sq_nonneg (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))]
      exact h
    have hΓone : Work.BoseFixB1B.PBΓ v μ ≤ 1 := hΓ1 μ (hAdm_of hle_g1)
    have hΓq : Work.BoseFixB1B.PBΓ v μ ≤ 1 / 4 := hΓq μ (hAdm_of hle_gq)
    have hc0 : 0 ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
      (Work.BoseFixB1S.sbCut_pos hμ hav).le
    have hcube : (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
        ≤ μ * Work.BoseB1Cube.nomGamma v R μ := by
      have h1 := Work.BoseB1Cube.sbCut_cube_le_mu_gamma hav hμ hdil1
      nlinarith only [h1, hΓle, hμ0]
    have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ :=
      Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
    have hQ0 : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ :=
      Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
    have hSQ : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ
        + Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ = (n : ℝ) := by
      rw [boxFlatCount_add_boxQCount_eq_of_inBox hℓ hd hΨc.continuous u hsupp, hI, mul_one]
    have hbg : Kg * (_root_.BoseGases.a v * μ) ≤ Work.BoseFixB1.bGapCoeff v μ := by
      have h := hgate μ (hAdm_of hle_gt)
      have hKg : Kg = 16 * Real.pi * Cn * Cs + 2 * Cr * (1 + Cn) := hKgdef
      rw [hKg] at h
      nlinarith only [h]
    have hbg' : (16 * Real.pi * Cn * Cs + 2 * Cr * (1 + Cn))
        * (_root_.BoseGases.a v * μ) ≤ Work.BoseFixB1.bGapCoeff v μ := by
      have hKg : Kg = 16 * Real.pi * Cn * Cs + 2 * Cr * (1 + Cn) := hKgdef
      rw [← hKg]; exact hbg
    have hCtle : 8 * Real.pi * Cs * (2 * Cn + 1) + 4 * Real.pi * Cs + 8 * Real.pi * Cn * Cs
        + 4 * Real.pi * κ * Cn * Cs + 4 * Real.pi * (2 + κ) * Cn ^ 2 + Cr * Cn ≤ Ct := by
      rw [hCtdef]; exact le_max_left _ _
    -- ## the pure-real ledger
    have hled := Work.BoseB1Cube.nomPortRows (Cn := Cn) (Cs := Cs) (Cr := Cr) (Ct := Ct) (κ := κ)
      (bg := Work.BoseFixB1.bGapCoeff v μ) (V := Work.BoseFixB1.bV v μ u) (μ := μ)
      (a := _root_.BoseGases.a v) (W := Work.BoseFixB1.bW v h μ u)
      (χ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) (G := Submission.BoseGases.g0w0Mass h)
      (Γ := Work.BoseFixB1B.PBΓ v μ) (Γ' := Work.BoseB1Cube.nomGamma v R μ)
      (S := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Q := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (n := (n : ℝ)) (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
      hCn hCs0 hCr0 hκ0 ha0 hVpos hμ (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)) hW0 hχ0 hG0
        hc0 hΓ0 hΓone hΓ'0 hΓle hS0 hQ0 hSQ
      hGle hWle2 hχV hμV hnwin hcube hbg' hCtle
    -- ## the crux
    have hjens' : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ ^ 2
        - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ := by
      simpa only [pow_two] using hjens
    have hm1le2' : Work.BoseFixB1.bW v h μ u
        ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)) := hm1 ▸ hm1le2
    have hcrux := Work.BoseB1Cube.ledger_crux (G := Submission.BoseGases.g0w0Mass h)
      (χ := Work.BoseB1Cube.nomChi v μ u)
      (M₂ := Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)))
      (W := Work.BoseFixB1.bW v h μ u)
      (S := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Q := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (Pc := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (n := (n : ℝ)) (Γ := Work.BoseFixB1B.PBΓ v μ) (κp := κ)
      hG0 hχ0 hPcnn hΓ0 hΓq hQ0 hS0 (Nat.cast_nonneg n) hSQ hjens' hboxd
    -- ## `payPortR3Lower` unfolded, and the crux in divided form
    have hpay : Work.BoseB1Cube.payPortR3Lower v h μ n Ψ u κ Cr
        = ((1 / 4) * ((Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
                (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
              / Work.BoseFixB1.bV v μ u) - μ) ^ 2 * Work.BoseFixB1.bW v h μ u
            - (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
            - (Work.BoseFixB1.bW v h μ u / (2 * Work.BoseFixB1.bV v μ u))
              * (2 * (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
                    (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
                  / Work.BoseFixB1.bV v μ u) + μ)
            - Work.BoseFixB1.bW v h μ u / (4 * (Work.BoseFixB1.bV v μ u) ^ 2))
          + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
              - Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
            * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
          + Work.BoseFixB1.bGapCoeff v μ
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
          - Cr * (_root_.BoseGases.a v)
            * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
                (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
          - Cr * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
          - (1 / 2) * (1 + κ * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
            * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          - Cr * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
            * ((n : ℝ) / Work.BoseFixB1.bV v μ u)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u := by
      rw [Work.BoseB1Cube.payPortR3Lower, Work.BoseFixB1.a0MainLocBox]
    have hcrux2 := cruxDivided (κ := κ) (Γ := Work.BoseFixB1B.PBΓ v μ)
      (G := Submission.BoseGases.g0w0Mass h) (χ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
      (n := (n : ℝ))
      (Pc := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ)
      (M₂ := Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)))
      (W := Work.BoseFixB1.bW v h μ u)
      (A := (2 + κ) * Work.BoseFixB1B.PBΓ v μ * Submission.BoseGases.g0w0Mass h
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u * (n : ℝ) ^ 2
            + 2 * Submission.BoseGases.g0w0Mass h * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u * (n : ℝ)
              * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ
            + 2 * Submission.BoseGases.g0w0Mass h * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u * (n : ℝ)
            + κ * Work.BoseFixB1B.PBΓ v μ * Submission.BoseGases.g0w0Mass h
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u * (n : ℝ))
      (V := Work.BoseFixB1.bV v μ u) hVpos hcrux
    -- ## the final assembly
    have hconv : ((1 / 4) * (((n : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
          * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
        - nomE v R Ct μ u
          * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
        = ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseFixB1.bW v h μ u - nomE v R Ct μ u := by
      rw [hIint]
      simp only [mul_one]
      rfl
    rw [hconv]
    have hgoalB : ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseFixB1.bW v h μ u
        - nomE v R Ct μ u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      rw [Work.BoseB1Cube.nomE]
      have hchi_eq : Work.BoseB1Cube.nomChi v μ u
          = Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := rfl
      rw [hchi_eq]
      linarith only [hled, hcrux2, hrung', hpay]
    exact hgoalB

end Work.BoseB1Cube

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open Classical

theorem nomRowSqWindowRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseB1Cube.NomRowSqWindowRow v h R := by
  intro Cn hCn
  obtain ⟨ε₀, Ct, hε₀, hCt0, hrow⟩ := nomRowI_one h hv hv1 hvrad hR hv_supp hav Cn hCn
  refine ⟨ε₀, Ct, hε₀, hCt0, ?_⟩
  intro μ hAdm n Ψ u hu hΨc hsupp hnwin
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hμpos : 0 < μ := hAdm.1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- ## `n = 0`: the word vanishes and the demand is `≤ 0`
    subst hn0
    have hzero : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 := sbWordCube_eq_zero_of_nat_zero u Ψ
    have hI0 : (0 : ℝ) ≤ ∫ x in Submission.BoseGases.abox 0 (sideAt μ (_root_.BoseGases.a v)),
        (Ψ x) ^ 2 := MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    have hg_all : ((1 / 4) * (((0 : ℕ) : ℝ) / nomV v μ u - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * nomW v h μ u - nomE v R Ct μ u ≤ 0 := by
      have harg : (((0 : ℕ) : ℝ) / nomV v μ u) - μ = -μ := by
        rw [Nat.cast_zero, zero_div, zero_sub]
      rw [harg]
      have hμ2 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
      have hW0 : 0 ≤ nomW v h μ u := by
        rw [Work.BoseB1Cube.nomW]
        exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
      have hE0 : 0 ≤ nomE v R Ct μ u := by
        rw [Work.BoseB1Cube.nomE]
        have hχ : 0 ≤ Work.BoseB1Cube.nomChi v μ u :=
          Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
        have hb : (0 : ℝ) ≤ Work.BoseFixB1B.PBΓ v μ := by
          rw [Work.BoseB1Cube.PBΓ_eq_fsXp hav hAdm.1]
          exact (Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := (287 / 2))
            (mul_pos hμpos (pow_pos hav 3))).le
        have hΓg : 0 ≤ Work.BoseB1Cube.nomGamma v R μ := by
          have h : 0 ≤ (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + Work.BoseFixB1B.PBΓ v μ := by
            linarith only [hb, sq_nonneg (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))]
          exact h
        have h1 : 0 ≤ μ ^ 2 * _root_.BoseGases.a v * Work.BoseB1Cube.nomGamma v R μ
            * Work.BoseB1Cube.nomChi v μ u :=
          mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) hΓg) hχ
        have h2 : 0 ≤ μ * _root_.BoseGases.a v := mul_nonneg hAdm.1.le hav.le
        nlinarith only [h1, h2, hCt0]
      nlinarith only [hμ2, hW0, hE0]
    calc ((1 / 4) * (((0 : ℕ) : ℝ) / nomV v μ u - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
          * (∫ x in Submission.BoseGases.abox 0 (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
        - nomE v R Ct μ u
          * (∫ x in Submission.BoseGases.abox 0 (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
        = (((1 / 4) * (((0 : ℕ) : ℝ) / nomV v μ u - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
            - nomE v R Ct μ u)
          * (∫ x in Submission.BoseGases.abox 0 (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2) := by
          ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hg_all hI0
      _ = Work.BoseFixB1B.sbWordCube v h μ u Ψ := hzero.symm
  · -- ## `n ≥ 1`: split off the degenerate boxed mass
    by_cases hIz : Work.BoseFixB1.bI v μ Ψ = 0
    · have hzero : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 :=
        Work.BoseB1Cube.sbWordCube_eq_zero_of_bI_eq_zero (v := v) (h := h) (μ := μ) hΨc hIz u
      have hIz' : (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
          (Ψ x) ^ 2) = 0 := hIz
      rw [hzero, hIz']
      simp only [mul_zero, sub_zero]
      exact le_refl 0
    · -- normalise the state to boxed mass `1`
      have hIpos : 0 < Work.BoseFixB1.bI v μ Ψ :=
        lt_of_le_of_ne (MeasureTheory.integral_nonneg (fun x => sq_nonneg _)) (Ne.symm hIz)
      set t : ℝ := (Real.sqrt (Work.BoseFixB1.bI v μ Ψ))⁻¹ with htdef
      have hsqrpos : 0 < Real.sqrt (Work.BoseFixB1.bI v μ Ψ) := Real.sqrt_pos.mpr hIpos
      have ht0 : 0 < t := by rw [htdef]; positivity
      have ht2 : t ^ 2 * Work.BoseFixB1.bI v μ Ψ = 1 := by
        rw [htdef, inv_pow, Real.sq_sqrt hIpos.le]
        field_simp
      have ht2pos : 0 < t ^ 2 := pow_pos ht0 2
      have hI1 : Work.BoseFixB1.bI v μ (fun x => t * Ψ x) = 1 := by
        rw [bI_const_mul, ht2]
      have hc' : ContDiff ℝ (⊤ : ℕ∞) (fun x => t * Ψ x) := hΨc.const_smul t
      have hsupp' : ∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          (fun x => t * Ψ x) x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u := by
        filter_upwards [hsupp] with x hx hne
        exact hx (fun h0 => hne (by rw [h0, mul_zero]))
      have hrow' := hrow μ hAdm n (fun x => t * Ψ x) u hu hnpos hc' hsupp' hnwin hI1
      have hIt : (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
            ((fun x => t * Ψ x) x) ^ 2)
          = t ^ 2 * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) := by
        have hb := bI_const_mul (v := v) (μ := μ) Ψ t
        rw [Work.BoseFixB1.bI] at hb
        exact hb
      have hsm : Work.BoseFixB1B.sbWordCube v h μ u (fun x => t * Ψ x)
          = t ^ 2 * Work.BoseFixB1B.sbWordCube v h μ u Ψ :=
        Work.BoseFixB1S.sbWordCube_smul h u Ψ t
      rw [hIt, hsm] at hrow'
      have hfac : ((1 / 4) * (((n : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
            * (t ^ 2 * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2))
          - nomE v R Ct μ u
            * (t ^ 2 * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2))
          = t ^ 2 * (((1 / 4) * (((n : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
              * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2)
            - nomE v R Ct μ u
              * (∫ x in Submission.BoseGases.abox n (sideAt μ (_root_.BoseGases.a v)),
                  (Ψ x) ^ 2)) := by ring
      rw [hfac] at hrow'
      exact le_of_mul_le_mul_left hrow' ht2pos

end Work.BoseB1Cube
