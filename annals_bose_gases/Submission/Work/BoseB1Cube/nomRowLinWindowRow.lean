import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.Free.HoleNodeF
import Submission.Work.BoseB1Cube.Free.LargeArmF
import Submission.Work.BoseB1Cube.Free.RazorSharp
import Submission.Work.BoseB1Cube.Free.SmallWinRoute
import Submission.Work.BoseB1Cube.newtonSelfEnergy
import Submission.Work.BoseB1Cube.nomAssemble
import Submission.Work.BoseB1Cube.nomRowPieces
import Submission.Work.BoseB1Cube.poorRowLedgerArith
import Submission.Work.BoseB1Cube.slidingBogPortCubeContDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomRowLinWindowRow` — FS's linear group row of `thm:smallbox`
# at the sliding box and the single cube cutoff

Holder: this module.  Target (statement byte-identical, body still `sorry`):
`Work.BoseB1Cube.nomRowLinWindowRow v h R`.

## What this module adds (`sorry`-free, axiom-clean)

* `Work.BoseB1Cube.SharpRow v h R` — the **sharp-row residual** (a `Prop`): the demand
  `(1/18)μ(n/V)W` bounded by the *sharp rung's left-hand side*
  `a0MainLocBox + bA2 + bSpectralCube + ½((M₂−M₁)/V²)Pc` (the pair square is kept);
* `Work.BoseB1Cube.SharpRow2 v h R` — **the residual that actually matters**: as `SharpRow`, plus an
  *arbitrary fixed* multiple `C·(a v)·μ·n₊` of the excited count.  ⚠ `SharpRow` is (almost
  certainly) **FALSE**: at the "product of mean-zero" states `Ψ = ∏ψ(xᵢ)` (`∫_Aψ = 0`, `∫_Aψ² = 1`,
  `supp ψ ⊆ A`) one has `S = Pc = bA2 = 0`, `bSpectralCube` small, `a0MainLocBox ≈ −μ²M₁/4` while
  the demand is `≈ (2/9)μ²M₁`.  The node nevertheless holds there — *because the gap slack is a free
  constant*: `bGapCoeff ≥ K(a v)μ` for every fixed `K` (PROVED `PerBoxGapAbsorbB1`) while the
  payment rung's credit is at most `C_p(a v)(1+2Cₙ)μ·n₊` on the count window, so
  `sbWordCube ≥ [rung LHS] + (K − C_p(1+2Cₙ))·(a v)·μ·n₊` with `K` free.  `SharpRow2` records
  exactly that slack; see `FINDING_nomRowLinWindowRow_session2.md` §10;
* `Work.BoseB1Cube.NormNode v h R` — the node restricted to normalised states;
* **`Work.BoseB1Cube.normNode_of_sharpRow2`** and `normNode_of_sharpRow` — **`SharpRow2 ⟹
  NormNode`** (resp. **`SharpRow ⟹ NormNode`**), the assembly of the
  PROVED payment rung (`paySurplusSlotFreeContDiff`), telescope
  (`sbWordSlotTelescopeContDiff`), slot identity (`sbWordCube_eq_add` + `sbPot_split`), gates
  (`boxDataGatesContDiff`) and the PROVED gap gate (`PerBoxGapAbsorbB1`);
* **`Work.BoseB1Cube.nomRowLinWindowRow_of_normNode`** — **`NormNode ⟹ the node`** (homogeneity
  `sbWordCube_smul` + the a.e.-null case `sbWordCube_eq_zero_of_ae_eq_zero`);
* **`Work.BoseB1Cube.nomRowLinWindowRow_of_sharpRow2`** — the two composed:
  **`SharpRow2 ⟹ the node`** (the recommended residual).

`#print axioms` is `[propext, Classical.choice, Quot.sound]` for both theorems.  The node itself
still carries its `sorry` — it is **not** proved here.

## §2bis — SESSION 3: the **excited-rich half is PROVED**, and the node reduces to the flat branch

The node is now reduced to a **strictly weaker** residual than `SharpRow2`, and one of the two
halves of that residual is discharged:

| declaration | content |
|---|---|
| `Work.BoseB1Cube.RichRow` | the `SharpRow2`-inequality on the excited-rich half `n/2 ≤ n₊` — **PROVED** (`richRow_holds`) |
| `Work.BoseB1Cube.PoorRow` | the same on the nearly-flat half `n₊ < n/2` — **the residual** |
| `Work.BoseB1Cube.richArith` | the abstraction-free ledger: on `Q ≥ τV/2` the row follows from `A₀ ≥ −(2Cn+5/4)μ²W`, the port row, the crude constants and the *free* constant `C` |
| `Work.BoseB1Cube.a0MainLocBox_lower` | `a0MainLocBox V μ W S ≥ −(2Cn+5/4)μ²W` on the two-sided count window with `1 ≤ μV` |
| `Work.BoseB1Cube.sharpRow2_of_rich_poor` | `RichRow → PoorRow → SharpRow2` (dichotomy `n₊ ⋛ n/2`) |
| `Work.BoseB1Cube.nomRowLinWindowRow_of_poorRow` | **`PoorRow ⟹ the node`** |

Why the rich half is *free*: on `n₊ ≥ n/2` every row that is proportional to `μ·n₊` — the port's
`Cq·a·(μ+τ)·n₊`, its constant row `Cq·a·μ`, and the whole demand `(1/18)μτW ≤ (Cn·CM/9)aμ²V` — is
paid by the *free* constant `C·(a v)·μ·n₊` of `SharpRow2` (with `n₊ ≥ n/2 ≥ CnμV/2`), while the rows
proportional to `avμ²V` are paid by the `A₀`-row and the port's mass row with the crude proved
constants (`M₁ ≤ CM·(a v)·V`, `g0w0Mass ≤ 8π(a v)`, `chiMass ≤ (chiSupAbs·chiSmallDecay M)²·V`).
No new analytic input is needed.

**Cone (session 3, late):** this module imports
`Submission.Work.BoseB1Cube.ConeC.BoseB1Cube_sharpInc` (the `ConeC` transplant of `sharpInc`:
three new copies + a copy of `sharpInc`, recipe in `FINDING_nomRowLinWindowRow_session3.md` §6), so
**`Work.BoseFixB1S.boxQSum_ge_sharpInc` is available to everything importing this module** — the
sharpest existed `boxQSum` lower bound,

    a0MainLocBox + bA2 + ½(M₂/V²)Pc − ¼(M₁/V²)(Pc + S²−S) − C·a·(μ+S/V)·n₊ + Inc ≤ boxQSum
      for any `Inc ≤ boxSqPart`  (`Inc := boxSqPart` is the strongest form),

which dominates `paySurplusSlotFreeContDiff`'s row by `¼(M₁/V²)·Var + Inc ≥ 0`
(`Var = Pc − S² + S ≥ 0`).  At flat states `Var = 0` and `boxSqPart = ½((M_v − M₂)/V²)·Pc` is the
*`ω²`-row*, so the transplant sharpens the ledger but does **not** by itself close `PoorRow`.

Why the *nearly-flat* half is the honest frontier (details and the quantitative obstruction in
`FINDING_nomRowLinWindowRow_session3.md`): there `S = n − n₊ ≥ n/2`, so the row must be paid by
`a0MainLocBox + ½((M₂−M₁)/V²)·Pc` (or by a smaller `θ·n` in the same free-constant way).  The
corpus's port `paySurplusSlotFreeContDiff` displays the pair square with `M₂ − M₁` where the truth
carries the `v`-numerator mass `M_v ≥ M₂` (FS's `lm:w2>w1`), and the port's mass row carries the
factor `(1+η)` with `η = 8K_s + 1 ≥ 9` (FS use `(1+ε)`, `ε = 1/20`), so on the flat states the
crude route is short by a *fixed* factor (order 2–10).  ⚠ **The CS step itself is NOT the gap**: FS's
`eq:Q3+Q4CS` is PROVED in the corpus (`Work.BoseB1Cube.boxQ3Q4PayCredit`, which imports cleanly
here; `Work.BoseFixR.rungQ3Q4_cancel`; `Work.BoseB1Cube.boxQ3Q4CSLocal`) — see the FINDING's §5.3
before filing anything about it.  The two honest repairs are: a *matched*-constant port
(`(1+ε)` in place of `(1+η)`), or the *manifest* pair-energy row (keeping `½·Σig` with `M_v`, e.g.
through the PROVED identity `boxQSum_sub_boxQ0_eq_manifestRow`).

## Why the node is *not* reached through `CrossRow` (the structural finding of this session)

The node's supply is (PROVED telescopes)

    sbWordCube = bGapCoeff·n₊ + bSpectralCube + boxQSum ,      bSpectralCube ≥ 0 (PROVED),

whereas `CrossRow` (`= Work.BoseB1Cube.boxQSum_ge_boxQ0_windowCount`, the chapter's standing
frontier) has **no `bSpectralCube` slot**: `sbWordCube_ge_nomLinRowWindow_of_pieces` reaches the
node through `nomLinRowArith`, whose conclusion is the *weaker* `(1/18)μτW ≤ gap·Q + boxQSum`.
Hence `CrossRow ⟹ node`, but the node does **not** need `CrossRow`.  See
`FINDING_nomRowLinWindowRow_session2.md` §6 for the family of in-box `ContDiff` states
(Jastrow-hole states with `η ≡ 1` on `ball(r₀)`, `r₀ ≥ supp w = R`, so that the manifest pair
energy vanishes *exactly*) on which the crux's manifest form
`2μP̃ + μQ̂ + (3/8)(M₂/V²)Pc ≤ ½Σig + Caρn₊` fails for small `n₊`, while the *node* survives through
`bSpectralCube` (the kinetic energy of the hole's boundary layer).

**Recommendation:** attack the node at the `bSpectralCube`-carrying rung — i.e. attack `SharpRow`
below — rather than at `CrossRow`.

## §3ter — SESSION 9: the ledger's **(CORE)** row is now PROVED on the big box

`Submission/Work/BoseB1Cube/holeCoreBigBox.lean` (**PROVED**, axiom-clean) contains
`Work.BoseB1Cube.holeCoreBigBox`: the (CORE) inequality of
`demand_le_sbWordCube_of_ledgerRows` — *verbatim* its `hcore` hypothesis — under `32 ≤ μV` plus the
state-independent rows (the mass row `(1−2Γ)Gχm ≤ M₂−W`, the ratio `Gχm ≤ W`, the crude row
`W ≤ cW·aV`, the gate `K a μ ≤ gap` with `1 ≤ K bQ`, and the fixed bookkeeping `C ≤ 1/4`,
`8C(1+2Cn) ≤ K`, `6 Cn cW ≤ K`).  Its scalar heart is `coreScalarBigBox2` (margin `> 0.69` at the
worst admissible point).  So the ledger's *only* arithmetic row is discharged for `32 ≤ μV` and
`bQ ≥ 1/K`; the residual is `bQ < 1/K` (the hole row) plus the corner `μV < 32`, whose statement
must carry `1 ≤ μV` (supplied by `one_le_mu_boxMassGood`) and the small window.
See `FINDING_nomRowLinWindowRow_session9.md`.

## §4 — SESSION 10: **the node is assembled**, modulo ONE holder-free leaf

Read `FINDING_nomRowLinWindowRow_session10.md` first.  The node's `sorry` used to be
`NomRowLinWindowRow` itself, and the fleet's whole `SmallWinProp`-side chain was
holder-**down**stream (through the gratuitous `import …smallWinDefs` of a definitions-only module),
so no future proof of the hole row could ever be imported here.  That is now fixed: the `Free`
cone (`Submission/Work/BoseB1Cube/Free/{Props,GapArmF,FlatArmF,LargeArmF,HoleNodeF}.lean`) contains
verbatim, holder-free re-issues of the two case-`Prop`s, the window dichotomy, the three arms and
the merged hole row; and this file ends with

    holeLeaf  : … → SmallWinHolePDF v h            -- the file's ONLY `sorry`
    largeWinPropF_holds,  normNodeF_holds,  normNode_of_normNodeF        -- PROVED
    nomRowLinWindowRow = nomRowLinWindowRow_of_normNode ∘ normNode_of_normNodeF ∘ normNodeF_holds

`SmallWinHolePDF`'s body is the verbatim body of the fleet's `SmallWinHolePD`, so the leaf is *the
fleet's node*, not a strengthening; the complementary cases are exactly the PROVED arms.  Once the
hole row lands (its cone is holder-downstream only through `smallWinDefs`), the copies of §0 of the
FINDING close this file mechanically.

⚠ The session also settled *why* a free-constant instrument cannot close this node: the razor's
and the port's state-independent row `C·(a v)·μ` must be paid by `≈ 1.53·μ²·bW` of the flat
surplus, which forces the instrument's constant to be a *fixed* `O(1)` (`C ≲ 3`, FS's sharp
`lm:appabogolubov`), while the corpus's ports have `C ≳ 10^{58}`.  Proving `RazorNom`/`HoleRow` with
any *existentially chosen* `C` is therefore not a step towards this node.  See §4 of the FINDING.
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
set_option maxHeartbeats 1600000

/-- **The sharp-row residual.**  Under FS's parameters, on `goodSet`, for an in-box normalised
`ContDiff` state in the count window, the **sharp rung's left-hand side** — the `A₀`-main term, the
pairing word `boxA2` *and* the spectral slot `bSpectralCube` — dominates the node's linear demand.

This is *strictly weaker* than `CrossRow`: it displays `bSpectralCube` (the slot FS use to pay the
boundary layers) and drops the pair square `½((M₂−M₁)/V²)·Pc` and the credit rows.  It is exactly
what is left over after the PROVED payment + telescope + gate assembly. -/
def SharpRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
            * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
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

/-- **The sharp-row residual with the gap slack.**  Same as `SharpRow`, but the right-hand side
also carries an arbitrary **fixed** multiple `C·(a v)·μ·n₊` of the excited count.  This is the
*weakest* statement the PROVED rung can supply: the gate `PerBoxGapAbsorbB1` gives
`bGapCoeff ≥ K·(a v)·μ` for **every** fixed `K`, and the credit consumed by the payment rung is at
most `C_p·(a v)·(1+2Cₙ)·μ·n₊` on the count window, so the rung's supply exceeds
`[a0Main + bA2 + bSpectralCube + ½((M₂−M₁)/V²)Pc]` by `(K − C_p(1+2Cₙ))·(a v)·μ·n₊` — and `K` is
free.  (This is the difference that makes the node reachable at the "product of mean-zero" states
`Ψ = ∏ψ(xᵢ)`, `∫_Aψ = 0`, where `S = Pc = bA2 = 0` and `bSpectralCube` is small: there `SharpRow`
alone fails, while the node survives on the gap slack.) -/
def SharpRow2 (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
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

/-- The node restricted to **normalised** states (the shape in which every rung is stated). -/
def NormNode (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **`SharpRow ⟹ NormNode`** — the assembly of the PROVED payment rung, telescope, gates and gap
gate (see the module docstring). -/
theorem normNode_of_sharpRow {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hSR : SharpRow v h R) :
    NormNode v h R := by
  intro Cn hCn
  -- ## the thresholds, all produced *before* `ε₀` is chosen
  obtain ⟨εp, Cp, hεp, hCp, hpay⟩ :=
    paySurplusSlotFreeContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εt, hεt, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εd, hεd, hgates⟩ := boxDataGatesContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εg, hεg, hgate⟩ :=
    Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav ((Cp + 1) * (1 + 2 * Cn)) (by positivity)
  obtain ⟨εs, hεs, hSR'⟩ := hSR Cn hCn
  set E0 : ℝ := min εp (min εt (min εd (min εg (min 1 εs)))) with hE0
  have hb1 : E0 ≤ εp := by rw [hE0]; exact min_le_left _ _
  have hb2 : E0 ≤ εt := by
    rw [hE0]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hb3 : E0 ≤ εd := by
    rw [hE0]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb4 : E0 ≤ εg := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hb5 : E0 ≤ 1 := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hb6 : E0 ≤ εs := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _))))
  refine ⟨E0, lt_min hεp (lt_min hεt (lt_min hεd (lt_min hεg (lt_min one_pos hεs)))), ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hnorm hn1 hn2
  -- ## threshold extraction
  have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm hb1
  have hAdmt : Work.BoseBoxFix.Adm v εt μ := Work.BoseFixB1.Adm.mono hAdm hb2
  have hAdmd : Work.BoseBoxFix.Adm v εd μ := Work.BoseFixB1.Adm.mono hAdm hb3
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm hb4
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm hb5
  have hAdms : Work.BoseBoxFix.Adm v εs μ := Work.BoseFixB1.Adm.mono hAdm hb6
  have hμ : 0 < μ := hAdm.1
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hRd, hRχ⟩ := hreg μ hμ hAdmt.2.1
  -- ## the gates and the geometry
  obtain ⟨hvol, hW, hM1nn, hM2, hPcnn, hcS2⟩ := hgates μ hAdmd n Ψ hΨ u hu hnorm
  have hμV : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := _root_.BoseGases.a v) (μ := μ) hav
      hAdm.1 hAdm1.2.1 hu
  -- ## the payment rung at the slot `μp = μ`
  have hpay' := hpay μ hAdmp μ (le_refl μ) n Ψ hΨ u hu hvol hμV hsupp hnorm hW hM1nn hM2 hPcnn hcS2
  -- ## the telescope (same file's PROVED `sbWordSlotTelescopeContDiff`)
  have htel := sbWordSlotTelescopeContDiff (v := v) h hv_supp hR hv hvrad hv1
    (μp := μ) (μ := μ) hℓ hd hRd hRχ u hvol Ψ hΨ
  -- ## `sbWordCube = sbWordSlot v h μ μ u Ψ`
  have hcube : Work.BoseFixB1B.sbWordCube v h μ u Ψ = sbWordSlot v h μ μ u Ψ := by
    rw [Work.BoseFixB1C.sbWordCube_eq_add u Ψ,
      sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdmp
        (ContDiff.continuous hΨ) u hRd hRχ]
    unfold Work.BoseB1Cube.sbWordSlot
    ring
  -- ## the gate
  have hgate' : ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)) ≤
      Work.BoseFixB1.bGapCoeff v μ := by
    have h := hgate μ hAdmg
    have hgc : Work.BoseFixB1.bGapCoeff v μ
        = Work.SmallBoxTBWord.tbGapCoeff
            ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
      rw [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
    rw [hgc]
    linarith [h]
  -- ## the count split and the window
  have hcount : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ ≤ (n : ℝ) := by
    have h := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := n)
      (ℓ := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
      (Ac := Work.BoseFixB1.bA v μ u) hℓ hvol
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _)
      (by rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def])
      (ContDiff.continuous hΨ)
    rw [hnorm, mul_one] at h
    exact h
  -- ## the arithmetic
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ := Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hSV : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hvol]
    nlinarith [hcount, hn2, hμ, hCn, hvol]
  have hcredit : Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
      ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ := by
    have h1 : Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        ≤ Cp * (_root_.BoseGases.a v) * ((1 + 2 * Cn) * μ) := by
      have h0 : 0 ≤ Cp * (_root_.BoseGases.a v) := mul_nonneg hCp ha
      have h2 : μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u
          ≤ (1 + 2 * Cn) * μ := by linarith
      exact mul_le_mul_of_nonneg_left h2 h0
    have h3 : Cp * (_root_.BoseGases.a v) * ((1 + 2 * Cn) * μ)
        ≤ ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)) := by
      nlinarith [ha, hμ, hCn, hCp]
    have h4 : ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v))
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
        ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ := by
      have h5 : ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v))
          = ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)) := rfl
      calc ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
          = (((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)))
              * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ := rfl
        _ ≤ Work.BoseFixB1.bGapCoeff v μ
              * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ :=
            mul_le_mul_of_nonneg_right hgate' hQnn
    have h3' : Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        ≤ ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)) := le_trans h1 h3
    have h6 : Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
        ≤ ((Cp + 1) * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_le_mul_of_nonneg_right h3' hQnn
    linarith [h6, h4]
  have hpc : 0 ≤ (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
      * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ := by
    have h1 : 0 ≤ (Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u) := by rw [← hW]; linarith [hM2]
    have h2 : 0 ≤ (1 / 2 : ℝ) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2) := by positivity
    exact mul_nonneg h2 hPcnn
  -- ## the assembly
  have hmain : Work.BoseFixB1S.bSpectralCube v μ Ψ u
      + Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
          (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ)
      + Work.BoseFixB1.bA2 v h μ Ψ u
      + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
            - Work.BoseFixB1.bW v h μ u)
          / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    rw [hcube, htel]
    linarith [hpay', hcredit]
  have hSR'' := hSR' μ hAdms n Ψ u hu hΨ hsupp hnorm hn1 hn2
  have hfin : (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
      * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    linarith [hSR'', hmain]
  rw [hnorm, mul_one] at hfin
  simpa only [nomV, nomW, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM,
    Work.BoseFixB1.bV, Work.BoseFixB1.bW, Work.BoseFixB1.bA] using hfin

/-- **`NormNode ⟹ the node`** — homogeneity of `sbWordCube` (`Work.BoseFixB1S.sbWordCube_smul`)
plus the a.e.-null case (`Work.BoseB1Cube.sbWordCube_eq_zero_of_ae_eq_zero`). -/
theorem nomRowLinWindowRow_of_normNode {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hN : NormNode v h R) :
    NomRowLinWindowRow v h R := by
  intro Cn hCn
  obtain ⟨ε, hε, hrow⟩ := hN Cn hCn
  refine ⟨ε, hε, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hn1 hn2
  simp only [nomV, nomW, Work.BoseFixB1.bV, Work.BoseFixB1.bW, Work.BoseFixB1.bSide,
    Work.BoseFixB1.bD, Work.BoseFixB1.bM, Work.BoseFixB1.bA] at hu hn1 hn2 ⊢
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  set I : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Ψ x) ^ 2 with hIdef
  have hInn : 0 ≤ I := by
    rw [hIdef]; exact integral_nonneg (fun x => sq_nonneg _)
  rcases eq_or_lt_of_le hInn with hI0 | hIpos
  · -- the a.e.-null case
    have hnn : 0 ≤ᵐ[(volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))]
        (fun x : X n => (Ψ x) ^ 2) := Filter.Eventually.of_forall (fun x => sq_nonneg _)
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      (f := Ψ) (ContDiff.continuous hΨ).continuousOn
    have hint : Integrable (fun x : X n => (Ψ x) ^ 2)
        ((volume : Measure (X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
      Work.BoseFixB1S.integrableOn_sq_of_bound (N := n) hℓ (ContDiff.continuous hΨ).measurable
        (fun x hx => by simpa [Real.norm_eq_abs] using hC x hx)
    have hzero : (fun x : X n => (Ψ x) ^ 2) =ᵐ[(volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp (by rw [hIdef] at hI0; exact hI0.symm)
    have hΨ0 : Ψ =ᵐ[(volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] 0 :=
      hzero.mono (fun x hx => by
        have hx' : (Ψ x) ^ 2 = 0 := hx
        exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hx')
    have hnpos : 0 < n := by
      by_contra hcon
      have : n = 0 := Nat.eq_zero_of_not_pos hcon
      subst this
      have hV' : 0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
        Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
      have hprod : 0 < Cn * μ * Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
        mul_pos (mul_pos (by linarith) hμ) hV'
      have hn1' : Cn * μ * Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u ≤ ((0 : ℕ) : ℝ) := hn1
      push_cast at hn1'
      linarith [hprod, hn1']
    have hsw : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 :=
      sbWordCube_eq_zero_of_ae_eq_zero (v := v) (h := h) (μ := μ) (u := u) (N := n)
        (by simpa only [Work.BoseFixB1.bSide] using hℓ)
        (by simpa only [Work.BoseFixB1.bD] using hd) hnpos (ContDiff.continuous hΨ).measurable hΨ0
    have hIz : (1 / 18) * μ * ((n : ℝ) /
          Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u * I = 0 := by
      rw [← hI0, mul_zero]
    rw [hIz, hsw]
  · -- the homogeneous case
    set c : ℝ := (Real.sqrt I)⁻¹ with hcdef
    have hc2 : c ^ 2 = I⁻¹ := by
      rw [hcdef, inv_pow, Real.sq_sqrt hIpos.le]
    have hΦint : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (c * Ψ x) ^ 2) = 1 := by
      have h1 : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (c * Ψ x) ^ 2)
          = c ^ 2 * ∫ x in Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2 := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      rw [h1, ← hIdef, hc2, inv_mul_cancel₀ (ne_of_gt hIpos)]
    have hΦsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        (c * Ψ x) ≠ 0 → ∀ i : Fin n,
          x i ∈ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
      filter_upwards [hsupp] with x hx hne i
      exact hx (fun h0 => hne (by rw [h0, mul_zero])) i
    have hrow' := hrow μ hAdm n (fun x => c * Ψ x) u hu
      (by simpa only [smul_eq_mul, mul_comm] using hΨ.smul_const c) hΦsupp hΦint hn1 hn2
    simp only [Work.BoseFixB1.bV, Work.BoseFixB1.bW] at hrow'
    rw [Work.BoseFixB1S.sbWordCube_smul (v := v) h (μ := μ) u Ψ c] at hrow'
    have h2 : (c ^ 2 * Work.BoseFixB1B.sbWordCube v h μ u Ψ) * I
        = Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      rw [hc2]
      field_simp
    calc (1 / 18) * μ * ((n : ℝ) /
          Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u * I
        = ((1 / 18) * μ * ((n : ℝ) /
            Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) * I := rfl
      _ ≤ (c ^ 2 * Work.BoseFixB1B.sbWordCube v h μ u Ψ) * I :=
          mul_le_mul_of_nonneg_right hrow' hIpos.le
      _ = Work.BoseFixB1B.sbWordCube v h μ u Ψ := h2

/-- **`SharpRow2 ⟹ NormNode`** — the assembly of the PROVED payment rung, telescope, gates and gap
gate (see the module docstring). -/
theorem normNode_of_sharpRow2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hSR : SharpRow2 v h R) :
    NormNode v h R := by
  intro Cn hCn
  -- ## the thresholds, all produced *before* `ε₀` is chosen
  obtain ⟨εp, Cp, hεp, hCp, hpay⟩ :=
    paySurplusSlotFreeContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εt, hεt, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εd, hεd, hgates⟩ := boxDataGatesContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εs, Cs, hεs, hCs, hSR'⟩ := hSR Cn hCn
  obtain ⟨εg, hεg, hgate⟩ :=
    Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav ((Cp + 1) * (1 + 2 * Cn) + Cs) (by positivity)
  set E0 : ℝ := min εp (min εt (min εd (min εg (min 1 εs)))) with hE0
  have hb1 : E0 ≤ εp := by rw [hE0]; exact min_le_left _ _
  have hb2 : E0 ≤ εt := by
    rw [hE0]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hb3 : E0 ≤ εd := by
    rw [hE0]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb4 : E0 ≤ εg := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hb5 : E0 ≤ 1 := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hb6 : E0 ≤ εs := by
    rw [hE0]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _))))
  refine ⟨E0, lt_min hεp (lt_min hεt (lt_min hεd (lt_min hεg (lt_min one_pos hεs)))), ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hnorm hn1 hn2
  -- ## threshold extraction
  have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm hb1
  have hAdmt : Work.BoseBoxFix.Adm v εt μ := Work.BoseFixB1.Adm.mono hAdm hb2
  have hAdmd : Work.BoseBoxFix.Adm v εd μ := Work.BoseFixB1.Adm.mono hAdm hb3
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm hb4
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm hb5
  have hAdms : Work.BoseBoxFix.Adm v εs μ := Work.BoseFixB1.Adm.mono hAdm hb6
  have hμ : 0 < μ := hAdm.1
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hRd, hRχ⟩ := hreg μ hμ hAdmt.2.1
  -- ## the gates and the geometry
  obtain ⟨hvol, hW, hM1nn, hM2, hPcnn, hcS2⟩ := hgates μ hAdmd n Ψ hΨ u hu hnorm
  have hμV : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := _root_.BoseGases.a v) (μ := μ) hav
      hAdm.1 hAdm1.2.1 hu
  -- ## the payment rung at the slot `μp = μ`
  have hpay' := hpay μ hAdmp μ (le_refl μ) n Ψ hΨ u hu hvol hμV hsupp hnorm hW hM1nn hM2 hPcnn hcS2
  -- ## the telescope (same file's PROVED `sbWordSlotTelescopeContDiff`)
  have htel := sbWordSlotTelescopeContDiff (v := v) h hv_supp hR hv hvrad hv1
    (μp := μ) (μ := μ) hℓ hd hRd hRχ u hvol Ψ hΨ
  -- ## `sbWordCube = sbWordSlot v h μ μ u Ψ`
  have hcube : Work.BoseFixB1B.sbWordCube v h μ u Ψ = sbWordSlot v h μ μ u Ψ := by
    rw [Work.BoseFixB1C.sbWordCube_eq_add u Ψ,
      sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdmp
        (ContDiff.continuous hΨ) u hRd hRχ]
    unfold Work.BoseB1Cube.sbWordSlot
    ring
  -- ## the gate
  have hgate' : ((Cp + 1) * (1 + 2 * Cn) + Cs) * (μ * (_root_.BoseGases.a v)) ≤
      Work.BoseFixB1.bGapCoeff v μ := by
    have h := hgate μ hAdmg
    have hgc : Work.BoseFixB1.bGapCoeff v μ
        = Work.SmallBoxTBWord.tbGapCoeff
            ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
      rw [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
    rw [hgc]
    linarith [h]
  -- ## the count split and the window
  have hcount : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ ≤ (n : ℝ) := by
    have h := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := n)
      (ℓ := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
      (Ac := Work.BoseFixB1.bA v μ u) hℓ hvol
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _)
      (by rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def])
      (ContDiff.continuous hΨ)
    rw [hnorm, mul_one] at h
    exact h
  -- ## the arithmetic
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ := Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hSV : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hvol]
    nlinarith [hcount, hn2, hμ, hCn, hvol]
  have hslack : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount
        (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
      - Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ
      ≥ Cs * (_root_.BoseGases.a v) * μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ := by
    -- `bGapCoeff ≥ K(μa)` with `K = (Cp+1)(1+2Cn) + Cs`
    have hgb : ((Cp + 1) * (1 + 2 * Cn) + Cs) * (μ * (_root_.BoseGases.a v))
        ≤ Work.BoseFixB1.bGapCoeff v μ := by
      have h := hgate μ hAdmg
      have hgc : Work.BoseFixB1.bGapCoeff v μ
          = Work.SmallBoxTBWord.tbGapCoeff
              ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
        rw [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
      rw [hgc]
      linarith [h]
    -- the credit is a fixed multiple of `(μa)·n₊`
    have hcred' : Cp * (_root_.BoseGases.a v)
        * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
        ≤ (Cp * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)) := by
      have h0 : 0 ≤ Cp * (_root_.BoseGases.a v) := mul_nonneg hCp ha
      have h2 : μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u
          ≤ (1 + 2 * Cn) * μ := by linarith
      have := mul_le_mul_of_nonneg_left h2 h0
      linarith [this]
    have h1 : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount
          (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
        ≥ (((Cp + 1) * (1 + 2 * Cn) + Cs) * (μ * (_root_.BoseGases.a v)))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_le_mul_of_nonneg_right hgb hQnn
    have h2 : Cp * (_root_.BoseGases.a v)
          * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        ≤ ((Cp * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v)))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_le_mul_of_nonneg_right hcred' hQnn
    have hkey : ((Cp + 1) * (1 + 2 * Cn) + Cs) * (μ * (_root_.BoseGases.a v))
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        - (Cp * (1 + 2 * Cn)) * (μ * (_root_.BoseGases.a v))
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ
        = Cs * (_root_.BoseGases.a v) * μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
          + (1 + 2 * Cn) * (μ * (_root_.BoseGases.a v))
            * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ := by ring
    have hnn2 : 0 ≤ (1 + 2 * Cn) * (μ * (_root_.BoseGases.a v))
        * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ :=
      mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hμ.le ha)) hQnn
    linarith [h1, h2, hkey, hnn2]
  have hpc : 0 ≤ (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
      * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ := by
    have h1 : 0 ≤ (Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u) := by rw [← hW]; linarith [hM2]
    have h2 : 0 ≤ (1 / 2 : ℝ) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2) := by positivity
    exact mul_nonneg h2 hPcnn
  -- ## the assembly
  have hmain : Work.BoseFixB1S.bSpectralCube v μ Ψ u
      + Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
          (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ)
      + Work.BoseFixB1.bA2 v h μ Ψ u
      + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
            - Work.BoseFixB1.bW v h μ u)
          / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
      + Cs * (_root_.BoseGases.a v) * μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    rw [hcube, htel]
    linarith [hpay', hslack]
  have hSR'' := hSR' μ hAdms n Ψ u hu hΨ hsupp hnorm hn1 hn2
  have hfin : (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
      * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    rw [hnorm, mul_one]
    linarith [hSR'', hmain]
  rw [hnorm, mul_one] at hfin
  simpa only [nomV, nomW, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM,
    Work.BoseFixB1.bV, Work.BoseFixB1.bW, Work.BoseFixB1.bA] using hfin

/-- **`SharpRow2 ⟹ the node`** (homogeneity). -/
theorem nomRowLinWindowRow_of_sharpRow2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hSR : SharpRow2 v h R) :
    NomRowLinWindowRow v h R :=
  nomRowLinWindowRow_of_normNode h hv hv1 hvrad hR hv_supp hav
    (normNode_of_sharpRow2 h hv hv1 hvrad hR hv_supp hav hSR)

end Work.BoseB1Cube

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **THE single remaining leaf of the node** (session 11: re-pointed to the fleet's *live* node).

The leaf is `Work.BoseB1Cube.SmallWinHolePDF v h` (`Free/HoleNodeF.lean`) — the verbatim body of the
fleet's **single remaining Bose node** `Work.BoseB1Cube.SmallWinHolePD`
(`Submission/Work/BoseB1Cube/smallWinHolePD.lean`), which is itself the only open leaf of
`Work.BoseB1Cube.SmallWinNode`.  All three of `SmallWinNode`, `SmallWinHolePD` and this leaf are
therefore *one and the same obligation*, and whoever closes it closes the node by the PROVED
reduction `Work.BoseB1Cube.smallWinPropF_of_holePDF` (gap arm `smallWinGapArmGenF` at
`c = min c₀ 10⁻⁶`, flat arm `flatArm37RowNodeF`, pair arm `sbWordCube_ge_demand_of_pairSum`) and
then the PROVED window dichotomy `Work.BoseB1Cube.normNodeF_of_winF`.

**Why this spelling of the leaf.**  `SmallWinHolePD` is *strictly weaker* than `SmallWinProp`: it
carries the three state hypotheses `bQ < c₀` (with `c₀` chosen *per* window constant `Cn`), `¬
FlatArm37`, and *pair-deadness* `pairSum − μ·fibSum < D`; each of the three complementary cases is a
PROVED arm.  It is also strictly weaker than the older spelling `SmallWinHoleRowF`
(`Free/SmallWinRoute.lean`, the fleet's filed `smallWinHoleRow`): that one asked for a *uniform*
threshold `∃ c₀ ∀ Cn` and dropped pair-deadness, both gratuitous strengthenings.

**Closure recipes** (either closes this file; both leaves are holder-free `Prop`s, so the copy is a
rename):
* copy the proof of `Work.BoseB1Cube.SmallWinHolePD` (`smallWinHolePD.lean`, or of `SmallWinNode`)
  into the `Free` cone as `SmallWinHolePDF`, i.e. with the renamings
  `SmallWinHolePD ↦ SmallWinHolePDF, SmallWinProp ↦ SmallWinPropF,
  smallWinGapArmGen ↦ smallWinGapArmGenF, flatArm37RowNode ↦ flatArm37RowNodeF,
  smallWinProp_of_holePD ↦ smallWinPropF_of_holePDF, sbWordCube_ge_demand_of_pairSum`
  (unchanged), and set the body of this theorem to the copy — *keep the proof cone free of
  `Submission.Work.BoseB1Cube.{nomRowLinWindowRow, smallWinDefs, SmallWinNode, smallWinHoleRow}`*;
* or copy the proof of `Work.BoseB1Cube.smallWinHoleRow` the same way and use the *alternative*
  route `normNodeF_holds_of_rowF` (below), which is `sorry`-free and takes `SmallWinHoleRowF` as a
  hypothesis. -/
theorem holeLeaf {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.SmallWinHolePDF v h := by
  sorry

/-- **The large-window arm**, holder-free (`Free/LargeArmF.lean`): `LargeWinNodeF`. -/
theorem largeWinPropF_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.LargeWinPropF v h R :=
  Work.BoseB1Cube.LargeWinNodeF (v := v) (R := R) h hv hv1 hvrad hR hv_supp hav

/-- **The normalised node, holder-free** (`Free/Props.lean`'s window dichotomy + the two arms),
through the fleet's **live** hole node `SmallWinHolePDF` (= `Work.BoseB1Cube.SmallWinHolePD`). -/
theorem normNodeF_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.NormNodeF v h R :=
  Work.BoseB1Cube.normNodeF_of_winF (v := v) (R := R) h
    (Work.BoseB1Cube.smallWinPropF_of_holePDF (v := v) (R := R) h hv hv1 hvrad hR hv_supp
      hav (holeLeaf h hv hv1 hvrad hR hv_supp hav))
    (largeWinPropF_holds h hv hv1 hvrad hR hv_supp hav)

/-- **The alternative route**, through the *older* spelling of the fleet's hole row
`SmallWinHoleRowF` (`Free/SmallWinRoute.lean`, the filed `Work.BoseB1Cube.smallWinHoleRow`):
`sorry`-free, the row enters as a hypothesis.  Kept so that *either* of the fleet's two spellings
closes this file — `SmallWinHolePD` through `normNodeF_holds` above, `smallWinHoleRow` through
this one. -/
theorem normNodeF_holds_of_rowF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hrow : Work.BoseB1Cube.SmallWinHoleRowF v h R) : Work.BoseB1Cube.NormNodeF v h R :=
  Work.BoseB1Cube.normNodeF_of_winF (v := v) (R := R) h
    (Work.BoseB1Cube.smallWinPropF_of_smallWinHoleRowF (v := v) (R := R) h hv hv1 hvrad hR hv_supp
      hav hrow)
    (largeWinPropF_holds h hv hv1 hvrad hR hv_supp hav)

/-- **The same, through `SmallWinHolePDF` as a hypothesis** (the leaf of `normNodeF_holds`), kept as
the documented interface for whoever closes the leaf elsewhere. -/
theorem normNodeF_holds_of_holePDF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hPD : Work.BoseB1Cube.SmallWinHolePDF v h) : Work.BoseB1Cube.NormNodeF v h R :=
  Work.BoseB1Cube.normNodeF_of_winF (v := v) (R := R) h
    (Work.BoseB1Cube.smallWinPropF_of_holePDF (v := v) (R := R) h hv hv1 hvrad hR hv_supp hav hPD)
    (largeWinPropF_holds h hv hv1 hvrad hR hv_supp hav)

/-- `NormNodeF` and `NormNode` are the same clause (their `def`-bodies are character-for-character
identical); this is the one-line conversion used below. -/
theorem normNode_of_normNodeF {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hN : Work.BoseB1Cube.NormNodeF v h R) : Work.BoseB1Cube.NormNode v h R := hN

/-- **The razor route** (`Free/RazorSharp.lean`, PROVED reduction): the *sharp* razor
`Work.BoseB1Cube.RazorSharpF v h R` (FS `lm:appinteractionestimate`, with **no** state-independent
credit row — unlike `RazorNom`/`HoleRow`, whose existential credit forces `C ≤ 1.53` and is
unpayable inside an error-free row) closes the small-window arm `SmallWinPropF`, hence
`NormNodeF`.  `sorry`-free: the razor enters as a hypothesis, so this is the documented *second*
route to the node next to `holeLeaf : SmallWinHolePDF`. -/
theorem normNodeF_holds_of_razorF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hRz : Work.BoseB1Cube.RazorSharpF v h R) : Work.BoseB1Cube.NormNodeF v h R :=
  Work.BoseB1Cube.normNodeF_of_winF (v := v) (R := R) h
    (Work.BoseB1Cube.razorSharpF_imp_smallWinPropF (v := v) (R := R) h hv hv1 hvrad hR hv_supp hav
      hRz)
    (largeWinPropF_holds h hv hv1 hvrad hR hv_supp hav)

/-- **The *minimal* razor route** (`Free/RazorSharp.lean`, PROVED reduction): the demand-plus-fibre
row `Work.BoseB1Cube.RazorDemandF v h R` — the node's own inequality with the gap column deleted and
a *payable* row `C₀·(a v)·(μ+τ)·n₊` added, i.e.

    (1/18)·μ·τ·W + μ·fibSum  ≤  cubeSpectral + pairSum + C₀·(a v)·(μ+τ)·n₊ ,

closes the small-window arm `SmallWinPropF` (and hence `NormNodeF`) through the *free* gate column
`bGapCoeff·n₊ ≥ Kg·(a v)·μ·n₊` alone — no manifest fibre bound, no Young/AM-GM step, no razor
surplus.  Its hard case needs the sharp capacity supply to beat `(19/(9λ))·½τ²W` (i.e. a **47 %**
loss budget at `λ = 4`), against the **28 %** of `RazorSharpF`/`RazorHole`; it is *not* implied by
`RazorSharpF` by any recorded route (the manifest's `√`-row would need the gate, which (DEMAND)'s
right-hand side does not carry), so it is a genuinely different, and genuinely easier, instrument.
`sorry`-free here: the row enters as a hypothesis, so this is the *third* route to the node. -/
theorem normNodeF_holds_of_razorDemandF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hRd : Work.BoseB1Cube.RazorDemandF v h R) : Work.BoseB1Cube.NormNodeF v h R :=
  Work.BoseB1Cube.normNodeF_of_winF (v := v) (R := R) h
    (Work.BoseB1Cube.razorDemandF_imp_smallWinPropF (v := v) (R := R) h hv hv1 hvrad hR hv_supp hav
      hRd)
    (largeWinPropF_holds h hv hv1 hvrad hR hv_supp hav)

/-- **The end-to-end conditional statements**: *either* sharp razor gives the **target itself**.
So the moment `Work.BoseB1Cube.Free.RazorSharF`/`RazorDemandF` (or `Work.BoseB1Cube.SmallWinHolePD`)
is proved, `holeLeaf` can be replaced by it and the target follows by one of these two lines. -/
theorem nomRowLinWindowRow_of_razorF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hRz : Work.BoseB1Cube.RazorSharpF v h R) :
    Work.BoseB1Cube.NomRowLinWindowRow v h R :=
  nomRowLinWindowRow_of_normNode h hv hv1 hvrad hR hv_supp hav
    (normNode_of_normNodeF (normNodeF_holds_of_razorF h hv hv1 hvrad hR hv_supp hav hRz))

/-- The same through the *minimal* row `RazorDemandF`. -/
theorem nomRowLinWindowRow_of_razorDemandF {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hRd : Work.BoseB1Cube.RazorDemandF v h R) :
    Work.BoseB1Cube.NomRowLinWindowRow v h R :=
  nomRowLinWindowRow_of_normNode h hv hv1 hvrad hR hv_supp hav
    (normNode_of_normNodeF (normNodeF_holds_of_razorDemandF h hv hv1 hvrad hR hv_supp hav hRd))

theorem nomRowLinWindowRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseB1Cube.NomRowLinWindowRow v h R :=
  nomRowLinWindowRow_of_normNode h hv hv1 hvrad hR hv_supp hav
    (normNode_of_normNodeF
      (normNodeF_holds h hv hv1 hvrad hR hv_supp hav))

end Work.BoseB1Cube

/-!
# §2 — the excited-rich half of the row (PROVED) and the nearly-flat residual

`SharpRow2` (the recommended residual of the module docstring) is split by the dichotomy
`n/2 ≤ n₊` versus `n₊ < n/2` into

* `Work.BoseB1Cube.RichRow` — the **excited-rich** half, `n/2 ≤ n₊`.  **PROVED** below
  (`richRow_holds`): on that half the row follows from the PROVED ports
  (`paySurplusSlotFreeContDiff` for the assembly, `slidingBogPortCubeContDiff` for the
  `A₂ + spectral` slot), the PROVED gates (`boxDataGatesContDiff`,
  `boxFlatCount_le_NB1`), the crude constants (`boxM1_le_aV`, `g0w0Mass_le_eight_pi_mul_a`,
  `chiMass_le_const_mul_boxMass`) and the free constant `C` of `SharpRow2` — no new mathematics;
* `Work.BoseB1Cube.PoorRow` — the **nearly-flat** half `n₊ < n/2`, the residual.

`sharpRow2_of_rich_poor` assembles them (with `C := max`), and
`nomRowLinWindowRow_of_poorRow` is the consumer-facing form: **the node follows from
`PoorRow` alone**.  On the nearly-flat half the pair-condensate count `S` is `≥ n/2`, so the
row must be paid by `a0MainLocBox + ½((M₂−M₁)/V²)·Pc` — i.e. by the *flat-branch* rows
(`lm:w2>w1` and the manifest pair energy), which is exactly the well-documented frontier of the
per-box chapter; the crude route through `paySurplusSlotFreeContDiff` is *lossy* there by the
factor `M_v/(M₂ − M₁)` (the corpus's port displays `½(M₂−M₁)/V²` where the truth carries the
`v`-numerator mass `M_v`), which is precisely why the split is drawn at `n/2`.
-/

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The excited-rich half of `SharpRow2`**: the `SharpRow2`-inequality for states with
`n/2 ≤ n₊ = boxQCount`. -/
def RichRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 2) * (n : ℝ) ≤ Work.BoseFixB1.bQ v μ Ψ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
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
            + C * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u

/-- **The nearly-flat half of `SharpRow2`**: the same inequality for states with
`n₊ = boxQCount < n/2`.  This is the residual. -/
def PoorRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        Work.BoseFixB1.bQ v μ Ψ u < (1 / 2) * (n : ℝ) →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
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
            + C * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u

/-- **The `A₀` lower bound on the two-sided count window.**  For `1 ≤ μV`, `S ≤ n` and
`n ≤ 2·Cn·μV`, the corpus's box-`A₀` satisfies `a0MainLocBox V μ W S ≥ −(2Cn + 5/4)·μ²·W`.

(The `1/V`-defects of `Q₀`'s exact value cost `(W/(2V))(2S/V + μ) + W/(4V²)`, bounded by
`Wμ²(2Cn + 1/2)` resp. `Wμ²/4` using `1/V ≤ μ`, which is `1 ≤ μV`.) -/
theorem a0MainLocBox_lower {Cn μ V W S n : ℝ} (hCn : 0 ≤ Cn) (hV : 0 < V) (hμ : 0 < μ)
    (hW : 0 ≤ W) (hμV : 1 ≤ μ * V) (hS : S ≤ n) (hn : n ≤ 2 * Cn * μ * V) :
    -(2 * Cn + 5 / 4) * μ ^ 2 * W ≤ Work.BoseFixB1.a0MainLocBox V μ W S := by
  have h1V : 1 / V ≤ μ := by
    rw [div_le_iff₀ hV]
    linarith [hμV]
  have h1V2 : 1 / V ^ 2 ≤ μ ^ 2 := by
    have h : (1 / V) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (by positivity) h1V 2
    rwa [div_pow, one_pow] at h
  have hSV : S / V ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hV]
    linarith [hS, hn]
  have h2S : 2 * (S / V) + μ ≤ (4 * Cn + 1) * μ := by linarith [hSV]
  have h4 : W / (2 * V) ≤ W * μ / 2 := by
    have h := mul_le_mul_of_nonneg_left h1V (by positivity : (0 : ℝ) ≤ W / 2)
    calc W / (2 * V) = (W / 2) * (1 / V) := by ring
      _ ≤ (W / 2) * μ := h
      _ = W * μ / 2 := by ring
  have h3 : (W / (2 * V)) * (2 * (S / V) + μ) ≤ W * μ ^ 2 * (2 * Cn + 1 / 2) := by
    have h5 : (W / (2 * V)) * (2 * (S / V) + μ) ≤ (W / (2 * V)) * ((4 * Cn + 1) * μ) :=
      mul_le_mul_of_nonneg_left h2S (by positivity)
    have h6 : (W / (2 * V)) * ((4 * Cn + 1) * μ) ≤ (W * μ / 2) * ((4 * Cn + 1) * μ) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    have h7 : (W * μ / 2) * ((4 * Cn + 1) * μ) = W * μ ^ 2 * (2 * Cn + 1 / 2) := by ring
    linarith [h5, h6, h7]
  have h8 : W / (4 * V ^ 2) ≤ W * μ ^ 2 / 4 := by
    calc W / (4 * V ^ 2) = (W / 4) * (1 / V ^ 2) := by ring
      _ ≤ (W / 4) * μ ^ 2 := mul_le_mul_of_nonneg_left h1V2 (by positivity)
      _ = W * μ ^ 2 / 4 := by ring
  have h9 : 0 ≤ (1 / 4) * (S / V - μ) ^ 2 * W := by positivity
  rw [Work.BoseFixB1.a0MainLocBox]
  linarith [h3, h8, h9]

/-- The credit constant of the port at the gate `Kq`. -/
noncomputable def richKq (Cn Cq : ℝ) : ℝ := Cq * (1 + 2 * Cn)

/-- The total amount the rich-case ledger has to find. -/
noncomputable def richCgoal (Cn CM Cq D2 : ℝ) : ℝ :=
  Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq + (2 * Cn + 5 / 4) * CM

/-- The free constant of `SharpRow2` that the rich case needs. -/
noncomputable def richC (Cn CM Cq D2 : ℝ) : ℝ :=
  richKq Cn Cq + 2 * richCgoal Cn CM Cq D2 / Cn + 1

/-- **The rich-case arithmetic**, in the abstraction-free form: on `n/2 ≤ Q` the row's right-hand
side dominates the demand, with the free constant `richC` paying the `μ·Q`-proportional rows.
`A0`, `a2`, `spec` are the `a0MainLocBox`, `bA2` and `bSpectralCube` slots; `A0` only enters
through its lower bound `hA0`, and `a2 + spec` through the port row `ha2`. -/
theorem richArith {Cn μ V W S Pc M2 Q G χm τ n av CM Cq D2 A0 a2 spec : ℝ}
    (hCn : 4 ≤ Cn) (hμ : 0 < μ) (hav : 0 ≤ av) (hV : 0 < V)
    (hWnn : 0 ≤ W) (hμV : 1 ≤ μ * V) (hQnn : 0 ≤ Q) (hPcnn : 0 ≤ Pc)
    (hD2nn : 0 ≤ D2) (hCMnn : 0 ≤ CM) (hCqnn : 0 ≤ Cq)
    (hGnn : 0 ≤ G) (hGle : G ≤ 8 * Real.pi * av)
    (hχmnn : 0 ≤ χm) (hχmle : χm ≤ D2 * V)
    (hSle : S ≤ n) (hn1 : Cn * μ * V ≤ n) (hn2 : n ≤ 2 * Cn * μ * V)
    (hτV : τ * V = n) (hτle : τ ≤ 2 * Cn * μ) (hQrich : (1 / 2) * (τ * V) ≤ Q)
    (hWb : W ≤ CM * av * V) (hWle : W ≤ M2)
    (hA0 : -(2 * Cn + 5 / 4) * μ ^ 2 * W ≤ A0)
    (ha2 : -(G * ((n + 1) * n / V ^ 2) * χm + Cq * av * (μ + τ) * Q + Cq * av * μ)
      ≤ a2 + spec) :
    (1 / 18) * μ * τ * W
      ≤ A0 + a2 + spec + (1 / 2) * ((M2 - W) / V ^ 2) * Pc
        + richC Cn CM Cq D2 * av * μ * Q := by
  have hCn4 : (0 : ℝ) < Cn := lt_of_lt_of_le (by norm_num) hCn
  have hCnne : Cn ≠ 0 := ne_of_gt hCn4
  have hVne : V ≠ 0 := ne_of_gt hV
  have hτ0 : 0 ≤ τ := by
    have h0 : 0 ≤ Cn * μ * V := by positivity
    have h1 : 0 ≤ τ * V := by rw [hτV]; linarith [hn1, h0]
    exact (mul_nonneg_iff_of_pos_right hV).mp h1
  -- ## the `n₊`-row: `Q` is large on the rich half
  have hQlow : (Cn / 2) * (μ ^ 2 * V) ≤ μ * Q := by
    have h2 : (1 / 2) * (Cn * (μ * V)) ≤ (1 / 2) * (τ * V) := by nlinarith [hn1, hτV]
    have h3 : (1 / 2) * (Cn * (μ * V)) ≤ Q := le_trans h2 hQrich
    have h4 : μ * ((1 / 2) * (Cn * (μ * V))) ≤ μ * Q := mul_le_mul_of_nonneg_left h3 hμ.le
    linarith [h4]
  -- ## the demand row
  have hDm : (1 / 18) * μ * τ * W ≤ (Cn * CM / 9) * av * μ ^ 2 * V := by
    have h1 : μ * τ * W ≤ μ * (2 * Cn * μ) * (CM * av * V) := by
      have h2 : μ * τ ≤ μ * (2 * Cn * μ) := mul_le_mul_of_nonneg_left hτle hμ.le
      have h3 : 0 ≤ μ * (2 * Cn * μ) := by positivity
      have h4 : μ * τ * W ≤ μ * (2 * Cn * μ) * W := by nlinarith [h2, hWnn]
      have h5 : μ * (2 * Cn * μ) * W ≤ μ * (2 * Cn * μ) * (CM * av * V) :=
        mul_le_mul_of_nonneg_left hWb h3
      linarith [h4, h5]
    have h6 : (1 / 18) * (μ * (2 * Cn * μ) * (CM * av * V))
        = (Cn * CM / 9) * av * μ ^ 2 * V := by ring
    linarith [h1, h6]
  -- ## the mass row
  have hmass : G * ((n + 1) * n / V ^ 2) * χm ≤ 64 * Real.pi * D2 * Cn ^ 2 * av * μ ^ 2 * V := by
    have hn1pos : (1 : ℝ) ≤ n := by nlinarith [hn1, hμV, hCn]
    have hnsq : (n + 1) * n ≤ 2 * n ^ 2 := by nlinarith [hn1pos]
    have hnum : (n + 1) * n / V ^ 2 ≤ 2 * τ ^ 2 := by
      have h1 : (n + 1) * n / V ^ 2 ≤ 2 * n ^ 2 / V ^ 2 :=
        div_le_div_of_nonneg_right hnsq (by positivity)
      have h2 : 2 * n ^ 2 / V ^ 2 = 2 * τ ^ 2 := by
        rw [div_eq_iff (by positivity : V ^ 2 ≠ 0)]
        rw [← hτV]
        ring
      linarith [h1, h2]
    have hτsq : τ ^ 2 ≤ 4 * Cn ^ 2 * μ ^ 2 := by
      have h1 : τ ^ 2 ≤ (2 * Cn * μ) ^ 2 := pow_le_pow_left₀ hτ0 hτle 2
      nlinarith [h1]
    have hstep1 : G * ((n + 1) * n / V ^ 2) * χm ≤ G * (2 * τ ^ 2) * (D2 * V) := by
      have h0 : 0 ≤ G * ((n + 1) * n / V ^ 2) := by positivity
      have h1 : G * ((n + 1) * n / V ^ 2) * χm ≤ G * ((n + 1) * n / V ^ 2) * (D2 * V) :=
        mul_le_mul_of_nonneg_left hχmle h0
      have h3 : 0 ≤ D2 * V := by positivity
      have h4 : G * ((n + 1) * n / V ^ 2) ≤ G * (2 * τ ^ 2) :=
        mul_le_mul_of_nonneg_left hnum hGnn
      have h5 : G * ((n + 1) * n / V ^ 2) * (D2 * V) ≤ G * (2 * τ ^ 2) * (D2 * V) :=
        mul_le_mul_of_nonneg_right h4 h3
      linarith [h1, h5]
    have hstep2 : G * (2 * τ ^ 2) * (D2 * V) ≤ (8 * Real.pi * av) * (8 * Cn ^ 2 * μ ^ 2) * (D2 * V) := by
      have h1 : G * (2 * τ ^ 2) ≤ (8 * Real.pi * av) * (2 * τ ^ 2) :=
        mul_le_mul_of_nonneg_right hGle (by positivity)
      have h2 : (8 * Real.pi * av) * (2 * τ ^ 2) ≤ (8 * Real.pi * av) * (8 * Cn ^ 2 * μ ^ 2) := by
        have h3 : 2 * τ ^ 2 ≤ 8 * Cn ^ 2 * μ ^ 2 := by linarith [hτsq]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have h4 : 0 ≤ D2 * V := by positivity
      have h5 : G * (2 * τ ^ 2) * (D2 * V) ≤ (8 * Real.pi * av) * (2 * τ ^ 2) * (D2 * V) :=
        mul_le_mul_of_nonneg_right h1 h4
      have h6 : (8 * Real.pi * av) * (2 * τ ^ 2) * (D2 * V)
          ≤ (8 * Real.pi * av) * (8 * Cn ^ 2 * μ ^ 2) * (D2 * V) :=
        mul_le_mul_of_nonneg_right h2 h4
      linarith [h5, h6]
    calc G * ((n + 1) * n / V ^ 2) * χm ≤ G * (2 * τ ^ 2) * (D2 * V) := hstep1
      _ ≤ (8 * Real.pi * av) * (8 * Cn ^ 2 * μ ^ 2) * (D2 * V) := hstep2
      _ = 64 * Real.pi * D2 * Cn ^ 2 * av * μ ^ 2 * V := by ring
  -- ## the `A₀`-row
  have hA0b : (2 * Cn + 5 / 4) * μ ^ 2 * W ≤ (2 * Cn + 5 / 4) * CM * av * μ ^ 2 * V := by
    have h1 : (2 * Cn + 5 / 4) * μ ^ 2 * W ≤ (2 * Cn + 5 / 4) * μ ^ 2 * (CM * av * V) :=
      mul_le_mul_of_nonneg_left hWb (by positivity)
    have h2 : (2 * Cn + 5 / 4) * μ ^ 2 * (CM * av * V)
        = (2 * Cn + 5 / 4) * CM * av * μ ^ 2 * V := by ring
    linarith [h1, h2]
  -- ## the credit rows are proportional to `μ·Q`, which the free constant pays
  have hcr : Cq * av * (μ + τ) * Q ≤ Cq * (1 + 2 * Cn) * av * μ * Q := by
    have h1 : μ + τ ≤ (1 + 2 * Cn) * μ := by linarith [hτle]
    have h3 : 0 ≤ Cq * av * Q := by positivity
    have h4 : (Cq * av * Q) * (μ + τ) ≤ (Cq * av * Q) * ((1 + 2 * Cn) * μ) :=
      mul_le_mul_of_nonneg_left h1 h3
    nlinarith [h4]
  have hcmu : Cq * av * μ ≤ Cq * av * μ ^ 2 * V := by
    have h1 : μ ≤ μ ^ 2 * V := by nlinarith [hμV, hμ]
    have h2 : 0 ≤ Cq * av := mul_nonneg hCqnn hav
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith [h3]
  -- ## the completion of the square: `richC·Cn/2 - richKq·Cn/2 = richCgoal + Cn/2`
  have hCc : richCgoal Cn CM Cq D2 ≤ (richC Cn CM Cq D2 - richKq Cn Cq) * Cn / 2 := by
    simp only [richC, richCgoal, richKq]
    have h1 : (Cq * (1 + 2 * Cn)
          + 2 * (Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq
              + (2 * Cn + 5 / 4) * CM) / Cn + 1 - Cq * (1 + 2 * Cn)) * Cn / 2
        = (Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq
            + (2 * Cn + 5 / 4) * CM) + Cn / 2 := by
      field_simp
      ring
    rw [h1]
    linarith
  have hClow : richCgoal Cn CM Cq D2 * av * μ ^ 2 * V
      ≤ (richC Cn CM Cq D2 - richKq Cn Cq) * av * μ * Q := by
    have h1 : richCgoal Cn CM Cq D2 * (μ ^ 2 * V)
        ≤ ((richC Cn CM Cq D2 - richKq Cn Cq) * Cn / 2) * (μ ^ 2 * V) :=
      mul_le_mul_of_nonneg_right hCc (by positivity)
    have h3 : 0 ≤ richC Cn CM Cq D2 - richKq Cn Cq := by
      simp only [richC, richKq, richCgoal]
      have hCn0 : (0 : ℝ) ≤ Cn := hCn4.le
      have h4 : 0 ≤ Cn * CM / 9 := by
        have := mul_nonneg hCn0 hCMnn
        linarith
      have h5 : 0 ≤ 64 * Real.pi * D2 * Cn ^ 2 := by positivity
      have h7 : 0 ≤ (2 * Cn + 5 / 4) * CM := by nlinarith [hCn4, hCMnn]
      have h8 : 0 ≤ 2 * (Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq
          + (2 * Cn + 5 / 4) * CM) / Cn :=
        div_nonneg (by linarith) hCn0
      linarith
    have h4 : ((richC Cn CM Cq D2 - richKq Cn Cq) * Cn / 2) * (μ ^ 2 * V)
        ≤ (richC Cn CM Cq D2 - richKq Cn Cq) * (μ * Q) := by
      calc ((richC Cn CM Cq D2 - richKq Cn Cq) * Cn / 2) * (μ ^ 2 * V)
          = (richC Cn CM Cq D2 - richKq Cn Cq) * ((Cn / 2) * (μ ^ 2 * V)) := by ring
        _ ≤ (richC Cn CM Cq D2 - richKq Cn Cq) * (μ * Q) :=
            mul_le_mul_of_nonneg_left hQlow h3
    have h5 : richCgoal Cn CM Cq D2 * (μ ^ 2 * V)
        ≤ (richC Cn CM Cq D2 - richKq Cn Cq) * (μ * Q) := le_trans h1 h4
    have h6 : richCgoal Cn CM Cq D2 * (μ ^ 2 * V) * av
        = richCgoal Cn CM Cq D2 * av * μ ^ 2 * V := by ring
    have h7 : (richC Cn CM Cq D2 - richKq Cn Cq) * (μ * Q) * av
        = (richC Cn CM Cq D2 - richKq Cn Cq) * av * μ * Q := by ring
    nlinarith [mul_le_mul_of_nonneg_right h5 hav, h6, h7]
  -- ## the pair square
  have hpairsq : 0 ≤ (1 / 2) * ((M2 - W) / V ^ 2) * Pc := by
    have h1 : 0 ≤ M2 - W := by linarith [hWle]
    have h2 : 0 ≤ (M2 - W) / V ^ 2 := div_nonneg h1 (by positivity)
    exact mul_nonneg (mul_nonneg (by norm_num) h2) hPcnn
  -- ## the ledger
  have hrich : richKq Cn Cq = Cq * (1 + 2 * Cn) := rfl
  have hCg : richCgoal Cn CM Cq D2
      = Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq
        + (2 * Cn + 5 / 4) * CM := rfl
  -- ## the ledger, in three linear steps
  have hstep1 : -(2 * Cn + 5 / 4) * μ ^ 2 * W
        - (G * ((n + 1) * n / V ^ 2) * χm + Cq * av * (μ + τ) * Q + Cq * av * μ)
        + richC Cn CM Cq D2 * av * μ * Q
      ≤ A0 + a2 + spec + (1 / 2) * ((M2 - W) / V ^ 2) * Pc
        + richC Cn CM Cq D2 * av * μ * Q := by
    linarith [hA0, ha2, hpairsq]
  have hstep2 : -(2 * Cn + 5 / 4) * CM * av * μ ^ 2 * V
        - 64 * Real.pi * D2 * Cn ^ 2 * av * μ ^ 2 * V
        - Cq * (1 + 2 * Cn) * av * μ * Q - Cq * av * μ ^ 2 * V
        + richC Cn CM Cq D2 * av * μ * Q
      ≤ A0 + a2 + spec + (1 / 2) * ((M2 - W) / V ^ 2) * Pc
        + richC Cn CM Cq D2 * av * μ * Q := by
    linarith [hstep1, hA0b, hmass, hcr, hcmu]
  have hstep3 : (Cn * CM / 9) * av * μ ^ 2 * V
      ≤ A0 + a2 + spec + (1 / 2) * ((M2 - W) / V ^ 2) * Pc
        + richC Cn CM Cq D2 * av * μ * Q := by
    have hKq : richKq Cn Cq * (av * μ * Q) = Cq * (1 + 2 * Cn) * (av * μ * Q) := by
      rw [hrich]
    have hgl : richCgoal Cn CM Cq D2 * (av * μ ^ 2 * V)
        = (Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq + (2 * Cn + 5 / 4) * CM)
            * (av * μ ^ 2 * V) := by
      rw [hCg]
    linarith [hstep2, hClow, hKq, hgl]
  linarith [hstep3, hDm]

end Work.BoseB1Cube

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The excited-rich half of the row is PROVED.**  On `n/2 ≤ n₊` the row follows from the PROVED
port `slidingBogPortCubeContDiff` (which absorbs `bA2 + bSpectralCube` at the price of the mass row
`g0w0Mass·χmass·(n+1)n/V²`) and the PROVED gates, the crude constants `M₁ ≤ CM(a v)V`,
`g0w0Mass ≤ 8π(a v)`, `chiMass ≤ D²V` and the `A₀`-lower bound `a0MainLocBox_lower`: on that half the
free constant `richC` pays every row that is proportional to `μ·n₊` (they are all `≤ ¼·(that)`
because `n₊ ≥ n/2 ≥ CnμV/2`), so no new analytic input is needed. -/
theorem richRow_holds {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) : RichRow v h R := by
  intro Cn hCn
  obtain ⟨εq, Cq, hεq, hCq, hport⟩ :=
    slidingBogPortCubeContDiff (v := v) h hv hv1 hvrad hR hv_supp hav (eps := 1) (by norm_num)
  obtain ⟨εd, hεd, hgates⟩ := boxDataGatesContDiff (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εt, hεt, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨CM, hCM0, hCM⟩ := Work.BoseFixB1.boxM1_le_aV (v := v) (R0 := R) hv_supp hR hv hvrad hv1
    h (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  have hGle : Submission.BoseGases.g0w0Mass h ≤ 8 * Real.pi * _root_.BoseGases.a v :=
    g0w0Mass_le_eight_pi_mul_a hR hv hvrad hv_supp h
  have hGnn : 0 ≤ Submission.BoseGases.g0w0Mass h :=
    Work.BoseB1Cube.g0w0Mass_nonneg hR hv hvrad hv_supp h
  set D2 : ℝ := (Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay (Work.BoseBox.mValue)) ^ 2 with hD2
  have hD20 : 0 ≤ D2 := by rw [hD2]; exact sq_nonneg _
  have ha0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hCnn : 0 ≤ richC Cn CM Cq D2 := by
    simp only [richC, richKq, richCgoal]
    have hCn0 : (0 : ℝ) ≤ Cn := by linarith
    have h1 : 0 ≤ Cn * CM / 9 := by
      have := mul_nonneg hCn0 hCM0
      linarith
    have h2 : 0 ≤ 64 * Real.pi * D2 * Cn ^ 2 := by positivity
    have h3 : 0 ≤ Cq * (1 + 2 * Cn) := by nlinarith [hCq, hCn]
    have h4 : 0 ≤ (2 * Cn + 5 / 4) * CM := by nlinarith [hCn, hCM0]
    have h5 : 0 ≤ 2 * (Cn * CM / 9 + 64 * Real.pi * D2 * Cn ^ 2 + Cq
        + (2 * Cn + 5 / 4) * CM) / Cn := div_nonneg (by linarith) hCn0
    linarith
  refine ⟨min εq (min εd (min εt 1)), richC Cn CM Cq D2,
    lt_min hεq (lt_min hεd (lt_min hεt one_pos)), hCnn, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hnorm hn1 hn2 hrich
  have hAdmq : Work.BoseBoxFix.Adm v εq μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmd : Work.BoseBoxFix.Adm v εd μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmt : Work.BoseBoxFix.Adm v εt μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hμ : 0 < μ := hAdm.1
  have hℓ0 : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hvol, hW1, hM1nn, hM2g, hPcnn, hcS2⟩ := hgates μ hAdmd n Ψ hΨ u hu hnorm
  obtain ⟨hRd, hRχ⟩ := hreg μ hμ hAdmt.2.1
  have hμV : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := _root_.BoseGases.a v) (μ := μ) hav hμ
      hAdm1.2.1 hu
  have hbM : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue :=
    Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
  have hWnn : 0 ≤ Work.BoseFixB1.bW v h μ u := by rw [← hW1]; exact hM1nn
  have hWle : Work.BoseFixB1.bW v h μ u
      ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)) := by
    rw [← hW1]
    exact hM2g
  have hSle : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ ≤ (n : ℝ) := by
    have hh := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := n)
      (ℓ := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
      (Ac := Work.BoseFixB1.bA v μ u) hℓ0 hvol
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _)
      (by rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA,
        Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def])
      (ContDiff.continuous hΨ)
    rwa [hnorm, mul_one] at hh
  have hQnn : 0 ≤ Work.BoseFixB1.bQ v μ Ψ u :=
    Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hPcnn' : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ := hPcnn
  have hWb : Work.BoseFixB1.bW v h μ u
      ≤ CM * (_root_.BoseGases.a v) * Work.BoseFixB1.bV v μ u := by
    rw [← hW1, hbM]
    exact hCM hℓ0 hd0 hRd hRχ u
  have hχmle : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u ≤ D2 * Work.BoseFixB1.bV v μ u := by
    rw [hD2, hbM]
    exact Work.BoseFixB1S.chiMass_le_const_mul_boxMass (M := Work.BoseBox.mValue)
      (by norm_num [Work.BoseBox.mValue]) hℓ0 hd0 u
  have hχmnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hA0 : -(2 * Cn + 5 / 4) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
      ≤ Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
          (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) Ψ) :=
    a0MainLocBox_lower (by linarith) hvol hμ hWnn hμV hSle hn2
  have ha2 : -(Submission.BoseGases.g0w0Mass h * (((n : ℝ) + 1) * (n : ℝ)
          / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
      + Cq * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bQ v μ Ψ u
      + Cq * (_root_.BoseGases.a v) * μ)
      ≤ Work.BoseFixB1.bA2 v h μ Ψ u + Work.BoseFixB1S.bSpectralCube v μ Ψ u := by
    have hp := hport μ hAdmq n Ψ u hu hΨ
    simp only [Work.BoseFixB1.bI] at hp
    rw [hnorm] at hp
    have hsimp : (1 / 2) * ((1 + 1) * Submission.BoseGases.g0w0Mass h)
          * (((n : ℝ) + 1) * (n : ℝ) / Work.BoseFixB1.bV v μ u ^ 2) * 1
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
        = Submission.BoseGases.g0w0Mass h
            * (((n : ℝ) + 1) * (n : ℝ) / Work.BoseFixB1.bV v μ u ^ 2)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u := by ring
    rw [hsimp] at hp
    linarith [hp]
  have hτV : ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bV v μ u = (n : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt hvol)
  have hτle : (n : ℝ) / Work.BoseFixB1.bV v μ u ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hvol]
    exact hn2
  have hQrich : (1 / 2) * (((n : ℝ) / Work.BoseFixB1.bV v μ u)
      * Work.BoseFixB1.bV v μ u) ≤ Work.BoseFixB1.bQ v μ Ψ u := by
    rw [hτV]
    exact hrich
  exact richArith hCn hμ ha0 hvol hWnn hμV hQnn hPcnn' hD20 hCM0 hCq hGnn hGle hχmnn
    hχmle hSle hn1 hn2 hτV hτle hQrich hWb hWle hA0 ha2

/-- **`SharpRow2` from the two halves.**  The dichotomy `n/2 ≤ n₊` versus `n₊ < n/2`
(`le_or_gt`) and `C := max C_rich C_poor`. -/
theorem sharpRow2_of_rich_poor {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (ha : 0 ≤ _root_.BoseGases.a v) (hR : RichRow v h R) (hP : PoorRow v h R) :
    SharpRow2 v h R := by
  intro Cn hCn
  obtain ⟨εr, Cr, hεr, hCr, hr⟩ := hR Cn hCn
  obtain ⟨εp, Cp, hεp, hCp, hp⟩ := hP Cn hCn
  refine ⟨min εr εp, max Cr Cp, lt_min hεr hεp, le_max_of_le_left hCr, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hnorm hn1 hn2
  have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have hQn : 0 ≤ Work.BoseFixB1.bQ v μ Ψ u := Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have h3 : 0 ≤ (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u :=
    mul_nonneg (mul_nonneg ha hμ.le) hQn
  have hbQ : Work.BoseFixB1.bQ v μ Ψ u
      = Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ := rfl
  rcases le_or_gt ((1 / 2) * (n : ℝ)) (Work.BoseFixB1.bQ v μ Ψ u) with hge | hlt
  · rw [← hbQ]
    have h1 := hr μ hAdmr n Ψ u hu hΨ hsupp hnorm hn1 hn2 hge
    have h2 : Cr * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u
        ≤ max Cr Cp * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u := by
      have h5 : Cr * ((_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u)
          ≤ max Cr Cp * ((_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u) :=
        mul_le_mul_of_nonneg_right (le_max_left Cr Cp) h3
      nlinarith [h5]
    linarith [h1, h2]
  · rw [← hbQ]
    have h1 := hp μ hAdmp n Ψ u hu hΨ hsupp hnorm hn1 hn2 hlt
    have h2 : Cp * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u
        ≤ max Cr Cp * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u := by
      have h5 : Cp * ((_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u)
          ≤ max Cr Cp * ((_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u) :=
        mul_le_mul_of_nonneg_right (le_max_right Cr Cp) h3
      nlinarith [h5]
    linarith [h1, h2]

/-- **The node follows from the nearly-flat residual** (`RichRow` being PROVED). -/
theorem nomRowLinWindowRow_of_poorRow {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hP : PoorRow v h R) : NomRowLinWindowRow v h R :=
  nomRowLinWindowRow_of_sharpRow2 h hv hv1 hvrad hR hv_supp hav
    (sharpRow2_of_rich_poor (le_of_lt hav) (richRow_holds h hv hv1 hvrad hR hv_supp hav) hP)

end Work.BoseB1Cube

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
set_option maxHeartbeats 1600000

/-- **(1) The word decomposition of the (PORT-POOR) assembly.**  `sbWordCube` splits into the
gap column `bGapCoeff·n₊`, the cube-windowed spectral slot `bSpectralCube` and the box-projection
word `boxQSum` — the identity that turns the rung `boxQSum_ge_sharpInc_bV` into a lower bound for
the word.  See `FINDING_nomRowLinWindowRow_session7.md` §6. -/
theorem sbWordCube_eq_gap_add_spectral_add_boxQSum {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {εr μ : ℝ} (hadmr : Work.BoseBoxFix.Adm v εr μ)
    {n : ℕ} {Ψ : X n → ℝ} (hΨc : Continuous Ψ) (u : E3)
    (hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16)
    (hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0)
    (hvol : 0 < Work.BoseFixB1.bV v μ u) :
    Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = Work.BoseFixB1.bGapCoeff v μ
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
        + Work.BoseFixB1S.bSpectralCube v μ Ψ u
        + Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μ
            (Work.BoseFixB1.bA v μ u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
            (Submission.BoseGases.omC (Classical.choose h)) Ψ := by
  classical
  -- a bound witness for `bqPotsplitBdd`
  obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.abox_compact n (Work.BoseFixB1.adm_ell_pos hadmr)).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ)) (f := Ψ) hΨc.continuousOn
  set Bb : ℝ := max C₀ 0 with hBbdef
  have hB0 : 0 ≤ Bb := le_max_right _ _
  have hbound : ∀ y ∈ Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
      |Ψ y| ≤ Bb := by
    intro y hy
    have h1 : ‖Ψ y‖ ≤ C₀ := hC₀ y hy
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  have hsplit := Work.BoseFixB1C.bqPotsplitBdd (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
    (μ := μ) (M := Work.BoseFixB1.bM v μ) (by simp only [Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]; norm_num)
    (Work.BoseFixB1.adm_ell_pos hadmr) (Work.BoseFixB1.adm_d_pos hadmr) hR16 hRχ u hvol
    hΨc.measurable hB0 hbound
  simp only [Work.BoseFixB1.bM] at hsplit
  rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, Work.BoseFixB1.sbPot,
    Work.SmallBoxSliding.qLHSwordB]
  simp only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM, Work.BoseFixB1.bA,
    Work.BoseFixB1.bV, Work.BoseFixB1B.cubeSpectral]
  rw [hsplit]
  simp only [Work.UBBInputs8.cnPlusBoxInd, Work.BoseFixB1S.boxQCount,
    Work.BoseFixB1S.bSpectralCube, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM,
    Work.BoseFixB1.bA, Work.BoseFixB1.bV]

/-- **⭐ (★) THE PAIR/FIBRE DECOMPOSITION OF THE MATCHED WORD** — the identity that puts the
state's own measured pair energy `pairSum` and its fibre row `μ·fibSum` *in the open*:

    sbWordCube v h μ u Ψ  =  bGapCoeff v μ · bQ v μ Ψ u  +  bSpectralCube v μ Ψ u
                             +  pairSum … Ψ  −  μ · fibSum … Ψ .

It is definitional plus one PROVED input: `sbWordCube = sbKinCube + sbPot`
(`matchedWindowDefs`), `sbKinCube = bGapCoeff·bQ + cubeSpectral`, and FS's `eq:HBU` split
`sbPot = pairSum − μ·fibSum` (`Work.BoseFixB1.sbPot_split`).  No `boxQSum`/`bqPotsplitBdd`
identification is needed — hence no volume hypothesis — and the side conditions are exactly those of
`sbPot_split`.

**Consequences.**  With (★), the node's clause `D ≤ sbWordCube` is *equivalent* to

    (NODE)   D·I + μ·fibSum  ≤  bGapCoeff·bQ + bSpectralCube + pairSum ,

i.e. "the gap column, the windowed spectral slot and the state's own pair energy pay the demand
plus the fibre row".  Every arm of the small-window case can now be read off `(NODE)`:

* the **pair arm** (`sbWordCube_ge_demand_of_pairSum`, PROVED) is the case
  `D + μ·fibSum ≤ pairSum`;
* the **flat arm** (`flatArm37RowNode`, PROVED) is the case `FlatArm37`;
* the **gap arm** (`smallWinGapArmGen`, PROVED) is the case `bQ ≥ c₀`;
* the **razor route** (`Free/RazorRoute.lean`) substitutes a *sharp* razor
  `(1/4)τ² + (1/2)μτ − (1/4)μ²)W·I ≤ bSpectralCube + pairSum + (payable rows)` into (★) and
  cancels `pairSum`, leaving only the PROVED manifest fibre bound
  (`Work.BoseFixB1S.fibSum_le_manifest`), the *free* gate column (`PerBoxGapAbsorbB1`) and the
  pure-real arithmetic `razorCoversDemandFibre`.

This is the operator-requested identity of `FINDING_nomRowLinWindowRow_session10.md` §1quinquies. -/
theorem sbWordCube_eq_gap_spectral_pair_sub_fibre {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {εr μ : ℝ} (hadmr : Work.BoseBoxFix.Adm v εr μ)
    {n : ℕ} {Ψ : X n → ℝ} (hΨc : Continuous Ψ) (u : E3)
    (hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16)
    (hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0) :
    Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
        + Work.BoseFixB1S.bSpectralCube v μ Ψ u
        + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
        - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ := by
  rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube,
    Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hadmr hΨc u
      (by simpa only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using hR16)
      (by simpa only [Work.BoseFixB1.bSide] using hRχ)]
  simp only [Work.BoseFixB1.bQ, Work.UBBInputs8.cnPlusBoxInd, Work.BoseFixB1B.cubeSpectral,
    Work.BoseFixB1S.bSpectralCube, Work.BoseFixB1S.boxQCount, Work.BoseFixB1.bSide,
    Work.BoseFixB1.bD, Work.BoseFixB1.bM, Work.BoseFixB1.bA, Work.BoseFixB1.bV]
  ring

end Work.BoseB1Cube

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **(2a) The rung at the word level.**  The rung `boxQSum_ge_sharpInc_bV` transported to
`sbWordCube` through the decomposition `sbWordCube_eq_gap_add_spectral_add_boxQSum`: the gap column
and the spectral slot are nonnegative, so the rung's left-hand side is dominated by the *word*. -/
theorem sbWordCube_ge_rungRows {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {εr μ C' : ℝ} {n : ℕ} {Ψ : X n → ℝ} {u : E3}
    (hadmr : Work.BoseBoxFix.Adm v εr μ) (hΨc : Continuous Ψ)
    (hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16)
    (hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0)
    (hvol : 0 < Work.BoseFixB1.bV v μ u)
    (hbGap : 0 ≤ Work.BoseFixB1.bGapCoeff v μ)
    (hcs : 0 ≤ Work.BoseFixB1S.bSpectralCube v μ Ψ u)
    (hrung : Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
              (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
            + Work.BoseFixB1.bA2 v h μ Ψ u
            + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)))
                  / (Work.BoseFixB1.bV v μ u) ^ 2)
                * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) Ψ
            - (1 / 4) * ((Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
                * (Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bA v μ u) Ψ
                  + (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                        (Work.BoseFixB1.bA v μ u) Ψ) ^ 2
                  - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bA v μ u) Ψ)
            - C' * (_root_.BoseGases.a v)
                * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
                      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
                    / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) Ψ
            + Work.BoseFixB1.boxSqPart (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u v)
                (Submission.BoseGases.omC (Classical.choose h)) Ψ
            ≤ Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μ
                (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u v)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
                (Submission.BoseGases.omC (Classical.choose h)) Ψ) :
    Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
        (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
      + Work.BoseFixB1.bA2 v h μ Ψ u
      + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)))
            / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
      - (1 / 4) * ((Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * (Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ
            + (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bA v μ u) Ψ) ^ 2
            - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ)
      - C' * (_root_.BoseGases.a v)
          * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) Ψ
      + Work.BoseFixB1.boxSqPart (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u v)
          (Submission.BoseGases.omC (Classical.choose h)) Ψ
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
  rw [sbWordCube_eq_gap_add_spectral_add_boxQSum (v := v) h hv hv1 hvrad hR hv_supp hadmr hΨc u
    hR16 hRχ hvol]
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ := Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have h1 : 0 ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ := mul_nonneg hbGap hQnn
  linarith [hrung, h1, hcs]

end Work.BoseB1Cube


namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem demand_le_sbWordCube_of_ledgerRows {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    {εr μ eps C K : ℝ} {n : ℕ} {Ψ : X n → ℝ} {u : E3}
    (hadmr : Work.BoseBoxFix.Adm v εr μ) (hΨc : Continuous Ψ)
    (hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16)
    (hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0)
    (hvol : 0 < Work.BoseFixB1.bV v μ u)
    (hbQthr : 1 ≤ K * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
    (hK : 0 < K) (hC : 0 ≤ C)
    (hboxsq : 0 ≤ Work.BoseFixB1.boxSqPart (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u v)
                (Submission.BoseGases.omC (Classical.choose h)) Ψ)
    (hKa : K * (_root_.BoseGases.a v) * μ ≤ Work.BoseFixB1.bGapCoeff v μ)
    (hKC : C * (2 * μ + (n : ℝ) / Work.BoseFixB1.bV v μ u + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u)
              + C * μ * K ≤ K * μ)
    (hcsrow : -((1 / 2) * (1 + eps)
                  * (Submission.BoseGases.g0w0Mass h
                      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                          (Work.BoseFixB1.bD v μ) u)
                  * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
                + C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                    * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
                + C * (_root_.BoseGases.a v) * μ)
              ≤ Work.BoseFixB1S.bSpectralCube v μ Ψ u + Work.BoseFixB1.bA2 v h μ Ψ u)
    (hrung : Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
              (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
            + Work.BoseFixB1.bA2 v h μ Ψ u
            + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)))
                  / (Work.BoseFixB1.bV v μ u) ^ 2)
                * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) Ψ
            - (1 / 4) * ((Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
                * (Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bA v μ u) Ψ
                  + (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                        (Work.BoseFixB1.bA v μ u) Ψ) ^ 2
                  - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bA v μ u) Ψ)
            - C * (_root_.BoseGases.a v)
                * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
                      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
                    / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) Ψ
            + Work.BoseFixB1.boxSqPart (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u v)
                (Submission.BoseGases.omC (Classical.choose h)) Ψ
            ≤ Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μ
                (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u v)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u)
                (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
                (Submission.BoseGases.omC (Classical.choose h)) Ψ)
    (hhalf : (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)) - Work.BoseFixB1.bW v h μ u)
                  / (Work.BoseFixB1.bV v μ u) ^ 2) * ((Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ) ^ 2 - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
              ≤ (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))) / (Work.BoseFixB1.bV v μ u) ^ 2) * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
                  - (1 / 4) * ((Work.BoseFixB1.bW v h μ u) / (Work.BoseFixB1.bV v μ u) ^ 2)
                      * (Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ + (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ) ^ 2 - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ))
    (hcore : (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
                + C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
                + C * (_root_.BoseGases.a v) * μ
                + C * (_root_.BoseGases.a v) * (μ + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ
              ≤ Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μ (Work.BoseFixB1.bW v h μ u)
              (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
                + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)) - Work.BoseFixB1.bW v h μ u)
                    / (Work.BoseFixB1.bV v μ u) ^ 2) * ((Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ) ^ 2 - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ)
                - (1 / 2) * (1 + eps)
                    * (Submission.BoseGases.g0w0Mass h
                        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                            (Work.BoseFixB1.bD v μ) u)
                    * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
                + Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ) :
    (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
  rw [sbWordCube_eq_gap_add_spectral_add_boxQSum (v := v) h hv hv1 hvrad hR hv_supp hadmr hΨc u
    hR16 hRχ hvol]
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Ψ :=
    Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  exact poorRowLedgerArith (Var := 0) (a := _root_.BoseGases.a v) (n := (n : ℝ))
    hvol hadmr.1 (le_of_lt hav) hQnn (Nat.cast_nonneg n) hbQthr hK hboxsq hKa hC hKC hcsrow
    hrung hhalf hcore


end Work.BoseB1Cube

