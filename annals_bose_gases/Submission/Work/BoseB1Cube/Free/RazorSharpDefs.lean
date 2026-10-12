import ChallengeDeps
import Submission.Work.BoseFixB1.perBoxF_localised
import Submission.Work.BoseFixB1B.matchedWindowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Free.RazorSharpDefs` — **the sharp razor** (FS
# `lm:appinteractionestimate`), the instrument that closes the node's small-window case

Holder: `Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean` (session 11).  Definitions only, hence
`sorry`-free and importable by anyone (in particular by the prover of `RazorSharpF` itself, whose
cone must stay free of `Submission.Work.BoseB1Cube.nomRowLinWindowRow`).

## What it says

For every window constant `Cn ≥ 4` there are `ε₀ > 0` and a *fixed* constant `C₀ ≥ 0` such that for
every admissible `μ`, every in-box `ContDiff` state `Φ` on `X n` with `∫Φ² = 1` in the node's count
window `Cn·μ·|B(u)| ≤ n ≤ 2Cn·μ·|B(u)|`,

    (RAZOR)  ((1/4)τ² + (1/2)τμ − (1/4)μ²)·W
               ≤  cubeSpectral v μ Φ u + pairSum v M ℓ d u Φ + C₀·(a v)·(μ + τ)·n₊ ,

`τ := n/|B(u)|`, `W := bW = w1MassB` (`= M₁`, FS's `eq:w1>` mass), `n₊ := bQ` the box-excited
count.  **There is no `∝ ‖Φ‖²` error row**: the state-independent credit `C·(μ²(a v)Γχ + μ(a v))·I`
of the chapter's `Work.BoseB1Cube.RazorNom` is *absent*, and the `n₊`-row (which *is* present) is
paid by the **free gate column** `bGapCoeff·n₊ ≥ Kg·(a v)·μ·n₊` for *any* prescribed fixed `Kg`
(`Work.BoseFixB1S.PerBoxGapAbsorbB1`), so `C₀` is immaterial.

## Why exactly this form (and not `RazorNom`)

* **`RazorNom` (and `HoleRow`) cannot close this node.**  Their credit row `C(μ²(a v)Γχ + μ(a v))I`
  must be paid by the razor's surplus `μ²W·(¼λ² − 5λ/9 − ¼)`, which is `≥ 1.53·μ²W` at `λ = 4`; with
  the small window `μW ≤ (a v)` that needs `C ≤ 1.53` — a *fixed* constant of order 1 — while the
  chapter's ports have `C ≳ 10^{58}`.  A proof with an existential (hence arbitrarily large) `C` is
  therefore *vacuous* for this node; the razor must be *sharp*, exactly as in FS.
* **This form closes the node unconditionally** — no `bQ`-threshold, no corner `μ|B| < 32`, no
  `FlatArm37`/pair-dead dichotomy.  The deduction (proved in
  `Submission/Work/BoseB1Cube/Free/RazorSharp.lean`, `razorSharpF_imp_smallWinPropF`) is:
  with the PROVED identity (★)
  `sbWordCube = bGapCoeff·n₊ + cubeSpectral + pairSum − μ·fibSum`
  (`matchedWindowDefs` + `Work.BoseFixB1.sbPot_split`), the node's clause
  `(1/18)μτW ≤ sbWordCube` follows from (RAZOR) together with
  (i) the PROVED manifest fibre bound `Work.BoseFixB1S.fibSum_le_manifest`,
  (ii) the *free* gate column, and
  (iii) the PROVED pure-real `razorCoversDemandFibre` (`(19/18)μτW ≤ (¼τ²+½μτ−¼μ²)W` for `τ ≥ 4μ`).
  No other hypothesis is used: in particular the proof of the node's small-window case needs
  **no** `bQ < c₀`, **no** `¬FlatArm37`, **no** pair-deadness, and **no** box-size restriction.
* The trace of the arithmetic is in `Submission/Work/BoseB1Cube/Free/RazorSharp.lean`'s docstring
  and in `Submission/Work/BoseB1Cube/FINDING_nomRowLinWindowRow_session11.md`: the three rows of
  `fibSum_le_manifest` (the flat row `∝ S`, the `√`-row and the `∝ n₊` row) are absorbed by
  `bGapCoeff·n₊` with a **fixed** `Kg = max (2Cm) (4C₀(1+2Cn)) (4Cm²·(a v)·2Cn/κ₄)`,
  `κ₄ = ¼·16 − 20/9 − ¼ = 1.5277…`, `Cm` the manifest constant.  The two regimes of the `√`-row
  (with and without the threshold `n₊ ≥ 16Cm²τW/Kg²`) both close, so no threshold survives.

## What is *not* claimed here

Nothing in this file asserts (RAZOR).  It is the chapter's single analytic frontier (FS's
`lm:appinteractionestimate`): its margin is the strict scattering gap
`Work.ScatGap.av_lt_suppR` (`a v < mfSuppR v`) against the capacity chronology, and the recorded
route is the void/capacity engine (`Work.BoseFixB1S.voidCapDualityB1`, `voidCapBall`,
`Work.BoseAnalysis...slotCapacityAeFam`) plus the pair-marginal aggregation.  The statement is
*sharp* on the calibration family (`Submission/Work/BoseB1Cube/FINDING_nomRowRazor.md` ADDENDUM:
the shallow-dip family gives `min_d[d²A + (1−d)²β] = Aβ/(A+β)` with `A = mfSuppR v/(a v) > 1`,
`β = M₂/M₁ ≤ 2·(1+o(1))`), and it is **not** the strong form `(1/2)τ²W ≤ …`, which that family
refutes.
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

/-- **The sharp razor** — FS `lm:appinteractionestimate` in the spectral currency, at the sliding
box, the single cube cutoff `chiSmallB`, at the node's own count window, and with **no
state-independent credit row** (see the module docstring for why this exact form is the one the node
consumes, and why `RazorNom`'s existential credit cannot be used). -/
def RazorSharpF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Φ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Φ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        ((1 / 4) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) ^ 2)
            + (1 / 2) * (((n : ℝ) / Work.BoseFixB1.bV v μ u) * μ) - (1 / 4) * μ ^ 2)
          * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.cubeSpectral v μ Φ u
            + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u Φ
            + C₀ * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ Φ u


/-- **The MINIMAL sufficient demand row** (the node's own inequality with the gap column deleted and a
*payable* row added).  At the node's state class (normalised, in-box, `ContDiff`, count window)

    (DEMAND)  (1/18)·μ·τ·W·1  +  μ·fibSum  ≤  cubeSpectral + pairSum + C₀·(a v)·(μ+τ)·n₊ .

**Why this is the weakest form the node can consume.**  With (★) the node's clause
`(1/18)μτW ≤ sbWordCube` is *equivalent* to `(1/18)μτW + μ·fibSum ≤ bGapCoeff·n₊ + cs + pairSum`;
the gap column `bGapCoeff·n₊ ≥ Kg·(a v)·μ·n₊` is *free* (`Kg` fixed, `PerBoxGapAbsorbB1`), and with
`τ ≤ 2Cn·μ` it pays any row `C₀·(a v)·(μ+τ)·n₊` with `C₀(1+2Cn) ≤ Kg`.  So **(DEMAND) ⟹ the
node's small-window arm** in one `linarith` — no manifest fibre bound, no Young/AM-GM step, no razor
surplus, no `μ|B|`-corner (`Free/RazorSharp.lean`, `razorDemandF_imp_smallWinPropF`).

**(DEMAND) is strictly weaker than `RazorSharpF`'s inequality** in every regime that matters for the
hole: at a pair-suppressed state the left-hand side is `(19/18)μτW ≈ (19/(9λ))·D_strong`
(`D_strong = ½τ²W`), whereas `RazorSharpF` demands `(¼λ²+½λ−¼)μ²W ≈ (2(¼λ²+½λ−¼)/λ²)·D_strong`,
i.e. `0.528·D_strong` against `0.719·D_strong` at the smallest admissible `λ = Cn = 4`.  The sharp
capacity supply is `(mfSuppR v/(a v))·D_strong` with the PROVED strict gap `a v < mfSuppR v`
(`ScatGap.av_lt_suppR`), so (DEMAND) tolerates a **47 %** loss in the aggregation where
`RazorSharpF`/`RazorHole` tolerate only **28 %**.

⚠ (DEMAND) is *not* implied by `RazorSharpF` by any route recorded so far (the manifest's `√`-row
needs either the gate — absent from (DEMAND)'s right-hand side — or the razor's surplus), so it is a
genuinely *different*, and genuinely *easier*, instrument; and it is *not* a rewording of the node's
own lemma: (DEMAND) ⟹ the node's arm only after spending the free gate column. -/
def RazorDemandF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ C₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : X n → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ContDiff ℝ (⊤ : ℕ∞) Φ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Φ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          + μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Φ
          ≤ Work.BoseFixB1B.cubeSpectral v μ Φ u
            + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u Φ
            + C₀ * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ Φ u

end Work.BoseB1Cube
