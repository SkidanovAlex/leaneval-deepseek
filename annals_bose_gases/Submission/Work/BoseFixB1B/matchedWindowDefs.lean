import ChallengeDeps
import Submission.Work.BoseFixB1.PerBoxNames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.matchedWindowDefs` — the **matched-window (single cube cutoff)**
# vocabulary of the small-box chapter, and its localisation **statement**

Holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.  Definitions only, hence `sorry`-free.

## Why this vocabulary

The *frozen* sliding word `sbWord = sbKin + sbPot` mixes FS's two cutoffs: its potential slot
`sbPot` carries the kernels whose window is the **cube** bump `chiSmallB`, while its kinetic slot
`sbKin = bGapCoeff·n₊ + bSpectral` carries the **ball** window `chiB`.  The two instruments that
actually *pay* the pairing — the rung-4 payment `Work.BoseFixB1S.a0A2PaymentAdm_holds` and the
Bogoliubov port `Work.BoseFixB1B.slidingBogPort_proved : SlidingBogPort` — are both stated at the
**matched** (`chiSmallB`) window, in the slot `bA2 + bSpectralCube`.  Composing them with the frozen
`sbKin` therefore needs the `chiB`/`chiSmallB` window comparison, and that comparison is **not an
independent input**: its only route consumes the a-priori supply `μ·M_w ≤ C·rows`, which is
equivalent to this very node (`FINDING_flatArmCountInputs.md` §3).

Running the chapter at the **single cube cutoff** removes the comparison and its node-fragment —
this is FS's own modelling (`eq:chiBdefinition`: one `χ_B` for both slots).  This module is that
vocabulary:

* `cubeSpectral v μ Φ u` — FS's single-cutoff windowed spectral slot at the cube window
  `chiSmallB`.  It is *definitionally* `Work.BoseFixB1S.bSpectralCube v μ Φ u` (same body, copied
  here so that this module's import cone does not have to contain
  `Submission.Work.BoseFixB1S.boxBogPortSliding`, whose closure is currently broken by a
  neighbour's in-progress file);
* `sbKinCube v μ u Φ` = `bGapCoeff v μ · n₊(B) + cubeSpectral v μ Φ u` — the frozen `sbKin` with
  its spectral slot read at `chiSmallB`;
* `sbWordCube v h μ u Φ` = `sbKinCube + sbPot` — the matched sliding word, FS's `H_{B(u)}(μ)` at
  the cube cutoff;
* `SlidingBCube v h` — **FS `eq:BSsliding2` / Bratteli–Solovej Thm 3.10 at the cube cutoff**
  (statement only, see below).

## The missing statement on this route (put on record here; the proof is NOT attempted)

`SlidingBCube v h` is the matched-window **localisation**

    (b / (2ℓ²))·⟨n₊⟩_Λ + (1/C)·∫_u sbWordCube h μ u Φ  ≤  wordB v h μ n Φ .

It is **not inheritable** from the proved ball-cutoff `Work.BoseFixB1.SlidingB`
(`Work.BoseFixB1B.slidingB_holds_from_assembly`, `..._from_proved`): the localisation is a *lower*
bound for `boxFormB` in terms of the *frozen* word, and `sbWordCube ≥ sbWord` pointwise (the cube
window dominates the ball window on the support of the box-mean-free fibre), so the matched
statement is strictly stronger — see `FINDING_wholeBoxSocket.md` §3, which also records why the
naive replacement fails.

What the corpus *does* have: the **one-body kinetic half** at the ball cutoff
(`Work.BoseFixB1.Core.oneBodyKineticHalf_core`, `Work.BoseFixB1.KineticHalf`), whose proof runs
through `Core.meanMismatch_le` / `Core.spectral_chain` / `Core.pnorm_payment` — all three stated
with the ball window `chiB`/`chiScale`, so they must be re-run at `chiSmallB` (that is the concrete
first *mathematical* task of this route, not the statement below).  Also relevant, because it says
which forms of a window transfer are *honest*: `FINDING_slidingWindowComparison_analysis.md` §7
(the `chiScale ℓ`-windowed slot is junk-zero; only windows supported in the box **and flat on
`∂A`** — `chiB`, `chiSmallB` — can be used as intermediates).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's single-cutoff windowed spectral slot at the **cube** window `chiSmallB` — definitionally
`Work.BoseFixB1S.bSpectralCube` (same body; see the module docstring for why it is copied here). -/
noncomputable def cubeSpectral (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
    (Work.BoseFixB1.bV v μ u)
    (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u)
    (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ

/-- **The matched (cube-cutoff) kinetic word**: the frozen `sbKin`'s gap row
`bGapCoeff v μ · n₊(B)` together with the cube-windowed spectral slot — the slot the PROVED port
`SlidingBogPort` pays the pairing with. -/
noncomputable def sbKinCube (v : E3 → ℝ) (μ : ℝ) (u : E3) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.BoseFixB1.bGapCoeff v μ
      * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Φ
    + cubeSpectral v μ Φ u

/-- **The matched sliding word** `sbWordCube = sbKinCube + sbPot`: the frozen `sbWord` with its
kinetic spectral slot moved to the cube cutoff `chiSmallB`, so that it matches the kernels and the
proved port. -/
noncomputable def sbWordCube (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  sbKinCube v μ u Φ + Work.BoseFixB1.sbPot h μ u Φ

/-- **FS `eq:BSsliding2` (Bratteli–Solovej Thm 3.10) at the single cube cutoff** — the
**matched-window localisation**: the large-box form `boxFormB` (= `wordB`, FS's `H_Λ(μ)`) dominates
the large-box kinetic gap plus the `u`-integral of the matched small-box words `sbWordCube`.

**Statement only — not proved, and `sorry`-free because it is a `def : Prop`.**  See the module
docstring for why it cannot be inherited from the proved ball-cutoff `SlidingB`, and for the
concrete first mathematical task (re-running the one-body kinetic half at `chiSmallB`).  The
constant `C ≥ 1` in front of the integral is free, exactly as in `Work.BoseFixB1.SlidingB`. -/
def SlidingBCube (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / C) * ∫ u : E3, sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseBoxFix.wordB v h μ n (Φ : Submission.BoseGases.X n → ℝ)

end Work.BoseFixB1B
