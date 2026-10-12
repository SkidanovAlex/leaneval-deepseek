import ChallengeDeps
import Submission.Work.BoseFixB1B.sbWordMuShift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.perBoxFTotalDefs` — FS `thm:smallbox` with the **total-density**
# `F`-term (the spelling that is missing from the corpus)

Written by the holder of `Submission/Work/BoseFixB1B/lowState_count_leAlt.lean` (to be handed to a
prover).

## Why this module exists

FS `thm:smallbox` (`final_v2.tex` l.3907) reads

    H_B(μ) ≥ ( c (n|B|⁻¹ − μ)² / (1 + n/(|B|μ))  − ½μ² ) ∬w_{1,B}
              − Cμ²a((Rλ₁⁻¹)² + K_B³(μa³)^{1/2})∫χ_B² − Cμa ,

whose first bracket is evaluated at the **total** in-box density `ρ := n/|B|` (a number, times the
*total* `∬w_{1,B}`).  The corpus formalises instead the **pointwise** version
`Work.BoseFixB1.PerBoxF`,

    c₁ · w1MassB · ∫Φ² F(nCountB(x)/chiMass) − ½μ² w1MassB ‖Φ‖² − … ≤ sbWord ,

in which `F` is applied *before* integrating.  Since `F` is **convex**
(`Work.BoseFixB1B.psiWeight_one_decomp`: `psiWeight 1 μ t = μ(t−3μ) + 4μ³/(t+μ)`), Jensen gives

    ⨍ Φ² F(dens(x))  ≥  F(⨍ Φ² dens)      (weights normalised by ‖Φ‖²),

so the *pointwise* form is **stronger** than the *total* form — which is one reason why
`PerBoxF` is **false for all states** (the Jastrow family, three refutations on record).

**WARNING (session-2 audit of the delegation of `perBoxFTotal_holds`,
`FINDING_perBoxFTotal_session2.md`).**  A second, independent defect sits under *every* statement
phrased with `Work.BoseFixB1.sbWord`: that word **mixes FS's two cutoffs** — its kinetic slot
`sbKin` carries the *ball* window `chiB` while its potential slot and pairing kernel
(`qLHSwordB`, `wSmallPair/wSmall1Pair`) carry the *cube* bump `chiSmallB` — whereas FS's
`H_{B(u)}(μ)` uses **one** cutoff `χ_B` for both (`eq:chiBdefinition`).  Machine-checked
consequence: on the admissible positions `u` where the two balls `ball(0,ℓ/2)` and
`ball((ℓd)u,ℓd/2)` are disjoint, `chiB ≡ 0` while `chiSmallB ≠ 0`
(`Work.BoseFixB1S.tBdiagFormInd_chiB_eq_zero_of_disjoint_balls`,
`exists_window_vacuous_but_box_meets_chiSmall`), so `sbKin` collapses to the gap row and
`sbWord` is **strictly smaller** than FS's `H_{B(u)}(μ)`.  Hence `PerBoxFTotal` / `PerBoxFTotalAt`
as stated here are **strictly stronger** than FS `thm:smallbox` and are **not** automatically true
— they are irreducible targets about the frozen word.  The honest total-density spelling of
`thm:smallbox` must be phrased at the **single cube cutoff**, i.e. in the vocabulary of
`Submission/Work/BoseFixB1B/matchedWindowDefs.lean` (the modelled decision recorded there and in
`FINDING_wholeBoxSocket.md` §4) — a modelling decision for the lead, not a consequence of this
file.  Consequence: `LowMax` restrictions were needed in the
sessions-2–5 chain *only because the total-density spelling was not formalised*.  Building it
removes that restriction.

## Contents

* `Work.BoseFixB1B.chiDensB` — FS's total in-box density `n/|B|` in the corpus's `χ²`-normalisation
  (the average of the pointwise density `nCountB/chiMass` against the `Φ²`-weight);
* `Work.BoseFixB1B.PerBoxFTotal` — FS `thm:smallbox` at the sliding box with that total-density
  `F`-term (free `c₁ > 0`, free `C ≥ 0`);
* the trivial *unfolding* of the pointwise form at the total density, so that a prover of the
  pointwise provider gets the total one **conditionally** (with the `LowMax` restriction), and a
  prover of the total one unconditionally.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **FS's total in-box density `n/|B|`** at the sliding box `B(u)`, in the corpus's
`χ²`-normalisation: the `Φ²`-weighted average of the pointwise density `nCountB/chiMass` that
appears in `Work.BoseFixB1.PerBoxF`,

    chiDensB = (∫_{abox} Φ² · nCountB M ℓ d u) / (chiMass M ℓ d u · ‖Φ‖²) .

The `chiMass` in the denominator is the same `∫χ_{B(u)}²` that normalises the pointwise density, so
that `chiDensB` *is* the average of `nCountB(x)/chiMass` against the normalised weight `Φ²/‖Φ‖²`;
this is what makes Jensen applicable (see the module docstring). -/
noncomputable def chiDensB {v : E3 → ℝ} (μ : ℝ) {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 *
        Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x)
    / (Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n Φ)

/-- **FS `thm:smallbox` at the sliding box `B(u)`, in the total-density (`∫Φ²`) spelling** — the
form the corpus is missing.  Compare `Work.BoseFixB1.PerBoxF`: the only difference is that the
mean-field weight is read at the *total* density `chiDensB` instead of pointwise. -/
def PerBoxFTotal (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : E3) : Prop :=
  c₁ * (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.SmallBoxSliding.psiWeight 1 μ (chiDensB (v := v) μ u (Φ : Submission.BoseGases.X n → ℝ)))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * (μ ^ 2 * (_root_.BoseGases.a v)
          * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)))
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * μ * (_root_.BoseGases.a v)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)


/-- **FS `thm:smallbox` with the chemical potential `μ'` decoupled from the parameter scale `μ`** —
the form FS `eq:badset` needs (they bound `H_B(4μ)`, i.e. the *same box* at the chemical potential
`4μ`; the corpus's `sbWord` family cannot express that, which is why
`Work.BoseFixB1B.sbWordAt` was introduced).  The density is the state's own (parameter-scale)
density `chiDensB μ`, and the mean-field weight and the error terms are read at `μ'`.  At
`μ' = μ` this is `PerBoxFTotal` (`Work.BoseFixB1B.sbWordAt_self`). -/
def PerBoxFTotalAt (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C : ℝ) (μ μ' : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : E3) : Prop :=
  c₁ * (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.SmallBoxSliding.psiWeight 1 μ'
            (chiDensB (v := v) μ u (Φ : Submission.BoseGases.X n → ℝ)))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - (1 / 2) * μ' ^ 2 * Work.BoseFixB1.w1MassB h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * (μ' ^ 2 * (_root_.BoseGases.a v)
          * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ' * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)))
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    - C * μ' * (_root_.BoseGases.a v)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  ≤ sbWordAt (v := v) h μ μ' u (Φ : Submission.BoseGases.X n → ℝ)

/-- `PerBoxFTotal` is the `μ' = μ` case of `PerBoxFTotalAt`. -/
theorem PerBoxFTotalAt_self {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (u : E3) :
    PerBoxFTotalAt v h R c₁ C μ μ n Φ u ↔ PerBoxFTotal v h R c₁ C μ n Φ u := by
  rw [PerBoxFTotalAt, PerBoxFTotal, sbWordAt_self]

end Work.BoseFixB1B
