import ChallengeDeps
import Submission.Work.BoseBox.Windows
import Submission.Work.BoseBox.cnPlus_le_of_spectralNPlusLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `Work.BoseBox.q3WindowDef` — the a-priori **particle window** of the `3Q` node

This module holds *only* the definition of the residual that the `3Q` node
`Work.BoseBox.NodeB3` (`= Work.BoseBox.q3Splitting`) consumes, so that the
sibling modules

* `Submission.Work.BoseBox.q3NodeAssembly` (the *proof* of `NodeB3` from the window), and
* `Submission.Work.BoseBox.q3WindowOfNodeB1` (the *proof* of the window from the corpus's
  a-priori node `NodeB1`),

can both import it without a cycle.  Nothing here is a proof: the definition is the *named gap*.

## Where the gap sits in the corpus's B1/B3 architecture

* `Work.BoseBox.NodeB3 v h J` (FS §7–§8 `lem:Q3-splitting1`, in the §6-restricted class) follows
  from `Q3ParticleWindow v h J` — **proved**, `q3NodeAssembly`;
* `Q3ParticleWindow v h J` follows from the corpus's a-priori node `Work.BoseBox.NodeB1 v h J`
  (FS §5 `thm:aprioribounds`, first conjunct) — **proved**,
  `q3WindowOfNodeB1`;
* `NodeB1 v h J` follows from the corpus's named analytic core
  `Work.BoseBox.AprioriCore v h` — **proved**, `Work.BoseBox.aprioriCore_nodeB1`
  (`Submission/Work/BoseBox/aprioriCore_nodeB1.lean`), and `AprioriCore` is bounded below by the
  FS §5 / Appendix `SmallBoxes` analysis (the workspace's remaining open chapter, see
  `Submission/Work/SmallBoxDesignNote.md`).

So the *only* unproved input of `Work.BoseBox.q3Splitting` is the a-priori particle window
(FS `eq:apriorinn+`, first conjunct) at FS's *decoupled* parameters; the `3Q`-splitting content
itself is proved. -/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Metric Filter

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 0. The degenerate case `a v = 0` is vacuous

`paramsAt μ 0 = fsParams 0`, `μ·0³ = 0`, and `ParamsOK (fsParams 0) 0` is false: `con:sKell`
would give `1 ≤ (fsParams 0).s · (fsParams 0).Kl · 0^ε = 0`. -/

lemma not_paramsOK_fsParams_zero : ¬ ParamsOK (fsParams 0) 0 := by
  intro hP
  have hs : (fsParams 0).s = 0 := by
    show fsXp (0:ℝ) (1:ℝ) = 0
    rw [fsXp]
    exact Real.zero_rpow (by norm_num)
  have hKl : (fsParams 0).Kl = 0 := by
    show fsXp (0:ℝ) (-(3 / 2 : ℝ)) = 0
    rw [fsXp]
    exact Real.zero_rpow (by norm_num)
  obtain ⟨ε, hε, -, hle⟩ := hP.sKell
  have hzero : (fsParams 0).s * (fsParams 0).Kl * (0:ℝ) ^ ε = 0 := by
    rw [hs, hKl, zero_mul, zero_mul]
  rw [hzero] at hle
  exact absurd hle (by norm_num)

/-! ## 1. The gap, named -/

/-- **FS §5 `thm:aprioribounds`, first conjunct, qualitative form** (the particle window the
assembly of `NodeB3` consumes): a *low* state whose excited count is bounded by the matrix window
`𝓜 = bigM (paramsAt μ (a v)) (a v) μ` has at most `Cw(μℓ³ + 𝓜 + 1)` particles.

FS prove this from the small-box sliding localisation (`thm:aprioribounds`, Appendix
`SmallBoxes`, Bratteli–Solovej Thm 3.10).  In this workspace the chain is
`AprioriCore v h → NodeB1 v h J` (`aprioriCore_nodeB1`, proved) and
`NodeB1 v h J → Q3ParticleWindow v h J` (`q3WindowOfNodeB1`, proved); the remaining analysis is
the a-priori chapter (FS §5 + Appendix), whose localisation side is largely in place:
`Work.BoseKinLoc.Kinetic.kinetic_localisation` (FS `lem:LocKinEn`, proved),
`Work.BoseKinLoc.Pot.pot_average` (FS `lem:LocPotential`, proved) and the sharp window-conditional
per-box bound `Work.SmallBoxBlockBound.smallbox_block_bound`.

The mean-field shortcut is *false* — see the counterexample in the module docstring of
`Submission/Work/BoseBox/q3Splitting.lean`. -/
def Q3ParticleWindow (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ) : Prop :=
  ∃ Cw ε₀ : ℝ, 0 ≤ Cw ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ bigM (paramsAt μ (a v)) (a v) μ * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) →
        (n : ℝ) ≤ Cw * (μ * sideAt μ (a v) ^ 3 + bigM (paramsAt μ (a v)) (a v) μ + 1)

end Work.BoseBox
