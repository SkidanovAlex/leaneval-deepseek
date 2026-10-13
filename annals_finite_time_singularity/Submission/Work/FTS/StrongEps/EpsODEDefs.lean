/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsODEDefs.lean` — the *vocabulary* of the un-projected
# `ε`-scheme, split out of `EpsODE.lean`

`EpsODE.lean` holds the design's statements **E2/E4 for the (superseded) un-projected scheme**
together with the datum classes of that scheme.  Both of its two theorems are *records of false or
superseded statements* and carry a live `sorry`:

* `IsEpsSol.local` — the un-projected E2a; **refuted** (`EpsLocalPStar/StatResidual.lean`: the
  scheme's right-hand side is minus the paper's stationary residual, so the `axis` clause cannot be
  preserved); superseded by the projected small-ball local step `EpsE4Thr.LocalStepP` /
  `E4R3.LocalStepChapter3`.
* `EpsUniform_of_data` — the un-projected E4; **false** for `C₀ < 1/√2`
  (`EpsE4Work.Certificate.epsUniformMem_Jeps_bound`) and superseded by `StrongEps.EpsE4R`.

The *definitions*, however, are used all over the tree (and in particular by `EpsE4R`, which is on
the `theorem_1_v2` wire), so leaving them in a module that carries two `sorry`s put those `sorry`s
into the wire's import cone for no gain.  This module therefore carries the three definitions alone;
`EpsODE.lean` imports it and keeps the two records.  A consumer that needs only the definitions
should import **this** module.

*Convention.*  As in `EpsStructP.lean`, `EpsDatum`/`EpsReg` are the classes of the *un-projected*
scheme; the classes of the projected scheme are `EpsDatumP`/`EpsRegP`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.StrongEps.EpsLimitDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The regularity class of the `ε`-scheme's data** (ruling v2, D4): `C^∞` on the open quadrant,
honest `ℋ⁶`, and the mollified profile in class C (so that `hEll`, `L6Ctx` and E3 apply to it). -/
def EpsDatum (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (h : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen h ∧ Work.Spaces.HkMem α 6 h ∧
    Work.FTS.ClassC.ClassC α (Jeps ρ ε h)

/-- **The regularity class of `ε`-solutions on `[0,T]`**: joint `C¹` in `(z,θ,τ)` on the open
quadrant up to the endpoints, and every slice in `EpsDatum` (what E2a outputs, what restarts need,
and what E3's energy identity consumes). -/
def EpsReg (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (g : Fam) : Prop :=
  ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
    ∀ τ ∈ Set.Icc 0 T, EpsDatum α ρ ε (slice g τ)

/-- **The sub-horizon a-priori bound** (replaces `EpsAprioriBdd`, which only spoke of solutions
on the full `[0,T]` and was therefore vacuous when none exists): every *regular* `ε`-solution on
any `[0,T']`, `T' ≤ T`, keeps its `ℋ⁶`-size `≤ M`. -/
def EpsAprioriBddH (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (M : ℝ) : Prop :=
  ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSol α ρ ε T' Φs E g₀ g → EpsReg α ρ ε T' g →
    ∀ τ ∈ Set.Icc 0 T', Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ M

end Work.FTS.StrongEps
