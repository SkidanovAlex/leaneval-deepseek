/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsStructP.lean` — the regularity classes of the `P₀`-scheme

`EpsODE.lean` defines the datum/regularity classes of the *as-stated* (un-projected) `ε`-scheme:

  `EpsDatum α ρ ε h := SmoothOpen h ∧ HkMem α 6 h ∧ ClassC α (J_ε h)`,
  `EpsReg α ρ ε T g   := C¹` of `(z,θ,τ) ↦ g z θ τ` `∧ ∀ τ ∈ [0,T], EpsDatum α ρ ε (slice g τ)`,
  `EpsAprioriBddH …  := ` the sub-horizon a-priori `ℋ⁶`-bound for regular `ε`-solutions.

The third conjunct of `EpsDatum` is **false** along the scheme (`NOTES_Pzero.md` §1: `J_ε` is a
two-dimensional log-coordinate convolution and the angular weight of `L₁₂` is not
shift-invariant), which is why a prover refuted the local-existence statement E2a as written and
why `PZeroScheme.lean` records the corrected scheme `IsEpsSolP`.  This module records the
corresponding datum classes for the corrected scheme: the only change is that the class-`C`
conjunct is now about the **projected** mollified profile `P₀ (J_ε h)`, for which the `l12` clause
`L₁₂ · 0 = 0` is *true by construction* (`PZeroAux.Pz_l12`).

Nothing here is analytic: the module only fixes vocabulary.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.EllSol.ClassC

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

/-- **The regularity class of the `P₀`-scheme's data**: `C^∞` on the open quadrant, honest `ℋ⁶`,
and *the projected mollified profile in class C* — the conjunct that the `P₀` repair makes true. -/
def EpsDatumP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (h : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen h ∧ Work.Spaces.HkMem α 6 h ∧
    Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε h))

/-- The un-projected datum data imply nothing by themselves about the projection; the point of
`EpsDatumP` is exactly that its class-`C` conjunct is the *projected* one.  This lemma records the
trivial implication `EpsDatumP ⟹ SmoothOpen ∧ HkMem α 6`, which is all that the E1/E3 bounds
consume from the datum. -/
theorem EpsDatumP.soft {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {h : Fn} (hd : EpsDatumP α ρ ε h) :
    Work.FTS.EllipticEst.SmoothOpen h ∧ Work.Spaces.HkMem α 6 h := ⟨hd.1, hd.2.1⟩

/-- **The regularity class of `P₀`-solutions on `[0,T]`**: joint `C¹` in `(z,θ,τ)` on the open
quadrant up to the endpoints, and every slice in `EpsDatumP` (what the corrected E2a outputs, what
restarts need, and what E3's energy identity consumes). -/
def EpsRegP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (g : Fam) : Prop :=
  ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
    ∀ τ ∈ Set.Icc 0 T, EpsDatumP α ρ ε (slice g τ)

/-- **The sub-horizon a-priori bound for the `P₀`-scheme** (the analogue of `EpsAprioriBddH`):
every *regular* `P₀`-solution on any `[0,T']`, `T' ≤ T`, keeps its `ℋ⁶`-size `≤ M`. -/
def EpsAprioriBddHP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (M : ℝ) : Prop :=
  ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g → EpsRegP α ρ ε T' g →
    ∀ τ ∈ Set.Icc 0 T', Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ M

/-- `EpsRegP` is monotone in the horizon. -/
theorem EpsRegP.mono {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T T' : ℝ} {g : Fam}
    (h : EpsRegP α ρ ε T' g) (hTT' : T ≤ T') : EpsRegP α ρ ε T g :=
  ⟨h.1.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans hTT'⟩,
    fun τ hτ => h.2 τ ⟨hτ.1, hτ.2.trans hTT'⟩⟩

/-- `EpsRegP` at `τ = 0` gives the datum of the initial value. -/
theorem EpsRegP.datum_zero {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {g : Fam}
    (h : EpsRegP α ρ ε T g) (hT : 0 ≤ T) : EpsDatumP α ρ ε (slice g 0) :=
  h.2 0 ⟨le_rfl, hT⟩

end Work.FTS.StrongEps
