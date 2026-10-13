/-
# `Work.FTS.Top.Defs` — node N0: the blow-up interface `BlowupAt`

This is the vocabulary of node **N0** of the lead's audit (`FTS_AUDIT_LEAD.md` §4) for the paper

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

## What N0 does

The audit replaces the dead `R1G` route and the vacuous interfaces `Work.LWP.LWPInputs`,
`Work.StabilityFar.EulerScalingToUnit` and `Work.StabilityFar.AssemblyInputs` by a single,
honest interface — `BlowupAt α T` — which is exactly "a solution of the incompressible Euler
equation on `ℝ³` of the class of the paper's Theorem 1, blowing up at time `T`".  N0 provides

* `Work.FTS.Top.BlowupAt` — the interface (this file);
* `Work.FTS.Top.blowupAt_one_of_blowupAt` — the *proved* time rescaling `BlowupAt α T → BlowupAt α 1`,
  replacing the vacuous hypothesis `EulerScalingToUnit` (`Rescale/Blowup.lean`);
* `Work.FTS.Top.intervalIntegrable_vortLInf` — the interval-integrability needed by the
  Beale–Kato–Majda comparison (`Integrable.lean`);
* `Work.FTS.Top.theorem_1_of_blowupAt` — the challenge's conclusion from `BlowupAt α 1`
  (`Main.lean`), through `Work.StabilityFar.bkm_divergence_at_one` and
  `Work.LWP.bkm_eq_challenge_integral`.

## Design rules satisfied by `BlowupAt`

The lead's rules for the replacement interfaces are:

1. **"Every interface structure must come with an inhabitation obligation."**
   `BlowupAt` carries *no* inhabitation obligation **and is not required to**: inhabiting it is
   precisely the mathematical content of `theorem_1`, and its clauses are therefore not a hidden
   hypothesis but the theorem's target.  What matters for the rule is the *other* direction, which
   is proved here: `BlowupAt` is **not vacuously false**.  The failure of
   `Work.StabilityFar.AssemblyInputs` (audit §2.3 (V2)) came from a regularity clause imposed on a
   *two-sided* time window `Ioo (-1) (T+1)` that reaches **past** the blow-up time: it gave a
   uniform bound `‖Du‖ ≤ K` on `[0,T)`, contradicting the `c/(T-t)` growth of the vorticity.
   `BlowupAt` has no clause past `T`:
   * `sol : IsLocalEulerEquationSolution … T u` is on the half-open strip `Ico 0 T`
     (this is the fixed challenge vocabulary; `InitIsLocalEulerEquation` in `ChallengeDeps`);
   * `strip S` is imposed only for `S ∈ Ioo 0 T`, i.e. strictly *below* the blow-up time;
   * `odd` and `lower` are imposed on `Ico 0 T`.
   The compactness argument of (V2) is therefore unavailable, and
   `Work.FTS.Top.Integrable.exists_bound_vorticity_Ioc` (in `Integrable/`) records the (true) sharp
   statement that the only time-uniform bound one can extract from `BlowupAt` is on the *closed*
   sub-strips `[0,t]`, `t < T` — where `lower` still forces `vortLInf` to grow like `1/(T-t)`.
   So the interface is satisfiable in the only sense that can be checked before the solution
   exists.
2. **"No interface may assume regularity at or past the blow-up time."**  Satisfied, see above.
3. **"No 'explicit field solves Euler exactly' targets."**  `BlowupAt` mentions no ansatz: `u` and
   `p` are existentially quantified unknowns, and the only equations on them are the Euler
   equation, the structural clauses (`div`, oddness, Hölder class, decay of the datum's vorticity)
   and the blow-up rate.

## The relation to the physical reconstruction (node N8)

Node N8 (`Work.FTS.Physical`) reconstructs the physical pair `(p,u)` from the fake-time solution
and produces the same interface, field for field.  The two structures are definitionally the same
shape; the identification is recorded in `Work.FTS.Top.Bridge`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import ChallengeDeps
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- `ℝ³`, definitionally `Work.LWP.R3`, `Work.StabilityFar.R3`, `Work.Cyl.R3` and
`Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **A finite-time blow-up of the incompressible Euler equation at time `T > 0`.**

This is the audit's `N0` interface: a pair `(p, u)` defined on `ℝ³ × [0,T)` such that

* `(p,u)` solves the incompressible Euler equation (`IsLocalEulerEquationSolution`, the *fixed*
  `ChallengeDeps` structure) with initial datum `u(·,0)`;
* the datum `u(·,0)` is divergence-free, odd, of class `C^{1,α}(ℝ³)`, and its vorticity decays
  like `‖x‖^{-α}` — the four datum clauses of the challenge statement;
* the solution is odd at every time `t ∈ [0,T)`;
* `u.uncurry` is jointly `C^{1,α}` on every strip `ℝ³ × [0,S]` with `S < T` — the strict part of
  the challenge's statement (it includes `∂ₜu`; see the audit §1 and §4-N7);
* the vorticity sup-norm dominates `c/(T-t)` on `[0,T)`, which is the quantitative form of the
  blow-up and the input of the Beale–Kato–Majda divergence.

Nothing is assumed *at* or *past* `T`. -/
structure BlowupAt (α : ℝ≥0) (T : ℝ) where
  /-- the velocity field -/
  u : R3 → ℝ → R3
  /-- the pressure field -/
  p : R3 → ℝ → ℝ
  /-- the blow-up time is positive -/
  hT : 0 < T
  /-- `(p,u)` solves the incompressible Euler equation on `[0,T)` with initial datum `u(·,0)` -/
  sol : IsLocalEulerEquationSolution p (u · 0) T u
  /-- the initial datum is divergence-free -/
  div0 : div (u · 0) = 0
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Set.Ico 0 T, IsOdd (u · t)
  /-- the initial datum is of class `C^{1,α}(ℝ³)` -/
  cdh0 : IsContDiffHolder ℝ α (u · 0)
  /-- the vorticity of the initial datum decays like `‖x‖^{-α}` -/
  decay0 : ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity (u · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)
  /-- joint `C^{1,α}` regularity of `u.uncurry` on every strip `ℝ³ × [0,S]`, `S < T` -/
  strip : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)
  /-- the vorticity sup-norm blows up at least like `c/(T-t)` -/
  lower : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t

namespace BlowupAt

variable {α : ℝ≥0} {T : ℝ}

/-- The datum of a `BlowupAt` is odd: the `t = 0` instance of the oddness clause. -/
theorem odd_zero (B : BlowupAt α T) : IsOdd (B.u · 0) :=
  B.odd 0 ⟨le_rfl, B.hT⟩

/-- **Converse direction of the structuring of the strip clause**: the joint `C^{1,α}`
regularity of `u.uncurry` on every strip `[0,S]`, `S < T`, is exactly the `SpaceTimeHolder`
predicate of the LWP chapter. -/
theorem spaceTimeHolder (B : BlowupAt α T) : Work.LWP.SpaceTimeHolder α B.u T := B.strip

/-- The datum of a `BlowupAt` is Lichtenstein–Günther admissible in the sense of the LWP chapter:
divergence-free, odd, `C^{1,α}`, with `α`-decaying vorticity. -/
theorem toEulerData (B : BlowupAt α T) : Work.LWP.EulerData α (B.u · 0) where
  div_free := B.div0
  odd := B.odd_zero
  contDiffHolder := B.cdh0
  vort_decay := B.decay0

/-- A `BlowupAt` is a member of the Lichtenstein–Günther class of the LWP chapter (Euler solution,
odd at every time, jointly `C^{1,α}` on compact strips). -/
theorem toLGClass (B : BlowupAt α T) : Work.LWP.LGClass α (B.u · 0) T B.p B.u where
  sol := B.sol
  odd := B.odd
  spacetime := B.strip

/-- **The blow-up rate clause, unfolded.**  The `lower` field of `BlowupAt` is literally the
`VortLinfLower` predicate of the stability chapter; the identification is recorded in
`Work.FTS.Top.BlowupAt.vortLinfLower`. -/
theorem lower_at (B : BlowupAt α T) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf B.u t := B.lower

end BlowupAt

end Work.FTS.Top
