/-
# `Work.CoreResiduals` — the CORE RESIDUALS of the `fts` formalisation

This is the area of the `fts` project (Elgindi, *Finite-time singularity formation for
`C^{1,α}` solutions to the incompressible Euler equations on `ℝ³`*, Annals of Math. **194**
(2021) 771--887) that owns the **four named analytic statements** of the delivered
`CoreResiduals` interface (`Submission/Work/ConstructionInstance/NOTES.md` §3.3--§3.6):

| residual | name here | statement | owner chapter |
|---|---|---|---|
| **R1** | `VortEq α P` | the `ℝ³` vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u` for `u = BS ω`, `ω = solVort P` | `Work.Stability` (through the `Cyl` dictionary) |
| **R2** | `LGClass α P` | the *spacetime* Lichtenstein–Gunther class of `BS(ω(·,t))` on the strips (`= Work.LWP.SpaceTimeHolder`) | `Work.LWP` |
| **R3** | `VortSmooth P` | `C¹` of the ansatz velocity `BS(ω(·,t))` on the two-sided window | `Work.Construction` |
| **R4** | `TimeHolderDeriv P` | the time-Hölder regularity of `∂ₜω` on the strips (finding H) | the `St1`/`St3` second-order estimate |

with the *inhabitant* `profileData_inhabited` (`g = 0`, `T = 2`, `λ̄(t) = 1-t/2`,
`L = 4^{1/p}+1`, `R = 2L`, `M = 20p`, `M₁ = 10p`).

## What this area delivers

* `Defs.lean` (this file) — the vocabulary: the four residual `Prop`s at a `ProfileData`, the
  **model data** predicate `IsModelData` and the four *model* statements
  `VortEqModel`/`LGClassModel`/`VortSmoothModel`/`TimeHolderDerivModel`, and the precisely named
  **analytic inputs** that stand between the delivered chapters and the residuals
  (`BiotSavartC1`, `BiotSavartSpaceTime`, `SwirlEllipticInverse`, `SelfSimProfileEquation`).
* `Model.lean` — the inhabitant and its concrete properties; the **rate rigidity** of the
  self-similar profile (`dynEqConst_rate_rigid`, `fstar_rate_rigid`), a *proved* obstruction
  showing that the delivered inhabitant is not consistent with residual R1.
* `BiotSavart.lean` — the genuine new mathematics on the Biot–Savart operator that is within
  reach (linearity, the far-field `C¹` statement, domination).
* `Reductions.lean` — the exact routing: each of R1–R4 from its owner chapter's input.
* `TimeHolderDeriv.lean` — R4 at the model data, proved.
* `Check.lean` — the end-to-end check: `CoreResiduals α P` → `ConstructedSolutionFixed α` →
  the challenge statement, plus the model-data consistency certificates.
* `NOTES.md` — the routing, the findings and the roadmap.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Maximality
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.ConstructionInstance.selfSimTimeHolderDeriv_profileData_inhabited
import Submission.Work.ConstructionInstance.exists_psiField_eq_biotSavart
import Submission.Work.Stability.Defs
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-- `ℝ³`, definitionally `Work.Cyl.R3`, `Work.LWP.R3` and `Work.ConstructionInstance.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The four residual statements, in their owner chapters' vocabulary -/

/-- **R1 — the `ℝ³` vorticity equation for `u = BS ω`.**  For the constructed (cut) vorticity
`ω = solVort P` and the reconstructed velocity `u(x,t) = BS(ω(·,t)) x`,
`∂ₜω + (u·∇)ω = (ω·∇)u` pointwise.  This is `Work.Stability`'s `St0`--`St3` bootstrap, whose
profile-level form is `Work.Stability.DynEq`/`SelfSimEulerS`. -/
abbrev VortEq (α : NNReal) (P : Work.ConstructionInstance.ProfileData α) : Prop :=
  Work.ConstructionInstance.SelfSimVorticityEquation α P

/-- **R2 — the spacetime Lichtenstein–Gunther class of `BS(ω(·,t))`** on every strip
`[0,S]`, `S < T`.  This *is* `Work.LWP.SpaceTimeHolder` (`Iff.rfl` in `Tie`). -/
abbrev LGClass (α : NNReal) (P : Work.ConstructionInstance.ProfileData α) : Prop :=
  Work.ConstructionInstance.SelfSimLGClass α P

/-- **R3 — `C¹` of the ansatz velocity on the two-sided window** `Ioo (-2) T`. -/
abbrev VortSmooth {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : Prop :=
  Work.ConstructionInstance.SelfSimVortSmooth P

/-- **R4 — the time-Hölder regularity of `∂ₜω` on the strips** (finding H of the delivered
`NOTES.md`), equivalently a strip bound on `∂ₜ²ω` (`selfSimTimeHolderDeriv_of_secondOrderData`). -/
abbrev TimeHolderDeriv {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : Prop :=
  Work.ConstructionInstance.SelfSimTimeHolderDeriv P

/-- The delivered **minimal residual interface** `Work.ConstructionInstance.CoreResiduals`. -/
abbrev Residuals (α : NNReal) (P : Work.ConstructionInstance.ProfileData α) :=
  Work.ConstructionInstance.CoreResiduals α P

/-- The candidate solution `u(x,t) = BS(solVort P · t) x` of the ansatz. -/
abbrev ansatzV {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : R3 → ℝ → R3 :=
  Work.ConstructionInstance.ansatzV P

/-- The constructed (cut) self-similar vorticity of the profile data. -/
abbrev solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : R3 → ℝ → R3 :=
  Work.ConstructionInstance.solVort P

/-- The ansatz velocity is the Biot–Savart field of the constructed vorticity, by definition. -/
theorem ansatzV_apply {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) (x : R3)
    (t : ℝ) : ansatzV P x t = Work.LWP.biotSavart (fun y => solVort P y t) x := rfl

/-! ## The model data -/

/-- **The data of the delivered inhabitant** (`profileData_inhabited`): the perturbation `g = 0`,
the blow-up time `T = 2`, the affine modulation `λ̄(t) = 1 - t/2`, the cut-off parameter
`L = 4^{1/p}+1` with `p = profExp α = 3α`, the support radius `R = 2L` and the two boxes
`M = 20p`, `M₁ = 10p`. -/
def IsModelData {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : Prop :=
  P.T = 2 ∧ P.g = (fun _ _ => (0 : ℝ)) ∧ P.lam = (fun t : ℝ => 1 - t / 2) ∧
    P.L = (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1 ∧
      P.M = 20 * Work.ConstructionInstance.profExp α ∧
        P.M₁ = 10 * Work.ConstructionInstance.profExp α

/-! ## The four statements *at the model data* -/

/-- **R1 at the model data**: the explicit cut self-similar field with `g = 0`, `T = 2`,
`λ̄(t) = 1-t/2` solves the `ℝ³` vorticity equation against its own Biot–Savart velocity. -/
def VortEqModel (α : NNReal) : Prop :=
  ∃ P : Work.ConstructionInstance.ProfileData α, IsModelData P ∧ VortEq α P

/-- **R2 at the model data.** -/
def LGClassModel (α : NNReal) : Prop :=
  ∃ P : Work.ConstructionInstance.ProfileData α, IsModelData P ∧ LGClass α P

/-- **R3 at the model data.** -/
def VortSmoothModel (α : NNReal) : Prop :=
  ∃ P : Work.ConstructionInstance.ProfileData α, IsModelData P ∧ VortSmooth P

/-- **R4 at the model data.** -/
def TimeHolderDerivModel (α : NNReal) : Prop :=
  ∃ P : Work.ConstructionInstance.ProfileData α, IsModelData P ∧ TimeHolderDeriv P

/-! ## The precisely named analytic inputs

Each of the following is a statement about a *different object* from the residual it produces
(a general vorticity field), so that the reduction `input → residual` is a genuine proof and not
a restatement.  They are the **precise residual** of this area: the analytic content of R2 and R3
that no delivered lemma provides yet.  `NOTES.md` records what the proof of each requires. -/

/-- **The admissibility bundle of the `C¹` statement (R3).**  A spacetime vorticity that is
supported in a fixed ball and, near every time in the half-window `preWindow T`,
locally bounded, locally Hölder in `x`, ae-strongly-measurable, differentiable in `t` with
locally bounded derivative and measurable derivative slices.

Every clause is imposed only *near* the times of the half-window `preWindow T` (where `λ̄` is
positive and locally bounded away from `0`) — measurability included: `ProfileData` constrains
neither `λ̄` nor the profile `g` outside that window, so a global measurability clause would be
unprovable; for the model data the bundle is supplied by
`BiotSavart.solVort_BSAdmissibleOnWindow`: the support is `solVort_supp`, the local boundedness is
`solVort_bdd` together with the continuity of `λ̄`, the local `x`-Hölder regularity is
`solVort_holder`, the `t`-differentiability is `hasDerivAt_selfSimVort_slice`, and the
`∂ₜ`-bound is `bddDt_selfSimVort`. -/
def BSAdmissibleOnWindow (ω : R3 → ℝ → R3) (R T : ℝ) : Prop :=
  0 < R ∧
    (∀ t : ℝ, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) ∧
    (∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3, ‖ω y t‖ ≤ M) ∧
    (∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
      ∃ C : ℝ, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ a b : R3,
        ‖ω a t - ω b t‖ ≤ C * ‖a - b‖ ^ c) ∧
    (∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume) ∧
    (∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
        HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t) ∧
    (∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧ ∃ M₁ : ℝ,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
        ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁) ∧
    (∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), MeasureTheory.AEStronglyMeasurable
        (fun y : R3 => FiniteTimeSingularity.timeDeriv ω y t) MeasureTheory.volume)

/-- **The extra time-regularity needed for the *joint* statement** (R3): the slices of `∂ₜω` are
locally Lipschitz in `t`, uniformly in `x`.  This is a *second-order* condition in time — the same
object as R4 (`TimeHolderDeriv`, the time-Hölder regularity of `∂ₜω`): for the explicit
self-similar field the second time derivative is the explicit field
`Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort`, whose bound on a strip gives this
Lipschitzness by the mean value theorem.

It is *needed*: without it the joint `C¹` statement is false — for
`ω(y,t) = ψ(y)·G(t)` with `ψ` a smooth bump and `G' = sin(1/·)` (bounded, Darboux, discontinuous
at `0`) every clause of `BSAdmissibleOnWindow` holds, yet the `t`-partial of
`F(x,t) = G(t)·BS ψ(x)` is `G'(t)·BS ψ(x)`, which is discontinuous in `t` wherever `BS ψ ≠ 0`. -/
def TimeDerivLocallyLipschitz (ω : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t₀ ∈ Work.ConstructionInstance.preWindow T, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
    ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ t' ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
      ‖FiniteTimeSingularity.timeDeriv ω y t - FiniteTimeSingularity.timeDeriv ω y t'‖
        ≤ N * |t - t'|

/-- **The missing chapter: joint `C¹` regularity of the Biot–Savart reconstruction** (R3's
analytic core).  For any admissible spacetime vorticity (`BSAdmissibleOnWindow`) whose `∂ₜ`-slices
are locally Lipschitz in `t` (`TimeDerivLocallyLipschitz`), the reconstructed velocity
`(x,t) ↦ BS(ω(·,t))(x)` is `C¹` (indeed `C^{1,c}` for the Hölder exponent `c` of the bundle)
everywhere.

This is *not* in Mathlib and not in the workspace: the delivered `Work.LWP.BiotSavartSchauder` is
a *per-slice*, non-quantitative statement, and the `x`-differentiability of the Biot–Savart
integral inside the support of `ω` needs the Calderón–Zygmund cancellation
(`biotSavart_centered` + `constant_vec_integral_ball_bsK_eq_zero` give the odd-kernel
reformulation; the differentiated integrand is then dominated by `C‖x-y‖^{c-3}`, integrable for
`c > 0`).  `BiotSavart.lean` proves the far-field half (`biotSavart_contDiffOn_far`). -/
def BiotSavartSpacetimeC1 : Prop :=
  ∀ (ω : R3 → ℝ → R3) (R T : ℝ), BSAdmissibleOnWindow ω R T →
    TimeDerivLocallyLipschitz ω T →
      ∀ x₀ : R3, ∀ t₀ ∈ Work.ConstructionInstance.preWindow T,
        ContDiffAt ℝ 1 (fun q : R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) (x₀, t₀)

/-- **The admissibility bundle of the Schauder statement (R2)**: a spacetime vorticity supported
in a fixed ball, uniformly bounded, uniformly `x`-Hölder and time-Hölder on the strip `[0,S]`,
with ae-strongly-measurable slices.

For the model data this bundle is supplied by `BiotSavart.solVort_BSAdmissibleStrip`
(`solVort_supp`, `solVort_bdd`, `solVort_holder_strip`, `solVort_timeHolder`). -/
def BSAdmissibleStrip (α : NNReal) (ω : R3 → ℝ → R3) (R S : ℝ) : Prop :=
  0 < R ∧
    (∀ t ∈ Set.Icc (0 : ℝ) S, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) ∧
    (∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ y : R3, ‖ω y t‖ ≤ M) ∧
    (∃ H : NNReal, ∀ t ∈ Set.Icc (0 : ℝ) S, HolderWith H α (ω · t)) ∧
    (∃ N : ℝ, ∀ y : R3, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S,
      ‖ω y t - ω y t'‖ ≤ N * |t - t'| ^ (α : ℝ)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) S,
      MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)

/-- **The time-regularity of an admissible strip vorticity** (the `t`-part of the hypothesis
bundle of the space-time Schauder estimate): the slices are differentiable in `t` on the strip, with
a uniformly bounded derivative whose slices are ae-strongly-measurable.  It is *needed*: the strip
`ℝ³ × [0,S]` is full-dimensional, so `ContDiffOn ℝ 1` on it already forces `t`-differentiability,
and `ω(y,t) = φ(y)·|t-1/2|` satisfies every clause of `BSAdmissibleStrip` without it. -/
def TimeDerivStrip (ω : R3 → ℝ → R3) (S : ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) S, ∀ y : R3,
    HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t) ∧
  (∃ M₁ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ y : R3,
    ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) S, MeasureTheory.AEStronglyMeasurable
    (fun y : R3 => FiniteTimeSingularity.timeDeriv ω y t) MeasureTheory.volume)

/-- **The second-order time-regularity of the strip bundle** (R2): the `∂ₜ`-slices are Hölder in
`t` of exponent `α`, uniformly in `x`, on the strip.  It is *needed*: `IsContDiffHolderOn ℝ α` on
the full-dimensional strip already forces the `t`-Hölder continuity of the `t`-partial
`BS(∂ₜω(·,t))(x)` uniformly in `x`, which nothing below `∂ₜω` can supply (the time-Hölder of `ω`
controls only the primitive of `∂ₜω`).

For the model data this is exactly residual **R4** in its strip form: `TimeHolderDeriv P` is
`TimeHolderOnBall α (∂ₜ (solVort P)) P.R S H₁` on `window S ⊇ Icc 0 S`, i.e. this clause on the
support ball, and it extends to all `x` because `∂ₜω` vanishes off the ball. -/
def TimeDerivStripHolder (α : NNReal) (ω : R3 → ℝ → R3) (S : ℝ) : Prop :=
  ∃ N₁ : ℝ, ∀ y : R3, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S,
    ‖FiniteTimeSingularity.timeDeriv ω y t - FiniteTimeSingularity.timeDeriv ω y t'‖
      ≤ N₁ * |t - t'| ^ (α : ℝ)

/-- The **full** hypothesis bundle of the space-time Schauder estimate: the strip admissibility of
the vorticity, the time-regularity of its slices, and the second-order time-regularity of `∂ₜω`. -/
def BSAdmissibleStripFull (α : NNReal) (ω : R3 → ℝ → R3) (R S : ℝ) : Prop :=
  BSAdmissibleStrip α ω R S ∧ TimeDerivStrip ω S ∧ TimeDerivStripHolder α ω S

/-- **The missing chapter: the spacetime Schauder estimate for the Biot–Savart operator**
(R2's analytic core).  For `0 < α < 1` and any fully admissible strip vorticity, the reconstructed
velocity is jointly `C^{1,α}` on `ℝ³ × [0,S]` — i.e. `Work.LWP.SpaceTimeHolder` at the concrete
field.

The per-slice Schauder input `Work.LWP.BiotSavartSchauder` is **not** enough: it carries no
uniformity in `t`, so it cannot produce the joint regularity (the whole point of the `St4`
far-field step).  The direct proof is the classical Schauder estimate in space-time (the
Calderón–Zygmund operator `ω ↦ (BS ω, ∇BS ω)` is bounded on the joint Hölder space
`C^{0,α}(ℝ³ × [0,S])` for `0 < α < 1`), which needs the same odd-kernel cancellation as
`BiotSavartSpacetimeC1`, plus the *quantitative* (uniform-in-slice) form of the estimate.

The hypotheses `0 < S` and `0 < α < 1` are both *necessary*: at `S = 0` the strip
`ℝ³ × {0}` is thin, so `fderivWithin` is opaque and the conclusion is not implied by the bundle.
The range `0 < α < 1` is the correct one: at `α = 0` the hypotheses reduce to boundedness, where the
estimate is false, and at the endpoint `α = 1` it is false too (an order-`0` Calderón–Zygmund
operator maps Lipschitz functions into the Zygmund class, not into Lipschitz: for
`ω₀(y) = (y₁²y₃/|y|²·χ(y), 0, 0)` — a Lipschitz, compactly supported, time-independent vorticity —
`∇BS ω₀` is not Lipschitz).  The challenge's exponent satisfies `α ≤ 1/3`
(`ProfileData.hα13`), so the range is not a restriction in the application. -/
def BiotSavartSpaceTime (α : NNReal) : Prop :=
  0 < (α : ℝ) ∧ (α : ℝ) < 1 ∧
    ∀ (ω : R3 → ℝ → R3) (R S : ℝ), 0 < S → BSAdmissibleStripFull α ω R S →
      IsContDiffHolderOn ℝ α (fun q : R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
        (Set.univ ×ˢ Set.Icc 0 S)

/-- **The corrected form of R1, with the cut-off deficit carried explicitly.**

The constructed vorticity `solVort P` of the delivered interface is the **cut** field
`χ(ρ/L)·λ̄^{-1}F(ρ^p/λ̄,θ)·e_θ` (finding F of the delivered `NOTES.md`: the cut-off is forced by
the support box `hSupp`).  The cut-off is *not* transparent — `χ = 1` only on `[-1,1]` — so the
cut field is **not** expected to solve the Euler vorticity equation with its own Biot–Savart
velocity: the deficit is exactly the far-field term `Work.Stability.Far` of the `St2`
`g`-equation (`Work.Stability.GEquationFar`).

This is therefore the honest form of R1: the equation holds *with* the deficit `Def`, and the
delivered residual is the case `Def = 0`.  The honest construction's modulation `g` is chosen so
as to cancel the deficit; for the model data (`g = 0`) it cannot be cancelled
(`Model.fstar_rate_rigid` exhibits the rate obstruction). -/
def VortEqWithDeficit {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (Def : R3 → ℝ → R3) : Prop :=
  ∀ x : R3, ∀ t : ℝ,
    FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) x t
      + FiniteTimeSingularity.directionalDeriv (Work.ConstructionInstance.solVort P)
          (fun x t => Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t) x) x t
      = FiniteTimeSingularity.directionalDeriv
          (fun x t => Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t) x)
          (Work.ConstructionInstance.solVort P) x t + Def x t

/-- The delivered residual R1 is the zero-deficit case of `VortEqWithDeficit`. -/
theorem vortEq_iff_noDeficit {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    VortEq α P ↔ VortEqWithDeficit P (fun x t => 0) := by
  simp only [VortEq, VortEqWithDeficit, Work.ConstructionInstance.SelfSimVorticityEquation,
    Work.LWP.VorticityEquation, Pi.zero_apply, add_zero]

end Work.CoreResiduals
