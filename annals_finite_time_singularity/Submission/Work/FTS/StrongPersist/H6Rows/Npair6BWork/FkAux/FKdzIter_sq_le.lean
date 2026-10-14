import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.H5.Atoms.SinSqSlot5
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.Defs
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.CoreResiduals.Defs =====
section

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


/-- The candidate solution `u(x,t) = BS(solVort P · t) x` of the ansatz. -/
abbrev ansatzV {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : R3 → ℝ → R3 :=
  Work.ConstructionInstance.ansatzV P

/-- The constructed (cut) self-similar vorticity of the profile data. -/
abbrev solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : R3 → ℝ → R3 :=
  Work.ConstructionInstance.solVort P


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


end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.AprioriOpen.Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **`GalClass` refines `CoerAdm`**: the profiles of the Galerkin span are admissible for the
coercivity estimates (only the order drops from `6` to `5`). -/
theorem coerAdm_of_galClass {α : ℝ} {g : Fn} (h : GalClass α g) : CoerAdm α g :=
  ⟨regQ_mono (k := 6) (by norm_num) h.reg, h.vanish, h.axis, h.l12⟩


/-- The a-priori level `Y = clo·C₀²·α⁴` is the square of the a-priori radius
`√clo·C₀·α²`. -/
theorem Rstar_sq {clo C₀ α : ℝ} (hclo : 0 ≤ clo) (hC₀ : 0 ≤ C₀) :
    (Real.sqrt clo * C₀ * α ^ 2) ^ 2 = clo * C₀ ^ 2 * α ^ 4 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hclo]
  ring

/-- **`hInit`** (design §4 L-N5.6): the projected datum lies in the a-priori ball
`R = √clo·C₀·α²`.  The proof is Bessel's inequality `bessel_galBasis` plus Cauchy–Schwarz for the
inner product and the smallness `|g₀|_{ℋ⁴} ≤ α²`. -/
theorem hInit (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) {g₀ : Fn}
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2) {φ : ℕ → Fn} (hφ : GalBasis α IP φ) :
    ∀ n, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2
      ≤ (Real.sqrt clo * C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
  have hcc := hIP.pos.2.1
  have hclo := hIP.pos.2.2.1
  have hCup := hIP.pos.2.2.2.1
  have hCcs := hIP.pos.2.2.2.2
  have hαpos : 0 < α := hα.1
  have hC₀ : 0 < C0 CcN cc clo Cup Ccs := C0_pos' hclo hCcs
  have hkey : Ccs < clo * C0 CcN cc clo Cup Ccs ^ 2 :=
    Ccs_lt_lower (CcN := CcN) hcc hclo hCup hCcs
  intro n
  have hb := bessel_galBasis hIP hα hφ hRegQ n
  have hcs := hIP.cs α hα g₀ g₀ hRegQ hRegQ
  have hIPle : IP α g₀ g₀ ≤ Ccs * α ^ 4 := by
    have h1 : IP α g₀ g₀ ≤ |IP α g₀ g₀| := le_abs_self _
    have h2 : Ccs * Xn α g₀ * Xn α g₀ ≤ Ccs * (α ^ 2 * α ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hXn hXn (Work.Spaces.HkNorm_nonneg α 4 g₀)
          (le_of_lt (pow_pos hαpos 2))) hCcs.le
    have h3 : Ccs * (α ^ 2 * α ^ 2) = Ccs * α ^ 4 := by ring
    linarith [h1, hcs, h2, h3]
  refine le_trans hb (le_trans hIPle ?_)
  rw [Rstar_sq hclo.le hC₀.le]
  exact le_of_lt (mul_lt_mul_of_pos_right hkey (pow_pos hαpos 4))




end Work.FTS.OpenPkg.AprioriOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory

/-! ## The weighted angular Cauchy–Schwarz for the angular moment `(F,K)_{L²_θ}`

`FK Y z = ∫_θ Y(z,θ) K(θ) dθ` with `K(θ) = 3 sinθ cos²θ`.  Against the *weighted* slice
energy `∫_θ sin(2θ)^{-η} Y(z,θ)² dθ` (which is what the `ℋ^k` slot energies control) the
correct constant is `4`, since `K(θ) = (3/2) cosθ · sin(2θ)` and
`√(∫_θ K(θ)² sin(2θ)^{η} dθ) ≤ √(∫_θ 3K(θ) dθ) = √3 ≤ 4`.

The proof uses only that `sin(2θ)^{-η} Y²` is integrable on `Iθ`: no measurability is
assumed on `Y` itself.  (When `θ ↦ Y(z,θ)K(θ)` is not a.e. strongly measurable both sides of
the final inequality are handled by the a.e. identities, which hold unconditionally.)
-/

/-- On `Iθ = [0,π/2]`, `sin(2θ) ≥ 0`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `K(θ)² ≤ 3K(θ)` on `Iθ`, since `K = 3 sinθ cos²θ` and `sinθ cos²θ ≤ 1`. -/
private lemma K_sq_le_three_mul_K {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.K θ) ^ 2 ≤ 3 * Work.Spaces.K θ := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc2nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hc2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have huv0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 hc2nn
  have huv1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.sin_le_one θ, hc2, huv0, hc2nn]
  have huvsq : (Real.sin θ * Real.cos θ ^ 2) ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 :=
    by nlinarith [sq_nonneg (Real.sin θ * Real.cos θ ^ 2)]
  rw [Work.Spaces.K]
  nlinarith [huvsq]

/-- `K(θ)² sin(2θ)^η ≤ 3K(θ)` on `Iθ` (`sin(2θ)^η ≤ 1` since `0 < η`). -/
private lemma K_sq_mul_sin_pow_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.K θ) ^ 2 * Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 3 * Work.Spaces.K θ := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have h1 : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hsin0 (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  calc (Work.Spaces.K θ) ^ 2 * Real.sin (2 * θ) ^ Work.Spaces.eta
      ≤ (Work.Spaces.K θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (Work.Spaces.K θ) ^ 2 := mul_one _
    _ ≤ 3 * Work.Spaces.K θ := K_sq_le_three_mul_K hθ

/-- Almost everywhere on `Iθ`, `sin(2θ) > 0` (the vanishing set is `{0, π/2}`). -/
private lemma ae_sin_two_pos_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 < Real.sin (2 * θ) := by
  have h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))),
      0 < Real.sin (2 * θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0:ℝ)) (b := Real.pi / 2))
  rwa [hset] at h

theorem FKAbsLeSqrtEta {z : ℝ} {Y : ℝ → ℝ → ℝ}
    (hY : MeasureTheory.IntegrableOn
      (fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Construction.FK Y z| ≤ 4 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2) := by
  have hηpos : 0 < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  set p : ℝ → ℝ := fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2 with hp
  set q : ℝ → ℝ := fun θ => (Work.Spaces.K θ) ^ 2 * Real.sin (2 * θ) ^ Work.Spaces.eta with hq
  have hp_int : MeasureTheory.Integrable p (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hY
  -- `q` is continuous, hence a.e. strongly measurable
  have hKcont : Continuous Work.Spaces.K := by
    unfold Work.Spaces.K
    exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)
  have hq_cont : Continuous q := by
    rw [hq]
    exact (hKcont.pow 2).mul
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun θ => Or.inr hηpos.le))
  have hq_aesm : AEStronglyMeasurable q (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hq_cont.aestronglyMeasurable
  have hK3_int : MeasureTheory.Integrable (fun θ => 3 * Work.Spaces.K θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.Nonlinear.Pieces.Rl1.n5_integrableOn_K.const_mul 3
  have hqnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] q := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hq]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  have hqle : q ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => 3 * Work.Spaces.K θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hq]
    exact K_sq_mul_sin_pow_le_three hθ
  have hq_int : MeasureTheory.Integrable q (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hK3_int.mono' hq_aesm ?_
    filter_upwards [hqnn, hqle] with θ hnn hle
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn]
  -- `∫_θ q ≤ 3`
  have hq_le3 : (∫ θ in Work.Spaces.Iθ, q θ) ≤ 3 := by
    have h1 : (∫ θ in Work.Spaces.Iθ, q θ) ≤ ∫ θ in Work.Spaces.Iθ, 3 * Work.Spaces.K θ :=
      MeasureTheory.integral_mono_ae hq_int hK3_int hqle
    rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Itheta_K, mul_one] at h1
    linarith
  have hpnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] p := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hp]
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  -- Cauchy–Schwarz against the weight `sin(2θ)^{η}`
  have hcs := Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) hpnn hqnn hp_int hq_int
  -- the pointwise identity `|Y K| = √p √q`
  have hid : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Y z θ * Work.Spaces.K θ| = Real.sqrt (p θ) * Real.sqrt (q θ) := by
    filter_upwards [ae_sin_two_pos_Iθ] with θ hsin
    have hs1 : Real.sqrt (Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        * Real.sqrt (Real.sin (2 * θ) ^ Work.Spaces.eta) = 1 := by
      rw [← Real.sqrt_mul (Real.rpow_nonneg hsin.le _), ← Real.rpow_add hsin,
        show -(Work.Spaces.eta) + Work.Spaces.eta = 0 by ring, Real.rpow_zero, Real.sqrt_one]
    rw [hp, hq, Real.sqrt_mul (Real.rpow_nonneg hsin.le _), Real.sqrt_sq_eq_abs,
      Real.sqrt_mul (sq_nonneg (Work.Spaces.K θ)), Real.sqrt_sq_eq_abs, abs_mul]
    rw [show (Real.sqrt (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) * |Y z θ|)
          * (|Work.Spaces.K θ| * Real.sqrt (Real.sin (2 * θ) ^ Work.Spaces.eta))
        = (Real.sqrt (Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
            * Real.sqrt (Real.sin (2 * θ) ^ Work.Spaces.eta))
          * (|Y z θ| * |Work.Spaces.K θ|) from by ring, hs1, one_mul]
  have hFK_le : |Work.Construction.FK Y z|
      ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (p θ) * Real.sqrt (q θ) := by
    rw [Work.Construction.FK]
    calc |∫ θ in Work.Spaces.Iθ, Y z θ * Work.Spaces.K θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |Y z θ * Work.Spaces.K θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ θ in Work.Spaces.Iθ, Real.sqrt (p θ) * Real.sqrt (q θ) :=
          MeasureTheory.integral_congr_ae hid
  have hsqrtq : Real.sqrt (∫ θ in Work.Spaces.Iθ, q θ) ≤ 4 := by
    have h16 : (∫ θ in Work.Spaces.Iθ, q θ) ≤ 16 := by linarith
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, q θ) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt h16
      _ = 4 := by rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc |Work.Construction.FK Y z|
      ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (p θ) * Real.sqrt (q θ) := hFK_le
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, p θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ, q θ) := hcs
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, p θ) * 4 :=
        mul_le_mul_of_nonneg_left hsqrtq (Real.sqrt_nonneg _)
    _ = 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, p θ) := by ring
    _ = 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2) := by rw [hp]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The unweighted slice of `D_z^b f` and the `H^k`-integrand

The `i = b` summand of `HkIntegrand` is `(D_z^b f · w / sin(2θ)^{η/2})^2`, and on the *open*
quadrant both the radial weight `w z` and the angular factor `sin(2θ)^{-η/2}` are `≥ 1`, so
this summand dominates `(D_z^b f)^2` there.  This is all that is needed to transport the
`H^k`-membership of `f` to integrability of the plain squared slice. -/

/-- On the open quadrant, the `i = b` summand of `HkIntegrand` dominates `(D_z^b f)^2`. -/
private lemma dzIter_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ} (b : ℕ) (hb : b ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith
  have hW1 : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div (Real.rpow_pos_of_pos hsinpos _)]
    exact le_trans (Real.rpow_le_one hsinpos.le hsinle (by norm_num [Work.Spaces.eta])) hw1
  have hWsq : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    nlinarith [hW1]
  have hsq := Work.Spaces.sq_le_HkIntegrand_z α k f z θ b hb
  calc (Work.Spaces.DzIter b f z θ) ^ 2
      = (Work.Spaces.DzIter b f z θ) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (Work.Spaces.DzIter b f z θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (sq_nonneg _)
    _ = (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := hsq

/-- The angular moment of the `b`-th radial derivative of `f`, bounded by the angular
`L²`-energy of that derivative (`n5_FK_abs_le` with `g := DzIter b f`).  The hypotheses are
exactly what makes the slice `θ ↦ (DzIter b f z θ)^2` integrable on `Iθ` at `z > 0`:
`SmoothOpen f` for the a.e. strong measurability and `HkMem α k f` with `b ≤ k` for the
domination by the `i = b` summand of `HkIntegrand α k f` (which is `≥ (DzIter b f)^2` because
`w z ≥ 1` and `sin(2θ)^(-η/2) ≥ 1` on the open quadrant). -/
theorem FKdzIter_sq_le {α : ℝ} {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {k : ℕ} (hmem : Work.Spaces.HkMem α k f) (b : ℕ) (hb : b ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      ≤ 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 := by
  -- a.e. strong measurability of the angular slice of `D_z^b f`
  have haesm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter b f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
      (hF.DzIter b).continuousOn hz
  -- `Iθ` and the open interval have the same measure, the two endpoints being null
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  -- integrability of the squared slice, dominated by the `H^k`-integrand
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter b f z θ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hmem.1 z (Set.mem_Ici.mpr hz.le)) (haesm.pow 2) ?_
    rw [hcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact dzIter_sq_le_HkIntegrand b hb hz hθ
  -- the `θ`-Cauchy–Schwarz bound for the angular moment
  have hFK := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le
    (g := Work.Spaces.DzIter b f) hz hint haesm
  have hP0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  calc (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      = |Work.Construction.FK (Work.Spaces.DzIter b f) z| ^ 2 := (sq_abs _).symm
    _ ≤ (4 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hFK 2
    _ = 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hP0]
        norm_num

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
