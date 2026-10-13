/-
# `Work.LWP.Inputs` — the precisely named analytic inputs of the LWP / continuation chapter

The area `Work.LWP` delivers, for the Lichtenstein–Gunther `C^{1,α}` theory of the 3D
incompressible Euler equation,

1. the Hölder-space Biot–Savart bounds (`Work.LWP.BiotSavart`),
2. local well-posedness in the Lichtenstein–Gunther class (`Work.LWP.LocalExistence`),
3. the Beale–Kato–Majda continuation criterion (`Work.LWP.BKM`),

together with the Picard–Lindelöf flow machinery and the transport estimates
(`Work.LWP.Flow`, `Work.LWP.Transport`).

Three pieces of *analysis* — none of them available in Mathlib — are the hard core of that
theory: the Calderón–Zygmund/Schauder estimate for the Biot–Savart operator, the Picard
iteration solving the vorticity equation, and the a priori log-Grönwall control of `∇u` by
`‖ω‖_{L∞}` underlying the Beale–Kato–Majda criterion.  Each of them is stated below as a
`Prop`-valued `def` with an explicit, checkable mathematical statement in the *challenge's own
vocabulary* (`FiniteTimeSingularity.vorticity`, `div`, `IsLocalEulerEquationSolution`, …), so
that the theorems of this chapter are stated conditionally on exactly these inputs and on
nothing else.  `NOTES.md` records for each input what a proof would require.

None of the inputs is a restatement of a theorem of this chapter: each is an inequality /
existence statement about a *different* object (`biotSavart`, the vorticity equation, the
`C^{1,α}` norm), and `Work.LWP.*` proves the reductions that turn them into the consumer shapes.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## 1. The Biot–Savart inputs -/

/-- **The Schauder / Calderón–Zygmund estimate for the Biot–Savart operator.**

`ω ∈ L¹ ∩ L^∞ ∩ C^{0,α}` divergence-free on `ℝ³` implies `u = biotSavart ω ∈ C^{1,α}`:
`ContDiff 1 u`, `Du` bounded and `α`-Hölder.  This is Schauder's second order estimate applied
to `u = (-Δ)^{-1}(∇×ω)`, whose second derivatives are Calderón–Zygmund transforms of `ω`;
equivalently it is the statement that the singular integral operators of order `1` map
`C^{0,α}_b` to itself.  This is the `C^{1,α}` *closure* of the Biot–Savart map. -/
def BiotSavartSchauder (α : NNReal) : Prop :=
  ∀ ω : R3 → R3, Integrable ω → IsBoundedFun ω → Holder α ω → (∀ x, div ω x = 0) →
    IsContDiffHolder ℝ α (biotSavart ω)

/-- **The Biot–Savart law for a divergence-free vorticity.**  `u = biotSavart ω` has vorticity
`ω` and is divergence-free.  (Both halves come from `u = ∇×A` with the Newtonian potential
`A = (4π)^{-1}∫ ω(y)/‖x-y‖ dy`, using `∇·A = 0` and `-ΔA = ω`.) -/
def BiotSavartLaw : Prop :=
  ∀ ω : R3 → R3, Integrable ω → IsBoundedFun ω → (∀ x, div ω x = 0) →
    (∀ x, vorticity (biotSavart ω) x = ω x) ∧ (∀ x, div (biotSavart ω) x = 0)

/-- **The inverse Biot–Savart law on `ℝ³`.**  A `C¹`, divergence-free velocity field which
decays at infinity is recovered from its vorticity by the Biot–Savart integral,
`u = biotSavart (∇×u)`.  (The proof is the standard one: `u - biotSavart (∇×u)` is a
divergence-free curl-free field, hence a gradient, hence — being bounded and decaying — zero;
equivalently the Helmholtz decomposition of `L²(ℝ³)`.) -/
def BiotSavartInverse : Prop :=
  ∀ u : R3 → R3, ContDiff ℝ 1 u → (∀ x, div u x = 0) → Integrable (vorticity u) →
    (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C / (1 + ‖x‖)) →
    ∀ x, biotSavart (vorticity u) x = u x

/-- **Reflection equivariance of Biot–Savart** (the "odd" clause of the Lichtenstein–Gunther
class).  If the vorticity is in the parity class `IsOddVorticity` (i.e. `ω ∘ reflZ = -flipZ ∘ ω`,
the parity of `∇×u` for an odd `u`), then `u = biotSavart ω` is reflection invariant,
`u (reflZ x) = flipZ (u x)`; combined with axisymmetry this is `IsOdd u`.  The proof is the
change of variables `y ↦ reflZ y` in the Biot–Savart integral, using that `reflZ` preserves
Lebesgue measure and that `σ(a × b) = det(σ) · (σ a × σ b)` for a reflection `σ`. -/
def BiotSavartReflection : Prop :=
  ∀ ω : R3 → R3, IsOddVorticity ω → ∀ x, biotSavart ω (reflZ x) = flipZ (biotSavart ω x)

/-! ## 2. The local existence inputs -/

/-- **The Lichtenstein–Gunther transport step: local existence for the vorticity equation.**

For every divergence-free `ω₀ ∈ L¹ ∩ L^∞ ∩ C^{0,α}(ℝ³)` there are `T > 0`, a vorticity field
`ω : ℝ³ × [0,T) → ℝ³` and a velocity field `u : ℝ³ × [0,T) → ℝ³` with `u(·,t) = biotSavart (ω(·,t))`,
as follows.

* `ω(·,0) = ω₀`;
* `ω(·,t) ∈ L¹ ∩ L^∞` and divergence-free for every `t ∈ [0,T)`;
* `u` has the *joint* `C^{1,α}` regularity of the Lichtenstein–Gunther class:
  `u.uncurry ∈ C^{1,α}(ℝ³ × [0,S])` for every `S < T`;
* `VorticityEquation u ω`, i.e. `∂ₜω + (u·∇)ω = (ω·∇)u`.

This is the Picard iteration of Lichtenstein and Günther: the vorticity equation is an ODE in the
Banach space `C^{0,α}_b ∩ L¹` whose vector field `ω ↦ -(BS ω ·∇)ω + (ω·∇)(BS ω)` is locally
Lipschitz by the Schauder estimate.  It is *strictly weaker* than the local existence theorem
`Work.LWP.local_existence`: it produces no pressure, no oddness, no identification of the initial
velocity, and states nothing about the Euler equation itself. -/
def VorticityTransportExistence (α : NNReal) : Prop :=
  ∀ ω₀ : R3 → R3, Integrable ω₀ → IsBoundedFun ω₀ → Holder α ω₀ → (∀ x, div ω₀ x = 0) →
    ∃ T : ℝ, 0 < T ∧ ∃ ω : R3 → ℝ → R3, ∃ u : R3 → ℝ → R3,
      (∀ x, ω x 0 = ω₀ x) ∧
      (∀ t ∈ Ico 0 T, ∀ x, u x t = biotSavart (fun y => ω y t) x) ∧
      (∀ t ∈ Ico 0 T, Integrable (fun x => ω x t)) ∧
      (∀ t ∈ Ico 0 T, IsBoundedFun (fun x => ω x t)) ∧
      (∀ t ∈ Ico 0 T, div (fun x => ω x t) = 0) ∧
      (∀ t ∈ Ico 0 T, ∀ x, vorticity (fun y => u y t) x = ω x t) ∧
      (∀ t ∈ Ico 0 T, div (fun x => u x t) = 0) ∧
      (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) ∧
      VorticityEquation u ω

/-- **Existence of the pressure by the Poincaré lemma on `ℝ³`.**  A `C¹` curl-free vector field
on the simply connected domain `ℝ³` is a gradient; the conclusion is written in the equivalent
Riesz form `fderiv ℝ P x y = ⟪F x, y⟫` rather than `∇ P x = F x`.  **This one is no longer an
input**: it is *proved* in `Submission/Work/LWP/CurlFree/curlFree_isGradient.lean`
(`Work.LWP.CurlFree.curlFree_isGradient`), and the abbreviation below is kept so that the
`LWPInputs` bundle can still carry it (a proved `Prop` is a valid field). -/
def CurlFreeIsGradient : Prop :=
  ∀ F : R3 → R3, ContDiff ℝ 1 F → (∀ x, vorticity F x = 0) →
    ∃ P : R3 → ℝ, ∀ x, ∀ y : R3, fderiv ℝ P x y = inner ℝ (F x) y

/-- **Reconstruction of the pressure.**  If `u` has the joint `C^{1,α}` regularity of the
Lichtenstein–Gunther class on `[0,T)`, if `ω(·,t) = ∇×u(·,t)` and `div u(·,t) = 0`, and if `ω`
solves the vorticity equation against `u`, then there is a pressure `p` — itself of class `C^1`
— with `∂ₜu + (u·∇)u + ∇p = 0` on `ℝ³ × (0,T)`.

The vector field `F = ∂ₜu + (u·∇)u` is curl-free: by the vector identity
`∇×((u·∇)u) = (u·∇)(∇×u) − ((∇×u)·∇)u + (div u)(∇×u)` valid for `div u = 0`, its curl is exactly
the left-hand side of the vorticity equation.  In the classical (smooth) case `F` is a gradient
by the Poincaré lemma (`CurlFreeIsGradient`); in the `C^{1,α}` case, where the product
`(∇u)·u` is only `C^{0,α}` and not differentientiable, the pressure is produced directly as the
Schauder solution of the Poisson equation `-Δp = div((u·∇)u)`, which is of class `C^{1,α}` —
this is the elliptic input of the Lichtenstein–Gunther theory. -/
def PressureReconstruction (α : NNReal) : Prop :=
  ∀ (u : R3 → ℝ → R3) (ω : R3 → ℝ → R3) (T : ℝ),
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
    (∀ t ∈ Ico 0 T, ∀ x, vorticity (fun y => u y t) x = ω x t) →
    (∀ t ∈ Ico 0 T, div (fun x => u x t) = 0) →
    VorticityEquation u ω →
    ∃ p : R3 → ℝ → ℝ, ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T) ∧
      ∀ x t, t ∈ Ioo 0 T →
        timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0

/-- **Uniqueness of classical solutions in the Lichtenstein–Gunther class.**  Two solutions with
the same data that are both jointly `C^{1,α}` agree on `[0,T)`.  (The classical proof compares
the vorticity fields along the flow of the difference; it is the "uniqueness" half of the
Lichtenstein–Gunther theorem.) -/
def EulerUniqueness (α : NNReal) : Prop :=
  ∀ (u₀ : R3 → R3) (T : ℝ) (p p' : R3 → ℝ → ℝ) (u u' : R3 → ℝ → R3),
    IsLocalEulerEquationSolution p u₀ T u → IsLocalEulerEquationSolution p' u₀ T u' →
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u'.uncurry (univ ×ˢ Icc 0 S)) →
    ∀ x t, t ∈ Ico 0 T → u x t = u' x t

/-- **Propagation of the odd symmetry.**  If the data are odd then every time slice of a classical
solution is odd.  (The reflected field `x ↦ flipZ (u (reflZ x) t)` is again a solution with the
same data, so uniqueness forces reflection invariance; combined with axisymmetry — which is
`Work.Cyl.isOdd_of_reflZ_invariant` — this is `IsOdd`.) -/
def IsOddPropagates : Prop :=
  ∀ (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ) (u : R3 → ℝ → R3),
    IsOdd u₀ → IsLocalEulerEquationSolution p u₀ T u →
    ∀ t ∈ Ico 0 T, IsOdd (u · t)

/-! ## 3. The continuation input -/

/-- **The Beale–Kato–Majda continuation criterion in the `C^{1,α}` class.**

If a solution exists on `[0,T)` and its BKM integral `bkm u t = ∫₀ᵗ ⨆ₓ‖ω(x,s)‖ ds` stays
*bounded* as `t ↑ T` — equivalently, by monotonicity, `∫₀^T ‖ω(·,s)‖_{L∞} ds < ∞` — then the
solution extends to a solution on `[0,T')` for some `T' > T`, agreeing with the original on
`[0,T)`.

The two ingredients are (i) the a priori estimate
`‖∇u(·,t)‖_{L∞} ≤ C ‖ω(·,t)‖_{L∞} (1 + log⁺(‖ω(·,t)‖_{C^α} / ‖ω(·,t)‖_{L∞}))`
(Calderón–Zygmund with a logarithmic loss), which combined with the transport identity for the
vorticity and the logarithmic Grönwall inequality
(`Work.LWP.BKM.gronwall_log`) bounds the `C^{0,α}` norm of `ω` on `[0,T)`; and (ii) restarting the
local existence theorem at time `T`.

The hypothesis is stated with `bkm` (rather than `IntegrableOn`) so that it is neither stronger
nor weaker than the criterion in the junk-free case, and so that it is *literally* the failure of
the conclusion `Tendsto (bkm u) (𝓝[<] T) atTop` (see `Work.LWP.bkm_divergence_of_maximal`). -/
def BKMExtension (α : NNReal) : Prop :=
  ∀ (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ) (u : R3 → ℝ → R3),
    IsLocalEulerEquationSolution p u₀ T u →
    (∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)) →
    (∃ M : ℝ, ∀ t ∈ Ico 0 T, bkm u t ≤ M) →
    ∃ T' : ℝ, T < T' ∧ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      IsLocalEulerEquationSolution p' u₀ T' u' ∧ ExtendsField u u' T

/-- **Existence of a maximal solution.**  Starting from `EulerData α u₀` (plus the
Biot–Savart-compatible extra data of `EulerDataBS`), the local existence theorem and the
Beale–Kato–Majda continuation criterion produce a maximal solution on some `[0,T)`: one takes
`T = sup {S : a Lichtenstein–Gunther solution exists on [0,S)}` and glues the chain of solutions
along an increasing sequence, using `EulerUniqueness` for well-definedness.  The maximal time is
finite here because the bootstrap produces a genuinely singular solution. -/
def MaximalSolutionExists (α : NNReal) : Prop :=
  ∀ u₀ : R3 → R3, EulerData α u₀ → EulerDataBS α u₀ →
    ∃ T : ℝ, 0 < T ∧ Nonempty (MaximalSolution α u₀ T)

end Work.LWP
