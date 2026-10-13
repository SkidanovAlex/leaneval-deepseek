/-
# `Work.LWP` — the vocabulary of the local well-posedness / continuation area

This module fixes the *notions* of the Lichtenstein–Gunther local well-posedness and
Beale–Kato–Majda continuation area for the paper

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

Everything here is stated against the *fixed* definitions of `ChallengeDeps.lean`
(`FiniteTimeSingularity.vorticity`, `FiniteTimeSingularity.div`,
`FiniteTimeSingularity.timeDeriv`, `FiniteTimeSingularity.directionalDeriv`,
`FiniteTimeSingularity.IsLocalEulerEquationSolution`, `FiniteTimeSingularity.IsOdd`,
`IsContDiffHolder`, `IsContDiffHolderOn`, `Holder`, `IsBoundedFun`, …).  Nothing in
`ChallengeDeps` is redefined.

## Conventions

* The spacetime velocity field is a *curried* function `u : R3 → ℝ → R3`, applied as `u x t`
  and sliced as `u · t`; this is exactly the convention of `ChallengeDeps`.
* `R3 = EuclideanSpace ℝ (Fin 3)`; `‖·‖` is the `L²` (Euclidean) norm.
* The flow `φ` of a velocity field is written *time first*, `φ t x`; `IsFlowOf u φ` records
  `φ 0 x = x` and `∂ₜ (φ · x) = u (φ t x) t`.
* `biotSavart ω` is the Newtonian-potential Biot–Savart operator of (BSLaw) in the paper's
  Introduction: the velocity field whose curl is `ω`.  It is normalised with the standard
  `(4π)^{-1}` and the sign is pinned by `biotSavart_vorticity` in `BiotSavart.lean`.

## What the consumer imports

`import Submission.Work.LWP.Defs` for the vocabulary; `import Submission.Work.LWP` for the
whole chapter (vocabulary + Hölder API + flows + Biot–Savart + local existence + BKM).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ChallengeDeps
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## The ambient space -/

/-- `ℝ³`, i.e. `EuclideanSpace ℝ (Fin 3)`.  The challenge writes `local notation "ℝ³" => …`;
we expose it globally inside `Work.LWP` so that statements can be read without the notation. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## Initial data and the Lichtenstein–Gunther class -/

/-- The decay clause on the vorticity appearing in `theorem_1`: `‖ω x‖ ≤ C / (‖x‖^α + 1)`. -/
def VorticityDecay (α : ℝ≥0) (ω : R3 → R3) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖ω x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)

/-- **Lichtenstein–Gunther admissible initial data**: a divergence-free, odd vector field of class
`C^{1,α}(ℝ³)` whose vorticity decays as in the main theorem.  This is exactly the data class of
Elgindi's Theorem 1 (and of the classical Lichtenstein–Gunther local well-posedness theorem). -/
structure EulerData (α : ℝ≥0) (u₀ : R3 → R3) : Prop where
  /-- `u₀` is divergence-free. -/
  div_free : div u₀ = 0
  /-- `u₀` is odd in the sense of `FiniteTimeSingularity.IsOdd`. -/
  odd : IsOdd u₀
  /-- `u₀ ∈ C^{1,α}(ℝ³)`: `ContDiff 1`, bounded derivative, `α`-Hölder derivative. -/
  contDiffHolder : IsContDiffHolder ℝ α u₀
  /-- The vorticity decays like `‖x‖^{-α}` at infinity. -/
  vort_decay : VorticityDecay α (vorticity u₀)

/-- Joint `C^{1,α}` regularity in `(x,t)` of a spacetime field, on every strip `ℝ³ × [0,S]`
with `S < T` — the regularity clause of the main theorem. -/
def SpaceTimeHolder (α : ℝ≥0) (u : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)

/-- **The Lichtenstein–Gunther solution class** on `[0,T)`: a solution of the incompressible Euler
equation in the sense of `IsLocalEulerEquationSolution`, odd at every time, and jointly
`C^{1,α}` on compact time strips.  This is the class of solutions whose existence the classical
theory of Lichtenstein and Günther asserts, and the class in which the main theorem is stated. -/
structure LGClass (α : ℝ≥0) (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ)
    (u : R3 → ℝ → R3) : Prop where
  /-- `(p,u)` solves the incompressible Euler equation up to time `T` with data `u₀`. -/
  sol : IsLocalEulerEquationSolution p u₀ T u
  /-- The oddness of the data is propagated in time. -/
  odd : ∀ t ∈ Ico 0 T, IsOdd (u · t)
  /-- Joint `C^{1,α}` regularity on compact time strips. -/
  spacetime : SpaceTimeHolder α u T

/-- **Biot–Savart-compatible initial data**: the extra properties of the initial datum needed to
run the reconstruction `ω₀ ↦ u = biotSavart ω₀` of the Lichtenstein–Gunther argument on top of
the *analytically* given datum class `EulerData`.  They are: the vorticity is `L¹` (so that the
Newtonian-potential Biot–Savart integral converges), the vorticity is divergence-free (the
standing assumption the paper's Introduction makes when solving the vorticity equation), and the
velocity decays at infinity (so that it is recovered from its vorticity; both are automatic for
the compactly supported vorticity of the assembly's construction). -/
structure EulerDataBS (α : ℝ≥0) (u₀ : R3 → R3) : Prop where
  /-- the vorticity is integrable, so that `biotSavart (vorticity u₀)` converges -/
  vort_integrable : Integrable (vorticity u₀)
  /-- the vorticity is divergence-free -/
  vort_div_free : ∀ x : R3, div (vorticity u₀) x = 0
  /-- the vorticity is bounded -/
  vort_bounded : IsBoundedFun (vorticity u₀)
  /-- the vorticity is `α`-Hölder -/
  vort_holder : Holder α (vorticity u₀)
  /-- the velocity decays at infinity, so that the Biot–Savart law inverts `∇×` -/
  decay : ∃ C : ℝ, ∀ x : R3, ‖u₀ x‖ ≤ C / (1 + ‖x‖)

/-- `u'` extends `u` on `[0,T)`. -/
def ExtendsField (u u' : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ x t, t ∈ Ico 0 T → u' x t = u x t

/-- A uniform-in-time bound on the sup-norm of the vorticity (as a function, not a `sSup`). -/
def UniformlyBoundedVorticity (u : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Ico 0 T, ∀ x : R3, ‖vorticity (u · t) x‖ ≤ M

/-! ## The Beale–Kato–Majda quantity -/

/-- The Beale–Kato–Majda quantity `∫₀ᵗ (⨆ₓ ‖ω(x,s)‖) ds` of the main theorem.  This is
*definitionally* the expression appearing in the challenge statement
`∫ s in 0..t, ⨆ x, ‖(∇×(u · s)) x‖`. -/
noncomputable def bkm (u : R3 → ℝ → R3) (t : ℝ) : ℝ :=
  ∫ s in 0..t, ⨆ x, ‖vorticity (u · s) x‖

/-- The `L∞`-in-space norm of the vorticity at time `t`, as a `sSup` (the integrand of `bkm`). -/
noncomputable def vortLInf (u : R3 → ℝ → R3) (t : ℝ) : ℝ := ⨆ x, ‖vorticity (u · t) x‖

/-! ## The vorticity formulation -/

/-- `ω` is the vorticity of `u`, pointwise. -/
def IsVorticityOf (u ω : R3 → R3) : Prop := ∀ x : R3, vorticity u x = ω x

/-- The 3D vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u`, written with the fixed definitions
`timeDeriv`, `directionalDeriv` of `ChallengeDeps`. -/
def VorticityEquation (u ω : R3 → ℝ → R3) : Prop :=
  ∀ x t, timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t

/-- The `div`-free condition on a spacetime vorticity field, slice by slice. -/
def DivFreeSlices (ω : R3 → ℝ → R3) : Prop := ∀ t, div (ω · t) = 0

/-! ## The reflection in the plane `x₃ = 0` -/

/-- The reflection of `ℝ³` in the plane `x₃ = 0`, i.e. `x ↦ (x₀, x₁, -x₃)`.  (This is
`Work.Cyl.reflZ`; it is repeated here so that `Work.LWP` is self-contained.) -/
def reflZ (x : R3) : R3 := WithLp.toLp 2 ![x 0, x 1, - x 2]

/-- The reflection of the *components* of a vector `v ↦ (v₀, v₁, -v₃)`.  (This is
`Work.Cyl.flipZ`.) -/
def flipZ (v : R3) : R3 := WithLp.toLp 2 ![v 0, v 1, - v 2]

/-- The parity class of the vorticity of an odd axisymmetric no-swirl velocity field: `ω` changes
sign under the reflection `reflZ` up to the component flip `flipZ`, i.e.
`ω (reflZ x) = - flipZ (ω x)`.  For `ω = ∇×u` this is equivalent to `u` being reflection-invariant
(hence, together with axisymmetry, `IsOdd`), by the identity
`curl (σ·v) = -σ·(curl v)` for a reflection `σ`. -/
def IsOddVorticity (ω : R3 → R3) : Prop := ∀ x, ω (reflZ x) = - flipZ (ω x)

/-! ## Biot–Savart -/

/-- The **Biot–Savart operator** on `ℝ³`, in the Newtonian-potential form obtained from
`u = ∇× (4π)^{-1}∫ ω(y)/‖x-y‖ dy`:

  `biotSavart ω x = (4π)^{-1} ∫ (ω y) ⨯₃ (x - y) / ‖x - y‖³ dy`.

Off the (measure-zero) diagonal the kernel is `(4π)^{-1} ω(y) × (x-y)/‖x-y‖³`, so that
`∇× (biotSavart ω) = ω` for divergence-free `ω` with sufficient decay — this is the Biot–Savart
law `u = (-Δ)^{-1}(∇×ω)` of the paper's Introduction. -/
noncomputable def biotSavart (ω : R3 → R3) (x : R3) : R3 :=
  (4 * Real.pi)⁻¹ • ∫ y : R3,
    WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • ((ω y) ⨯₃ (x - y)))

/-- The scalar form of the Biot–Savart kernel: `(4π)^{-1} / ‖x - y‖³` times the cross product. -/
noncomputable def bsKernel (ω : R3 → R3) (x y : R3) : R3 :=
  WithLp.toLp 2 (((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3 : ℕ))⁻¹) • ((ω y) ⨯₃ (x - y)))

/-! ## Flows -/

/-- `φ` is the flow of the (time-dependent) velocity field `u`: for each initial point `x`, the
curve `φ x ·` is the integral curve of `u` starting at `x`, i.e. `φ x 0 = x` and
`∂ₜ (φ x ·) t = u (φ x t) t` for every `t`.  As for the velocity field, the initial point comes
first. -/
def IsFlowOf (u : R3 → ℝ → R3) (φ : R3 → ℝ → R3) : Prop :=
  (∀ x, φ x 0 = x) ∧ ∀ x t, HasDerivAt (fun s => φ x s) (u (φ x t) t) t

/-- The Lagrangian (transport) form of the vorticity equation along a flow:
`ω (φ x t) t = Dφ(t,x) · ω(x,0)`. -/
def LagrangianTransport (ω : R3 → ℝ → R3) (φ : R3 → ℝ → R3) : Prop :=
  ∀ x t, ω (φ x t) t = fderiv ℝ (fun y => φ y t) x (ω x 0)

/-- The spatial support of the time slice `t` of a spacetime field. -/
def sliceSupport (ω : R3 → ℝ → R3) (t : ℝ) : Set R3 := Function.support (ω · t)

/-- Transport of the support of the vorticity by the flow. -/
def TransportsSupport (ω : R3 → ℝ → R3) (φ : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, sliceSupport ω t = (fun x => φ x t) '' sliceSupport ω 0

/-! ## Maximal solutions -/

/-- A **maximal Lichtenstein–Gunther solution** on `[0,T)`: a `C^{1,α}` solution on every
`[0,S]`, `S < T`, which cannot be extended past `T` as a solution of the same kind.  The
divergence of the BKM integral at `T` is *not* a field of this structure: it is a theorem
(`Work.LWP.bkm_divergence_of_maximal`) proved from the Beale–Kato–Majda continuation criterion.
This is the object the main theorem's conclusion is phrased in terms of (with `T = 1`). -/
structure MaximalSolution (α : ℝ≥0) (u₀ : R3 → R3) (T : ℝ) where
  /-- the maximal time is positive -/
  T_pos : 0 < T
  /-- the pressure -/
  p : R3 → ℝ → ℝ
  /-- the velocity -/
  u : R3 → ℝ → R3
  /-- the solution on `[0,T)`, in the challenge's predicate -/
  sol : IsLocalEulerEquationSolution p u₀ T u
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Ico 0 T, IsOdd (u · t)
  /-- joint `C^{1,α}` regularity on compact time strips -/
  spacetime : SpaceTimeHolder α u T
  /-- no solution of class `C^{1,α}` with the same data extends it past `T` -/
  maximal : ¬ ∃ T' : ℝ, T < T' ∧ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
    IsLocalEulerEquationSolution p' u₀ T' u' ∧ ExtendsField u u' T

end Work.LWP
