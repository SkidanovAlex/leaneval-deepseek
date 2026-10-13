/-
# `Work.FTS.Physical.Defs` — the vocabulary of the physical reconstruction (node N8)

This is the area of the `fts` / `annals_finite_time_singularity` project that owns **node N8** of
the lead's audit (`FTS_AUDIT_LEAD.md` §4): the passage from the *fake-time* dynamic solution of
the paper's rescaled equation back to the *physical* solution of the incompressible Euler
equation on `ℝ³`, together with the interface `BlowupAt` that the top-level wiring (node N0)
consumes.

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
  Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

The chapter is deliberately written against the *fixed* definitions of `ChallengeDeps.lean` and
the existing vocabulary of the workspace (`Work.LWP.Defs`: `biotSavart`, `vortLInf`, `IsOddVorticity`;
`Work.CoreResiduals.Defs`: `BSAdmissibleStripFull`, `BiotSavartSpaceTime`;
`Work.Cyl`: the `(ρ,θ)` dictionary).  Nothing of `ChallengeDeps` is redefined.

## The physics-to-fake-time dictionary

The paper's construction produces a solution `F = F_* + g` of the rescaled ("fake-time")
equation in the variables `(z, θ, τ)`, `z = ρ^{3α}/B(τ)`, `ρ = ‖x‖`, `θ = arctan(x₃/r)`, with a
clock `τ ↦ t` given by `dt/dτ = A(τ)` where the amplitude `A` solves `A' = -(1+μ)A`.  The
physical vorticity of the reconstructed solution is

  `ω(x,t) = A(τ(t))⁻¹ · χ(ρ(x)/L) · F(ρ(x)^{3α}/B(τ(t)), θ(x), τ(t)) · e_θ(x)`,

and the physical velocity is `BS ω`.  The quantitative content of the reconstruction is:

* the **clock**: `A > 0`, `A' = -(1+μ)A` with `1/2 ≤ 1+μ ≤ 2` gives `A(τ) ≤ A(0)e^{-τ/2}`, hence
  `∫₀^∞ A < ∞`; `t(τ) = ∫₀^τ A` increases to the blow-up time `T`, and the tail identity
  `T - t(τ) = ∫_τ^∞ A ≤ 2A(τ)` gives the `A ≍ T - t` comparison;
* the **Biot–Savart velocity** `u = BS ω`: joint `C^{1,α}` on the strips comes from the
  space-time Schauder estimate `Work.CoreResiduals.BiotSavartSpaceTime` (proved in the workspace),
  oddness from `Work.LWP.biotSavart_reflZ`, divergence-freeness from the Biot–Savart law;
* the **div-curl / Liouville identification**: two odd, sublinear, divergence-free fields with the
  same curl differ by an odd sublinear harmonic field, which vanishes (`DivCurlLiouville`); this is
  what identifies `BS ω` with the paper's stream-function field `psiField Φ` and hence transfers
  the vorticity equation of the fake-time solution to the physical pair `(u, ω)`;
* the **pressure**: `curl(∂ₜu + (u·∇)u) = 0` by the vorticity equation, so the Poincaré lemma on
  `ℝ³` (`Work.LWP.CurlFree.curlFree_isGradient`) produces `p` with `∇p = -(∂ₜu + (u·∇)u)`;
* the **`c/(T-t)` lower bound**: the profile bound `|F_* + g| ≥ c₀α` at a point of the domain
  (`Work.StabilityFar.Profile.exists_Fstar_add_ge`) and `A(τ(t)) ≤ 2(T-t)` give
  `‖ω(·,t)‖_∞ ≥ c/(T-t)`, which is `BlowupAt.lower`.

## Interfaces and their inhabitation

Per the lead's rule, every structure of this chapter comes with an inhabitation obligation that is
*discharged in the workspace*: `PhysClock` is inhabited by the explicit clock `A(τ) = e^{-τ}`,
`μ = 0` (`PhysClock.expInhabited`), and the purely elementary data of the reconstruction
(`PhysProfileData` in `Physical/Profile.lean`) is inhabited by the trivial profile.  The analytic
content of the fake-time solution is **not** bundled into a structure here: the reconstruction
theorems of `Physical/Reconstruction.lean` take it as explicit, named hypotheses about objects
different from their conclusions.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- `ℝ³`, definitionally `Work.LWP.R3` and `Work.Cyl.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The clock `τ ↦ t` -/

/-- **The clock of the dynamic rescaling.**  The amplitude `A = A(τ)` of the physical vorticity
solves `A' = -(1+μ)A` in fake time, where the modulation `1+μ` stays in `[1/2,2]`.  The physical
time is `t(τ) = ∫₀^τ A`, the blow-up time is `T = ∫₀^∞ A`, and the reconstruction lives on
`[0,T)`.

The two constants `1/2 ≤ 1+μ ≤ 2` are the paper's `Λ`-bounds of the modulation bootstrap: they are
exactly what makes `A` decay like `e^{-τ/2}` (so that `T < ∞`, i.e. the blow-up is in finite time)
and what makes `A(τ) ≥ (T - t(τ))/2` (so that the vorticity lower bound blows up at the rate
`1/(T-t)`). -/
structure PhysClock where
  /-- the amplitude `A(τ)` of the rescaled solution -/
  A : ℝ → ℝ
  /-- the modulation `μ(τ)` -/
  mu : ℝ → ℝ
  /-- `A > 0` in fake time -/
  hApos : ∀ τ : ℝ, 0 ≤ τ → 0 < A τ
  /-- `A` is continuous on the fake-time half-line -/
  hAcont : ContinuousOn A (Set.Ici (0 : ℝ))
  /-- the modulation ODE `A' = -(1+μ)A` -/
  hAderiv : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + mu τ) * A τ) τ
  /-- the lower modulation bound `1/2 ≤ 1+μ` -/
  hmu_lo : ∀ τ : ℝ, 0 ≤ τ → 1 ≤ 2 * (1 + mu τ)
  /-- the upper modulation bound `1+μ ≤ 2` -/
  hmu_hi : ∀ τ : ℝ, 0 ≤ τ → 1 + mu τ ≤ 2

namespace PhysClock

/-- The physical time `t(τ) = ∫₀^τ A(s) ds`. -/
noncomputable def t (C : PhysClock) (τ : ℝ) : ℝ := ∫ s in (0 : ℝ)..τ, C.A s

/-- The blow-up time `T = ∫₀^∞ A(s) ds`. -/
noncomputable def T (C : PhysClock) : ℝ := ∫ s in Set.Ici (0 : ℝ), C.A s

@[simp] theorem t_zero (C : PhysClock) : C.t 0 = 0 := by simp [t]

end PhysClock

/-! ## The physical vorticity and velocity -/

/-- **The physical velocity is the Biot–Savart field of the physical vorticity.**  This is the
reconstruction `u = BS ω` of the paper's Introduction; the analytic property that makes it useful
is the Calderón–Zygmund/Schauder estimate for compactly supported Hölder vorticity, proved in
`Work.CoreResiduals.BiotSavart` and packaged as `Work.CoreResiduals.BiotSavartSpaceTime`. -/
noncomputable def physVel (ω : R3 → ℝ → R3) : R3 → ℝ → R3 :=
  fun x t => Work.LWP.biotSavart (fun y => ω y t) x

theorem physVel_apply (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    physVel ω x t = Work.LWP.biotSavart (fun y => ω y t) x := rfl

/-- The slice form of `physVel`. -/
theorem physVel_slice (ω : R3 → ℝ → R3) (t : ℝ) :
    (physVel ω · t) = Work.LWP.biotSavart (fun y => ω y t) := rfl

/-! ## The `BlowupAt` interface (node N0)

This is the object the top-level wiring consumes: a genuinely blowing-up solution of the
incompressible Euler equation on `ℝ³`, with all the structural clauses of `theorem_1` except the
normalisation of the blow-up time.  It contains no hypothesis at or past the blow-up time: all
regularity clauses are on the strips `[0,S]`, `S < T`. -/

/-- **A finite-time blow-up of the incompressible Euler equation at time `T > 0`, of
`C^{1,α}` class with `α`-decaying compactly supported technology.**  The fields are `u` (velocity)
and `p` (pressure); the clauses are, in order: `(p,u)` solves Euler on `[0,T)` with initial datum
`u(·,0)`; the datum is divergence-free; the solution is odd at every time; the datum is `C^{1,α}`;
the datum's vorticity decays as in `theorem_1`; the solution is jointly `C^{1,α}` on every strip
`ℝ³ × [0,S]`, `S < T`; and the vorticity sup-norm dominates `c/(T-t)`. -/
structure BlowupAt (α : ℝ≥0) (T : ℝ) where
  /-- the velocity field -/
  u : R3 → ℝ → R3
  /-- the pressure field -/
  p : R3 → ℝ → ℝ
  /-- the blow-up time is positive -/
  hT : 0 < T
  /-- `(p,u)` solves the incompressible Euler equation on `[0,T)` with datum `u(·,0)` -/
  sol : IsLocalEulerEquationSolution p (u · 0) T u
  /-- the datum is divergence-free -/
  div0 : div (u · 0) = 0
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Set.Ico 0 T, IsOdd (u · t)
  /-- the datum is `C^{1,α}` -/
  cdh0 : IsContDiffHolder ℝ α (u · 0)
  /-- the datum's vorticity decays like `‖x‖^{-α}` -/
  decay0 : ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity (u · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)
  /-- joint `C^{1,α}` regularity on the strips `ℝ³ × [0,S]`, `S < T` -/
  strip : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)
  /-- the `c/(T-t)` lower bound on the vorticity sup-norm -/
  lower : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t

/-! ## The div-curl / Liouville input

The one classical analytic fact that the workspace does not yet contain (and that the paper's
reconstruction uses to identify the Biot–Savart field with the stream-function field): a harmonic
vector field of sublinear growth is constant, and hence — if it is odd — zero.  It is stated here
in the form in which the reconstruction consumes it: as a *difference* statement, so that it
applies to two candidate velocities with the same curl. -/

/-- `F` grows at most like `‖x‖^s` (`s < 1`): the sublinear bound of the Liouville argument. -/
def Sublinear (F : R3 → R3) : Prop :=
  ∃ C s : ℝ, 0 ≤ C ∧ s < 1 ∧ ∀ x : R3, ‖F x‖ ≤ C * (1 + ‖x‖) ^ s

/-- **Div-curl Liouville lemma.**  Two odd, `C¹`, divergence-free fields of sublinear growth whose
curls agree are equal.

This is the classical Liouville theorem for harmonic functions, in the form in which the
reconstruction consumes it: the difference of two fields with the same curl and divergence is
harmonic (each component has vanishing Laplacian), and a harmonic *vector field* of sublinear
growth is constant; oddness forces the constant to be `0`.  It is the analytic input of the
identification `BS ω = psiField Φ`; the reduction of the identification to it is proved in
`Physical/Liouville.lean`. -/
def DivCurlLiouville : Prop :=
  ∀ F G : R3 → R3, ContDiff ℝ 1 F → ContDiff ℝ 1 G →
    (∀ x, div F x = 0) → (∀ x, div G x = 0) →
    (∀ x, vorticity F x = vorticity G x) →
    Sublinear F → Sublinear G → IsOdd (F - G) → ∀ x, F x = G x

end Work.FTS.Physical
