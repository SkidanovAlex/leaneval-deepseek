import Submission.UnifDeps
import Submission.GreenInterface
import Submission.HolomorphicLog
import Submission.Conjugate
import Submission.Work.UnitGreen.Defs

/-!
# The holomorphic modulus of the Green function: definitions

This module sets up the vocabulary for the "periods are multiples of `2π`" step of the
hyperbolic case of uniformization (Hubbard, *Teichmüller theory* Vol. 1, Chapter 1).

Throughout, `X` is a complex one-manifold, `z₀ : X`, and `E : X → ℝ` is a Green function with pole
`z₀` in the sense of `Work.UnitGreen.IsUnitGreenFunctionAt`: positive and harmonic off `z₀`, with logarithmic
pole at `z₀` and compact superlevel sets (decay at the ideal boundary).

The classical construction of the uniformizing map is `Φ = exp (-(E + iE*))`, where `E*` is the
harmonic conjugate of `E`; the conjugate is only defined modulo the periods of `E`, and `Φ` is
single-valued precisely when all periods are multiples of `2π`.

We isolate the two notions that the argument needs:

* `Work.Modulus.IsLocalModulus z₀ E U Φ` — `Φ` is a **local holomorphic modulus** for `E` on `U`:
  holomorphic on `U`, non-vanishing off `z₀` and with modulus `exp (-E)` there;

* `Work.Modulus.HasTrivialModulusMonodromy z₀ E` — the **monodromy of the multivalued modulus is
  trivial**: every local modulus continues single-valuedly along every loop in `X ∖ {z₀}`.

The main result of the chapter is that the unit-pole Green function of a Riemann surface with
`H¹(X,ℝ) = 0` has a global holomorphic modulus: see `Work.Modulus.Main`, in particular
`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112`.  (The name
`Work.Modulus.exists_holomorphic_modulus_of_greenFunction` in `Main.lean` is the requested
statement with the older, unsatisfiable hypothesis `Submission.HasGreenFunctionE`; see
`Work.Modulus.not_hasGreenFunctionE` and the module docstring of `Main.lean`.)
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A local holomorphic modulus for `E` on the open set `U`.**  `Φ` is holomorphic on `U`, does not
vanish on `U ∖ {z₀}`, and has modulus `exp (-E)` there.  (The point `z₀` is allowed to be a zero of
`Φ`; the local modulus produced by the Green function vanishes there to first order.) -/
def IsLocalModulus (z₀ : X) (E : X → ℝ) (U : Set X) (Φ : X → ℂ) : Prop :=
  IsOpen U ∧ Submission.HolomorphicOnX Φ U ∧
    (∀ x ∈ U, x ≠ z₀ → Φ x ≠ 0) ∧
    (∀ x ∈ U, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))

/-- The open set on which the conjugate of `E` lives: the complement of the pole. -/
def punctured (z₀ : X) : Set X := {z₀}ᶜ


@[simp] theorem mem_punctured {z₀ x : X} : x ∈ punctured z₀ ↔ x ≠ z₀ := Iff.rfl

theorem isOpen_punctured (z₀ : X) : IsOpen (punctured z₀) := isOpen_compl_singleton

/-- The punctured surface `X ∖ {z₀}` as an *open subset* (`TopologicalSpace.Opens`), so that
Mathlib's charted-space and manifold instances for open subsets apply to it.  As a type it is
definitionally equal to `↥(punctured z₀)`. -/
def puncturedOpens (z₀ : X) : TopologicalSpace.Opens X :=
  ⟨punctured z₀, isOpen_punctured z₀⟩

@[simp] theorem coe_puncturedOpens (z₀ : X) :
    ((puncturedOpens z₀ : TopologicalSpace.Opens X) : Set X) = punctured z₀ := rfl

instance puncturedOpens_charted (z₀ : X) : ChartedSpace ℂ (puncturedOpens z₀) := inferInstance

instance puncturedOpens_manifold (z₀ : X) :
    IsManifold (modelWithCornersSelf ℂ ℂ) 1 (puncturedOpens z₀) := inferInstance

/-- **Triviality of the monodromy of the multivalued modulus.**  Every local modulus extends
single-valuedly: there is a *global* holomorphic `Φ` with modulus `exp (-E)` off the pole.  This is
the form in which the period computation (periods are multiples of `2π`) is consumed. -/
def HasTrivialModulusMonodromy (z₀ : X) (E : X → ℝ) : Prop :=
  ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ univ ∧
    (∀ x, x ≠ z₀ → Φ x ≠ 0) ∧ (∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))

theorem HasTrivialModulusMonodromy.isLocalModulus {z₀ : X} {E : X → ℝ}
    (h : HasTrivialModulusMonodromy z₀ E) :
    ∃ Φ, IsLocalModulus z₀ E univ Φ := by
  obtain ⟨Φ, hhol, hne, hmod⟩ := h
  exact ⟨Φ, isOpen_univ, hhol, fun x _ => hne x, fun x _ => hmod x⟩

end Work.Modulus
