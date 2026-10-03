import Mathlib
import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.GreenData
import Submission.Lib.Unif2.GreenModulus
import Submission.Lib.Unif2.GreenConditional
import Submission.Lib.Unif2.Helpers

/-!
# The Green-modulus interface

This module fixes the exact shape of the "hyperbolic" input to the uniformization theorem, so that
the remaining work can be split cleanly.  Two predicates are introduced.

* `Submission.HasGreenFunctionWeak z₀ E` — the *weak* potential-theoretic data: `E > 0` off `z₀`,
  harmonic there, and decaying at the ideal boundary (all superlevel sets `{x | ε ≤ E x}`,
  `ε > 0`, are compact).  This is exactly the negation of the hypothesis of
  `Work.Parabolic.plane_of_no_greenFunction`, so the *parabolic* case of uniformization is
  `¬ ∃ z₀ E, HasGreenFunctionWeak z₀ E`.

* `Submission.HasGreenFunctionE z₀ E` — the *strong* data: the weak data together with a
  *logarithmic pole of coefficient one* at `z₀` (`E x + log ‖(chartAt ℂ z₀) x - chart z₀‖` bounded
  near `z₀`, and `E → +∞` at `z₀`).

* `Submission.HasGreenModulusData z₀` — the *analytic* data: a strong Green function `E` together
  with a holomorphic `Φ` with a simple zero at `z₀` and `‖Φ x‖ = exp (-E x)` off `z₀`.  This is
  precisely the hypothesis list of `Submission.uniformization_of_green_modulus`, which concludes
  the uniformization theorem.

The three remaining (delegated) steps are

* `Work.Modulus.exists_holomorphic_modulus_of_greenFunction` — strong data ⟹ holomorphic modulus
  (the periods of the conjugate of `E` are multiples of `2π`; the only place where the challenge
  hypothesis `H¹(X,ℝ) = 0` is used);
* `Submission.exists_hasGreenFunctionE_of_hasGreenFunctionWeak` —
  `HasGreenFunctionWeak z₀ E ⟹ ∃ E', HasGreenFunctionE z₀ E'` (rescaling by the order of the
  logarithmic pole, and filling in a unit-pole potential when the pole is removable);
* `Work.Parabolic.plane_of_no_greenFunction` — no weak Green function ⟹ `X ≅ ℂ`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold mℂ 1 X]

/-- **The weak Green function data at `z₀`.**

⚠ **THIS PREDICATE IS UNSATISFIABLE** on a non-compact `X`
(`Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact`): because `E : X → ℝ` is a *total*
function, `E z₀` is finite, so `{x | ε ≤ E x}` for `ε > E z₀` is closed and misses `z₀`; for it to
be compact it must keep a positive distance from `z₀`, forcing `E` to be bounded near `z₀`, whence
(removable singularity + maximum principle) `E` is a nonnegative harmonic function with compact
superlevel sets on a non-compact surface, which is impossible.  The satisfiable notion — the one
every statement about Green functions in this workspace must use — is
`Work.Parabolic.IsGreenFunctionAt z₀ E` (`Submission/Work/Parabolic/Basic.lean`), which asks for
`IsCompact (closure {x | ε ≤ E x})`, and `Work.UnitGreen.IsUnitGreenFunctionAt`, which additionally
normalises the logarithmic pole.  This definition and `HasGreenFunctionE` below are kept only so
that earlier files still build; do not use them in new statements.

`E` is positive and harmonic off `z₀` and tends to `0` at the ideal boundary, in the sense that
every superlevel set `{x | ε ≤ E x}` (`ε > 0`) is compact. -/
def HasGreenFunctionWeak (z₀ : X) (E : X → ℝ) : Prop :=
  (∀ x, x ≠ z₀ → 0 < E x) ∧
  HarmonicOnX E (univ \ {z₀}) ∧
  (∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ E x})

/-- **The strong Green function data at `z₀`.**  ⚠ Unsatisfiable for the same reason as
`HasGreenFunctionWeak` above; use `Work.UnitGreen.IsUnitGreenFunctionAt` instead.

  In addition to the weak data, `E` has a
*logarithmic pole of coefficient one* at `z₀`: in the preferred chart at `z₀` the quantity
`E x + log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖` stays bounded near `z₀`, and `E` is unbounded
above there. -/
def HasGreenFunctionE (z₀ : X) (E : X → ℝ) : Prop :=
  HasGreenFunctionWeak z₀ E ∧
  (∃ C : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
    |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C) ∧
  (∀ A : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ → A < E x)

/-- The strong data implies the weak data. -/
theorem HasGreenFunctionE.weak {z₀ : X} {E : X → ℝ} (h : HasGreenFunctionE z₀ E) :
    HasGreenFunctionWeak z₀ E := h.1

/-- **The logarithmic-singularity input** (Bôcher's theorem for positive harmonic functions):
near an isolated singularity a positive harmonic function differs from `-c·log ‖ξ‖` by a bounded
quantity, with `c ≥ 0`.  `Work.Potential.logCoefficient_of_pos_harmonic` proves this. -/
def LogCoefficientInput (z₀ : X) : Prop :=
  ∀ {u : X → ℝ}, HarmonicOnX u (univ \ {z₀}) → (∀ x, x ≠ z₀ → 0 < u x) →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ C : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
      |u x + c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C

/-- **The removable-singularity input**: a harmonic function on `X \ {z₀}` bounded in a
neighbourhood of `z₀` extends to a harmonic function on `X`.
`Work.Potential.removable_singularity_of_bounded_near` proves this. -/
def RemovableInput (z₀ : X) : Prop :=
  ∀ {u : X → ℝ}, HarmonicOnX u (univ \ {z₀}) →
    (∃ M : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ → |u x| ≤ M) →
    ∃ U : X → ℝ, HarmonicOnX U univ ∧ ∀ x, x ≠ z₀ → U x = u x

/-- **The hyperbolic input of the uniformization theorem.**  A point `z₀` together with a strong
Green function and a holomorphic function whose modulus is `exp (-E)` — exactly the hypotheses of
`Submission.uniformization_of_green_modulus`. -/
def HasGreenModulusData (z₀ : X) : Prop :=
  ∃ (E : X → ℝ) (Φ : X → ℂ),
    HasGreenFunctionE z₀ E ∧
    HolomorphicOnX Φ univ ∧ HasLogPoleAt z₀ Φ ∧
    (∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))

/-- **The hyperbolic endgame.**  If the Green-modulus data exist at some `z₀` and `X` is
non-compact, the uniformization conclusion holds. -/
theorem uniformization_of_greenModulusData (hX : ¬ CompactSpace X) {z₀ : X}
    (h : HasGreenModulusData (X := X) z₀) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  obtain ⟨E, Φ, hE, hΦ, hpole, hmod⟩ := h
  obtain ⟨hpos, -, hinf⟩ := hE.1
  exact uniformization_of_green_modulus (X := X) hX hΦ hpos hmod hinf hpole

/-- The uniformization conclusion from the *strong Green function* together with a holomorphic
modulus `Φ` for it. -/
theorem uniformization_of_greenFunctionE (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hE : HasGreenFunctionE (X := X) z₀ E) (hΦ : HolomorphicOnX Φ univ)
    (hpole : HasLogPoleAt z₀ Φ)
    (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  uniformization_of_greenModulusData hX ⟨E, Φ, hE, hΦ, hpole, hmod⟩

end Submission
