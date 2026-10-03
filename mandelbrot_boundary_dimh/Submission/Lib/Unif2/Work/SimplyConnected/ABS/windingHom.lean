import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Main
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.Modulus.hasTrivialModulusMonodromy_of_periods
import Submission.Lib.Unif2.Work.Modulus.poleOrderModulus

/-!
# The integer-valued period (winding) homomorphism of the punctured surface

Let `X` be a connected Riemann surface, `x₀ : X`, `U := X ∖ {x₀}` (as `Work.Modulus.puncturedOpens
x₀`), and `E` a *unit-pole* Green function at `x₀` (`Work.UnitGreen.IsUnitGreenFunctionAt`).

## The object

`P := Work.Modulus.greenPeriodHom hE u₀ : Additive (π₁(U,u₀)) →+ ℝ` is the drift of the harmonic
conjugate of `E` around a loop of `U`; the holomorphic modulus `exp (-(E + iE*))` is single-valued
exactly when `P (π₁ U) ⊆ 2πℤ`.

The purpose of this file is to isolate the **arithmetic content** of that statement as a
factorisation of `P` through the *integer-valued* winding homomorphism

`W : Additive (π₁(U,u₀)) →+ ℤ`,   `P = 2π · W`,

i.e. `P γ = (W γ : ℝ) * (2π)` for all `γ`.  This is the exact shape in which the missing
topological input enters the target `unitGreen_modulus_of_subsingleton_hom`:

* `unitGreen_modulus_of_integerValuedPeriods` (below, **sorry-free**) — the requested modulus
  follows as soon as a single integer-valued homomorphism `W` with `P = 2π · W` is exhibited.  The
  proof is `Work.Modulus.hasTrivialModulusMonodromy_of_periods` plus
  `Work.Modulus.poleOrderModulus_of_unitGreen`.

* `exists_integerValued_greenPeriodHom` (below, **the remaining obligation**) — such a `W` exists,
  under `[Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]`.

## Why the obligation splits into two classical pieces

Write `j : π₁(U) → π₁(X)` for the map induced by the inclusion.  What is already proved in the
workspace is `Work.Modulus.greenPeriodHom_two_pi_zmultiples`:

  `γ ∈ ker j  ⟹  ∃ k : ℤ, P γ = k · 2π`

(the `2π i Res = -2π` computation at the pole, by Sard + Stokes on an extension disc of `γ` to `X`,
formalised through the branch-bundle covering of `X`).  Two things are still missing.

**(1) The winding homomorphism `W : π₁(U) →+ ℤ` (degree theory of maps to `ℂ* ≃ S¹`).**
`W` is the "linking number with the puncture `x₀`": on a small positively oriented circle around
`x₀` in the chart at `x₀` it takes the value `1`, and it is built from a nowhere-vanishing
continuous linking map `ℓ : U → ℂ*` (the normalised chart coordinate near `x₀`).  Formally, one
needs `deg : (Y → ℂ)`-nowhere-zero ⟶ `Hom (π₁ Y) ℤ` (the degree of a map to `S¹`, equivalently
`π₁(ℂ*) ≅ ℤ`, with the class of `t ↦ exp (2π i t)` corresponding to `1`), natural under composition,
and the computation that on a loop inside the chart at `x₀` which is a positively oriented circle
the degree of `c` is `1`.

**(2) The matching statement.** For `γ ∈ ker j` (a loop of `U` that is null-homotopic in `X`), the
integer of `greenPeriodHom_two_pi_zmultiples` is exactly `W γ`: the flux of `⋆dE` across an
extension disc of `γ` is `-2π` times the *local degree* of that extension at `x₀`, and that local
degree is the winding number of `γ` about `x₀`, i.e. `W γ`.

Given (1) and (2), `P - 2π W` kills `ker j`, hence descends to `π₁(X)`, where it vanishes by the
challenge hypothesis `Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)` — provided one can
transport a homomorphism killing `ker j` to a homomorphism of `π₁(X)`; since `ℝ` is a divisible
(hence injective) `ℤ`-module it suffices that the subgroup `j '' π₁(U)` be *all* of `π₁(X)`, which
is the standard fact that a loop on a surface can be pushed off a point (dimension ≥ 2).
Then `P = 2π W`, so `P` is integer-valued, and the modulus exists.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The requested modulus, from an integer-valued period homomorphism.**

If at *every* base point `u` of the punctured surface `U = X ∖ {x₀}` the period homomorphism
`Work.Modulus.greenPeriodHom hE u : Additive (π₁(U,u)) →+ ℝ` of the unit-pole Green function `E`
factors as `2π` times an *integer-valued* homomorphism `W u : Additive (π₁(U,u)) →+ ℤ`, then `E`
has a holomorphic modulus `Φ` with a log pole at `x₀` and `‖Φ x‖ = exp (-(E x))` off `x₀`.

The proof is the chapter of `Work.Modulus`: the factorisation is exactly the hypothesis of
`Work.Modulus.hasTrivialModulusMonodromy_of_periods` (all periods multiples of `2π`), which
produces a single-valued holomorphic `Φ` with `‖Φ x‖ = exp (-(E x))` and `Φ x ≠ 0` off the pole;
`Work.Modulus.poleOrderModulus_of_unitGreen` then identifies the vanishing order at `x₀` as
`Submission.HasLogPoleAt`.  No topological hypothesis on `X` is used here: everything is contained
in the factorisation.  (The factorisation at a single base point implies the one at all others by
conjugating loops, a real base-point-change statement for `greenPeriodHom`.) -/
theorem unitGreen_modulus_of_integerValuedPeriods {x₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) x₀ E)
    (hW : ∀ u : Work.Modulus.puncturedOpens x₀,
      ∃ W : Additive (FundamentalGroup (Work.Modulus.puncturedOpens x₀) u) →+ ℤ,
        ∀ γ : Additive (FundamentalGroup (Work.Modulus.puncturedOpens x₀) u),
          Work.Modulus.greenPeriodHom hE u γ = (W γ : ℝ) * (2 * Real.pi)) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt x₀ Φ ∧
      ∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  choose W hW' using hW
  obtain ⟨Φ, hhol, hne, hmod⟩ :=
    Work.Modulus.hasTrivialModulusMonodromy_of_periods (z₀ := x₀) hE
      (fun u γ => ⟨W u (Additive.ofMul γ), by
        rw [hW' u (Additive.ofMul γ)]⟩)
  exact ⟨Φ, hhol, Work.Modulus.poleOrderModulus_of_unitGreen hE hhol hne hmod, hmod⟩

end Work.SimplyConnected.ABS
