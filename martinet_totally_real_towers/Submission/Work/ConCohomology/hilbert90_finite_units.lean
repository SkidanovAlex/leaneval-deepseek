/-
Copyright: the martinet_totally_real_towers team.

# Hilbert 90 for the units of a finite field extension

This module discharges Noether's generalization of Hilbert's Theorem 90 in the shape needed by
this chapter: for a finite extension of fields `L/K`, every `1`-cocycle
`a : Gal(L/K) → Additive Lˣ` (with the inhomogeneous cocycle condition
`a (σ * τ) = a σ + σ • a τ` of `Defs`) is a coboundary `a = d⁰β`.

Nothing here needs `L/K` to be Galois or separable: `Gal(L/K)` denotes the group of
`K`-algebra automorphisms of `L`, and Noether's argument (Dedekind's linear independence of the
automorphisms, then `β = (∑_τ f τ · τ z)⁻¹`) works verbatim for an arbitrary finite extension.
The general statement is already in Mathlib, in `Mathlib.RepresentationTheory.Homological.
GroupCohomology.Hilbert90`:

`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`

for `f : Gal(L/K) → Lˣ` with `IsMulCocycle₁ f := ∀ g h, f (g * h) = g • f h * f g`, and produces
`β : Lˣ` with `g • β / β = f g`.  All that is left is the translation between

* `Additive Lˣ` (additive notation, our `IsCocycle1`, our `d0Fun`), and
* `Lˣ` (multiplicative notation, `IsMulCocycle₁`, `IsMulCoboundary₁`).

Because `Lˣ` is *commutative* the two orderings of the cocycle condition agree, and the two
coboundary conditions are the same formula `g • β / β`; so the translation is the identity on
coefficients, `f := fun σ => (a σ).toMul`, and the witness `β` is simply `Additive.ofMul β`.
-/

import Mathlib
import Submission.Work.ConCohomology.GaloisUnits

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function

theorem hilbert90_finite_units {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : Gal(L/K) → Additive Lˣ) (ha : IsCocycle1 a) :
    ∃ β : Additive Lˣ, a = d0Fun (G := Gal(L/K)) β := by
  -- The same cocycle, written multiplicatively.  `Lˣ` is commutative, so the order of the two
  -- factors in the cocycle condition is immaterial.
  have hf : groupCohomology.IsMulCocycle₁ (fun σ : Gal(L/K) => (a σ).toMul) := by
    intro σ τ
    have h' := congrArg Additive.toMul (ha σ τ)
    simp only [toMul_add, toMul_smul_additiveUnits] at h'
    show (a (σ * τ)).toMul = σ • (a τ).toMul * (a σ).toMul
    rw [h', mul_comm]
  -- Noether's generalization of Hilbert 90 in Mathlib.
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (fun σ : Gal(L/K) => (a σ).toMul) hf
  -- `hβ σ : σ • β / β = (a σ).toMul`, which is exactly the statement that `a` is the coboundary
  -- of `β` in additive notation.
  refine ⟨Additive.ofMul β, ?_⟩
  funext σ
  apply Additive.toMul.injective
  have h := hβ σ
  simp only [d0Fun_apply, toMul_sub, toMul_smul_additiveUnits] at *
  rw [show Additive.toMul (Additive.ofMul β) = β from rfl]
  exact h.symm

end Work.ConCohomology
