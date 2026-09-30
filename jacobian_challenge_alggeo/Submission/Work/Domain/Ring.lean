/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ring lemma behind the domain engine (area DM, part 2)

Let `R` be an integrally closed domain with fraction field `K`, and let `S` be a finite `R`-algebra
which embeds into `K` as an `R`-algebra.  Then `R → S` is surjective: every element of `S` is
integral over `R` (finiteness) and lies in `K = Frac R`, hence lies in `R`.

This is the algebraic heart of the extension theorem for rational maps: a finite birational
morphism onto a normal base is an isomorphism.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Domain

/-- If `S` is a finite `R`-algebra with an `R`-algebra embedding into the fraction field of the
integrally closed domain `R`, then `R → S` is surjective. -/
theorem algebraMap_surjective_of_finite_of_isIntegrallyClosed
    {R S K : Type u} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [Module.Finite R S] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (hR : IsIntegrallyClosed R) (φ : S →ₐ[R] K) (hφ : Function.Injective φ) :
    Function.Surjective (algebraMap R S) := by
  intro s
  have hint : IsIntegral R (φ s) := (Algebra.IsIntegral.of_finite R S).isIntegral s |>.map φ
  obtain ⟨r, hr⟩ := hR.algebraMap_eq_of_integral hint
  exact ⟨r, hφ (by rw [φ.commutes, hr])⟩

end Work.Domain
