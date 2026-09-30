/-
# The function-field dictionary of an affine chart

For an integral scheme `X` and a nonempty affine open `U ⊆ X`, the function field `K(X)` is the
fraction field of the coordinate ring `Γ(X,U)`.  Specialised to the curve `C` and its base
changes this is the "chart dictionary" used by the affine-chart analysis of specialisation of
linear equivalence:

* `K(C_F) = Frac(Γ(C_F, W_F))` and, by `Work.SpecLin.Chart.sectionsTensorEquiv`,
  `Γ(C_F, W_F) ≅ Γ(C,W) ⊗_K F`;
* `K(C_κ) = Frac(Γ(C_κ, W_κ))` and `Γ(C_κ, W_κ) ≅ Γ(C,W) ⊗_K κ = (Γ(C,W) ⊗_K R) ⧸ P`.

Together with `IsAffineOpen.isLocalization_stalk` this turns `Scheme.ord` at a place of the
chart into the valuation of the localisation of the coordinate ring at the corresponding prime.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Work.SpecLin.Alt

/-- **The function field of an integral scheme is the fraction field of any nonempty affine
open subscheme.**

Proof: the generic point of `X` lies in `U`, its `IsAffineOpen.primeIdealOf` is the zero ideal,
and `IsAffineOpen.isLocalization_stalk` exhibits the stalk at the generic point (i.e. the
function field) as the localisation of `Γ(X,U)` at that (zero) prime, i.e. as the fraction
field. -/
theorem isFractionRing_functionField {X : AlgebraicGeometry.Scheme} [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  have hmem : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hpid : hU.primeIdealOf (⟨genericPoint X, hmem⟩ : ↥U) = (⊥ : PrimeSpectrum Γ(X, U)) := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  have hM : (⊥ : Ideal Γ(X, U)).primeCompl = nonZeroDivisors Γ(X, U) := by
    ext x
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  have hloc : IsLocalization ((⊥ : Ideal Γ(X, U)).primeCompl) X.functionField := by
    have h := hU.isLocalization_stalk (⟨genericPoint X, hmem⟩ : ↥U)
    rw [hpid] at h
    exact h
  rw [hM] at hloc
  exact hloc

end Work.SpecLin.Alt
