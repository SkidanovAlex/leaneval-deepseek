import Mathlib

/-!
# Vanishing of `N ⊗[A] A[1/g]` implies vanishing of `N ⊗[A] Frac A`

Let `A` be a domain, `g ≠ 0` and `N` an `A`-module.  If the extension of scalars of `N` along
`A → A[1/g] = Localization.Away g` vanishes, then so does the extension of scalars of `N` along
`A → Frac A = FractionRing A`.

Mathematically this is the trivial observation that `A[1/g]` is an `A`-subalgebra of `Frac A`
(here one uses `g ≠ 0`, i.e. `g` is a non-zero-divisor, so that `g` becomes invertible in the
fraction field), hence

`N ⊗[A] Frac A ≅ (N ⊗[A] A[1/g]) ⊗[A[1/g]] Frac A`,

which vanishes because it is a tensor product of the vanishing `N ⊗[A] A[1/g]` with something.

Formally, the isomorphism of base changes across a composite of ring homomorphisms is Mathlib's
`ModuleCat.extendScalarsComp`, and the "vanishing is preserved" step uses that a subsingleton
module tensored with anything is subsingleton (`TensorProduct.uniqueRight`).  The only extra
ingredient is that `ModuleCat.extendScalars` of equal ring homomorphisms gives isomorphic
objects, which is `extendScalars_congr` below.
-/

namespace Work.DSEQ0

universe u

open CategoryTheory Limits

set_option linter.style.haveILetI false

/-- Extension of scalars along equal ring homomorphisms gives isomorphic objects: after
substituting the equality, the two functors are syntactically identical. -/
noncomputable def extendScalars_congr {R S : Type u} [CommRing R] [CommRing S] {f f' : R →+* S}
    (h : f = f') (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj M ≅ (ModuleCat.extendScalars f').obj M := by
  subst h
  exact Iso.refl _

theorem isZero_extendScalars_away (A : Type u) [CommRing A] [IsDomain A] (g : A) (hg0 : g ≠ 0)
    (N : ModuleCat.{u} A)
    (h : CategoryTheory.Limits.IsZero
      ((ModuleCat.extendScalars (algebraMap A (Localization.Away g))).obj N)) :
    CategoryTheory.Limits.IsZero
      ((ModuleCat.extendScalars (algebraMap A (FractionRing A))).obj N) := by
  -- `g ≠ 0` in a domain means that `g` is a non-zero-divisor, hence invertible in `Frac A`.
  have hg : IsUnit ((algebraMap A (FractionRing A)) g) := by
    have hmem : g ∈ nonZeroDivisors A := by
      rw [mem_nonZeroDivisors_iff_ne_zero]; exact hg0
    exact IsLocalization.map_units (FractionRing A) ⟨g, hmem⟩
  -- The canonical ring homomorphism `A[1/g] →+* Frac A`, from the universal property of
  -- localisation away from `g`.
  let φ : Localization.Away g →+* FractionRing A :=
    IsLocalization.Away.lift (R := A) (S := Localization.Away g) (P := FractionRing A) g hg
  -- `N ⊗[A] Frac A ≅ (N ⊗[A] A[1/g]) ⊗[A[1/g]] Frac A` and the latter vanishes.
  have h₂ : CategoryTheory.Limits.IsZero
      ((ModuleCat.extendScalars (φ.comp (algebraMap A (Localization.Away g)))).obj N) := by
    have hY : CategoryTheory.Limits.IsZero
        ((ModuleCat.extendScalars φ).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away g))).obj N)) := by
      -- A subsingleton module tensored with anything is subsingleton.
      haveI hsub : Subsingleton
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away g))).obj N) :=
        ModuleCat.subsingleton_of_isZero h
      haveI : Unique ((ModuleCat.extendScalars φ).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away g))).obj N)) :=
        TensorProduct.uniqueRight
      exact ModuleCat.isZero_of_subsingleton _
    exact CategoryTheory.Limits.IsZero.of_iso hY
      ((ModuleCat.extendScalarsComp (algebraMap A (Localization.Away g)) φ).app N)
  -- Finally `φ ∘ (A → A[1/g]) = (A → Frac A)` by the universal property of localisation.
  have heq : algebraMap A (FractionRing A) = φ.comp (algebraMap A (Localization.Away g)) :=
    (IsLocalization.Away.lift_comp (R := A) (S := Localization.Away g)
      (P := FractionRing A) g hg).symm
  exact CategoryTheory.Limits.IsZero.of_iso h₂ (extendScalars_congr heq N)

end Work.DSEQ0
