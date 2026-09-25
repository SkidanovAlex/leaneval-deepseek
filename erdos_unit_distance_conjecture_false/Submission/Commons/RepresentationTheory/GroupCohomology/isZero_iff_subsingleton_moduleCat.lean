import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# A `ℤ`-module is a zero object iff it is a subsingleton

For the category `ModuleCat ℤ` of `ℤ`-modules (i.e. abelian groups), being a zero object is
equivalent to the underlying type being a subsingleton.  This is the specialisation to `ℤ` of
`ModuleCat.isZero_iff_subsingleton`.
-/

namespace Commons.RepresentationTheory.GroupCohomology

theorem isZero_iff_subsingleton_moduleCat (X : ModuleCat ℤ) :
    CategoryTheory.Limits.IsZero X ↔ Subsingleton ↥X :=
  ModuleCat.isZero_iff_subsingleton

end Commons.RepresentationTheory.GroupCohomology