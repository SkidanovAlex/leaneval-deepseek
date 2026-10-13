import Mathlib
import Submission.Work.DSF1.Sheaf.SSEBasic

/-!
# Lifting a section killed by `S.g` along `S.f`

For a short exact sequence `0 → X₁ →f X₂ →g X₃ → 0` of sheaves of `𝒪_X`-modules and any open
`V ⊆ X`, the sequence of abelian groups

`Γ(V, X₁) →f Γ(V, X₂) →g Γ(V, X₃)`

is exact in the middle: a section of `X₂` over `V` killed by `g` is in the image of `f`.  (Only the
middle exactness holds; surjectivity of `Γ(V, X₂) → Γ(V, X₃)` is false in general.)

The proof is the standard one, assembled from two facts about functors between abelian categories:

* `SheafOfModules.toSheaf X.ringCatSheaf`, the forgetful functor from sheaves of `𝒪_X`-modules to
  sheaves of abelian groups, preserves finite limits; by
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` it therefore carries a short exact
  sequence to a *left* exact sequence: `(S.map toSheaf).Exact` and `Mono ((S.map toSheaf).f)`.
* For a left exact short complex of sheaves of abelian groups on a topological space, the induced
  sequence on sections of an open is exact in the middle; this is
  `TopCat.Sheaf.sections_exact_of_left_exact` (Mathlib), whose proof is the usual one: local lifts
  coming from exactness of the sheaf sequence are compatible because `f` is a mono, hence glue by
  the sheaf condition.

Both `sectionsAt S.X V` and `sectionsMap S.s V` are *defined* as the value on sections of
`SheafOfModules.toSheaf X.ringCatSheaf`, so the two statements match definitionally.
-/

namespace Work.DSF1.Sheaf

universe u

theorem exists_lift_of_sectionsMap_eq_zero {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex (SheafOfModules X.ringCatSheaf))
    (hS : S.ShortExact) (V : X.Opens) (b : Work.DSF1.Sheaf.sectionsAt S.X₂ V)
    (hb : Work.DSF1.Sheaf.sectionsMap S.g V b = 0) :
    ∃ a : Work.DSF1.Sheaf.sectionsAt S.X₁ V, Work.DSF1.Sheaf.sectionsMap S.f V a = b := by
  have h := (CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (SheafOfModules.toSheaf X.ringCatSheaf)).mp inferInstance S hS
  exact TopCat.Sheaf.sections_exact_of_left_exact h.1 h.2 b hb

end Work.DSF1.Sheaf
