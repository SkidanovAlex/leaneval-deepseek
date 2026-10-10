import Mathlib.Algebra.MonoidAlgebra.Cardinal
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Submission.Work.SSGRoute.e0b_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

/-- `Rep Coeff G` is equivalent to `ModuleCat Coeff[G]`, and the latter has enough injectives;
transporting along the equivalence gives enough injectives for `Rep Coeff G`. -/
theorem enoughInjectives_rep (G : Type) [Group G] :
    CategoryTheory.EnoughInjectives (Rep.{0} SSGRoute.PTExt.Coeff G) :=
  CategoryTheory.EnoughInjectives.of_equivalence
    (Rep.toModuleMonoidAlgebra (k := SSGRoute.PTExt.Coeff) (G := G))

/-- **Effacement in `Rep Coeff G`.** Every representation embeds into an injective one whose
positive-degree cohomology (`groupCohomology`, equivalently the `Ext`-cohomology `extH`) vanishes.
This is the standard "effacing object": an injective object is acyclic for the left exact functor
`H⁰ = (-)^G`, hence has vanishing higher cohomology. -/
theorem exists_effacing_object (G : Type) [Group G] (A : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∃ (I : Rep.{0} SSGRoute.PTExt.Coeff G) (_ : CategoryTheory.Injective I)
      (ι : A ⟶ I), CategoryTheory.Mono ι ∧
      (∀ n : ℕ, 1 ≤ n → Subsingleton (groupCohomology I n)) ∧
      (∀ n : ℕ, 1 ≤ n → Subsingleton (SSGRoute.PTExt.extH I n)) := by
  have : CategoryTheory.EnoughInjectives (Rep.{0} SSGRoute.PTExt.Coeff G) :=
    enoughInjectives_rep G
  obtain ⟨P⟩ := CategoryTheory.EnoughInjectives.presentation A
  -- An injective object has vanishing positive `Ext`-cohomology.
  have hextH : ∀ n : ℕ, 1 ≤ n → Subsingleton (SSGRoute.PTExt.extH P.J n) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact Abelian.Ext.subsingleton_of_injective (SSGRoute.PTExt.unitRep G) P.J m
  refine ⟨P.J, P.injective, P.f, P.mono, ?_, hextH⟩
  -- `groupCohomology` agrees with `extH` through the Ext bridge.
  intro n hn
  exact Work.SSGRoute.Bridge.subsingleton_groupCohomology_of_subsingleton_extH n G P.J
    (hextH n hn)

end

end Work.SSGRoute
