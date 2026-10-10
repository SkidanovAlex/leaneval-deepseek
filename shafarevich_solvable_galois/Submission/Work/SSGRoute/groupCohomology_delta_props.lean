import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Properties of the connecting map `δ` of a short exact sequence of representations

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `Coeff`-linear `G`-representations, the
connecting homomorphism `δⁿ : Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)` of the long exact cohomology sequence is

* injective as soon as `Hⁿ(G, X₂)` is a subsingleton, and
* surjective as soon as `Hⁿ⁺¹(G, X₂)` is a subsingleton.

Both statements are immediate from exactness of the long exact cohomology sequence, which Mathlib
records as `groupCohomology.mapShortComplex₃_exact` (exactness at `Hⁿ(G, X₃)`) and
`groupCohomology.mapShortComplex₁_exact` (exactness at `Hⁿ⁺¹(G, X₁)`), together with the snake
lemmas `groupCohomology.mono_δ_of_isZero` / `groupCohomology.epi_δ_of_isZero`.

Concretely, triviality of `Hⁿ(G, X₂)` forces `Hⁿ(G, X₂) ⟶ Hⁿ(G, X₃)` to be the zero map, so
`ker δⁿ` is trivial; triviality of `Hⁿ⁺¹(G, X₂)` forces `Hⁿ⁺¹(G, X₁) ⟶ Hⁿ⁺¹(G, X₂)` to be the
zero map, so `im δⁿ` is everything.
-/

namespace Work.SSGRoute

open CategoryTheory

theorem groupCohomology_delta_props (G : Type) [Group G]
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (n : ℕ) :
    (Subsingleton (groupCohomology S.X₂ n) →
      ∀ (y : groupCohomology S.X₃ n),
        (groupCohomology.δ hS n (n + 1) rfl).hom y = 0 → y = 0) ∧
    (Subsingleton (groupCohomology S.X₂ (n + 1)) →
      ∀ (z : groupCohomology S.X₁ (n + 1)),
        ∃ (y : groupCohomology S.X₃ n), (groupCohomology.δ hS n (n + 1) rfl).hom y = z) := by
  constructor
  · -- Injectivity of `δⁿ` when `Hⁿ(G, X₂)` vanishes: `δⁿ` is a monomorphism.
    intro hsub y hy
    have hZ : CategoryTheory.Limits.IsZero (groupCohomology S.X₂ n) :=
      @ModuleCat.isZero_of_subsingleton SSGRoute.PTExt.Coeff _ (groupCohomology S.X₂ n) hsub
    have hmono : Mono (groupCohomology.δ hS n (n + 1) rfl) :=
      groupCohomology.mono_δ_of_isZero hS n hZ
    have hinj : Function.Injective (groupCohomology.δ hS n (n + 1) rfl).hom :=
      (ModuleCat.mono_iff_injective _).mp hmono
    exact hinj (by simpa using hy)
  · -- Surjectivity of `δⁿ` when `Hⁿ⁺¹(G, X₂)` vanishes: `δⁿ` is an epimorphism.
    intro hsub z
    have hZ : CategoryTheory.Limits.IsZero (groupCohomology S.X₂ (n + 1)) :=
      @ModuleCat.isZero_of_subsingleton SSGRoute.PTExt.Coeff _ (groupCohomology S.X₂ (n + 1)) hsub
    have hepi : Epi (groupCohomology.δ hS n (n + 1) rfl) :=
      groupCohomology.epi_δ_of_isZero hS n hZ
    have hsurj : Function.Surjective (groupCohomology.δ hS n (n + 1) rfl).hom :=
      (ModuleCat.epi_iff_surjective _).mp hepi
    exact hsurj z

end Work.SSGRoute
