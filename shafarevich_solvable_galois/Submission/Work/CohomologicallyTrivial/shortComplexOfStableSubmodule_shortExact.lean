import Mathlib.Tactic.Have
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Submission.Work.CohomologicallyTrivial.SubQuotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sub/quotient short complex of a stable submodule is short exact

For a representation `M : Rep k G` and a `G`-stable submodule `W ≤ M.V`, the short complex

`0 → W → M → M ⧸ W → 0`

built in `SubQuotDefs.lean` is short exact: the inclusion `W → M` is a mono, the projection
`M → M ⧸ W` is an epi, and the complex is exact in the middle (the kernel of the projection is
exactly the image of the inclusion).

The exactness is proved by applying the faithful forgetful functor
`Rep k G ⥤ ModuleCat k`, which preserves homology, and using the concrete description of
exactness of a short complex of modules.
-/

open CategoryTheory

namespace Work.CohomologicallyTrivial

theorem shortComplexOfStableSubmodule_shortExact {k : Type} [CommRing k] {G : Type} [Group G]
    (M : Rep k G) (W : Submodule k M.V) (hW : ∀ g : G, W ≤ Submodule.comap (M.ρ g) W) :
    (Work.CohomologicallyTrivial.shortComplexOfStableSubmodule M W hW).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- exactness in the middle
    let F : Rep k G ⥤ ModuleCat k := forget₂ (Rep k G) (ModuleCat k)
    refine (ShortComplex.exact_map_iff_of_faithful
      (S := shortComplexOfStableSubmodule M W hW) F).1 ?_
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ (x₂ : M.V), W.mkQ x₂ = 0 → ∃ (x₁ : W), W.subtype x₁ = x₂
    intro x₂ hx₂
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx₂
    exact ⟨⟨x₂, hx₂⟩, rfl⟩
  · -- the inclusion `W → M` is a mono
    refine (Rep.mono_iff_injective _).mpr ?_
    intro x y h
    exact Subtype.ext h
  · -- the projection `M → M ⧸ W` is an epi
    refine (Rep.epi_iff_surjective _).mpr ?_
    intro x
    exact Submodule.mkQ_surjective W x

end Work.CohomologicallyTrivial
