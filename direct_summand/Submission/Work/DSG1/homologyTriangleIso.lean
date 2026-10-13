import Mathlib

namespace Work.DSG1

open CategoryTheory Limits Pretriangulated

set_option maxHeartbeats 800000
-- `Mono` and `Epi` are propositions used as type class instances below.
set_option linter.style.haveILetI false

/-- In a distinguished triangle of the bounded below derived category whose first object has
vanishing homology in degrees `i` and `i+1`, the map induced by the second morphism on the `i`-th
homology is an isomorphism. -/
theorem homologyTriangleIso {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {T : Triangle (DerivedCategory.Plus C)} (hT : T ∈ distTriang _) (i : ℤ)
    (h₁ : IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj T.obj₁))
    (h₂ : IsZero ((DerivedCategory.Plus.homologyFunctor C (i + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor C i).map T.mor₂) := by
  -- `DerivedCategory.Plus.homologyFunctor C i` is, definitionally, the degree `i` term of the
  -- shift sequence attached to `DerivedCategory.Plus.homologyFunctor C 0`, so the long exact
  -- sequence of the distinguished triangle `T` is available for it.
  let F0 := DerivedCategory.Plus.homologyFunctor C 0
  -- The map `H^i(obj₂) ⟶ H^i(obj₃)` is injective: it is the second map of the exact complex
  -- whose first map `H^i(obj₁) ⟶ H^i(obj₂)` has zero source.
  haveI hmono : Mono ((DerivedCategory.Plus.homologyFunctor C i).map T.mor₂) := by
    have h : Mono ((F0.shift i).map T.mor₂) := by
      rw [F0.homologySequence_mono_shift_map_mor₂_iff T hT i]
      exact h₁.eq_of_src _ _
    exact h
  -- It is also surjective: it is the first map of the exact complex whose second map
  -- `H^i(obj₃) ⟶ H^{i+1}(obj₁)` has zero target.
  haveI hepi : Epi ((DerivedCategory.Plus.homologyFunctor C i).map T.mor₂) := by
    have h : Epi ((F0.shift i).map T.mor₂) := by
      rw [F0.homologySequence_epi_shift_map_mor₂_iff T hT i (i + 1) rfl]
      exact h₂.eq_of_tgt _ _
    exact h
  exact isIso_of_mono_of_epi _

end Work.DSG1
