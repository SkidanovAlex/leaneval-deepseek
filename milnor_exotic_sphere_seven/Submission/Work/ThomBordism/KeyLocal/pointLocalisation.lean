import Submission.Work.ThomBordism.someOpen_relCohMap_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# Localisation at a point (the pullback along an open neighbourhood)

A cohomology class of the pair `(X, X∖{x₀})` is *determined* by its restriction to any open
neighbourhood `U` of `x₀`: the pullback

  `H^n(X, X∖{x₀}) → H^n(U, U∖{x₀})`

along the inclusion `U ↪ X` is injective (in fact an isomorphism — excision, with `Z := X∖U` and
`A := X∖{x₀}`).  This is the tool that lets a *local* computation (performed in a chart
neighbourhood of `x₀`) conclude an equality of global classes relative to the point.

Proof: `Work.ThomBordism.relCohMap_subtypeIncl_injective` (the `relCohMap` spelling of
`Work.Cohomology.capRel_excision_isIso`) with `A := X∖{x₀}`, which is open because `X` is `T1`. -/
namespace Work.ThomBordism.KeyLocal

noncomputable section

/-- **Localisation at a point.**  For a `T1` space `X`, a point `x₀` and an open neighbourhood
`U ∋ x₀`, the pullback `H^n(X, X∖{x₀}) → H^n(U, U∖{x₀})` along the inclusion is injective. -/
theorem pointLocalisation_injective {X : Type} [TopologicalSpace X] [T1Space X] {x₀ : X}
    {U : Set X} (hU : IsOpen U) (hx : x₀ ∈ U) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
      ({y : ↥U | (y : X) ≠ x₀}) ({y : X | y ≠ x₀}) (fun y hy => hy) ℤ n)) := by
  have hA : IsOpen ({y : X | y ≠ x₀}) := isClosed_singleton.isOpen_compl
  have hcov : U ∪ {y : X | y ≠ x₀} = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : y = x₀
    · exact Or.inl (by rw [hy]; exact hx)
    · exact Or.inr hy
  exact relCohMap_subtypeIncl_injective U ({y : X | y ≠ x₀}) hU hA hcov n

end

end Work.ThomBordism.KeyLocal
