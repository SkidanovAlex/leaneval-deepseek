import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_H2_lift_defs
import Submission.Work.SSGRoute.PT.isOpen_setOf_inv_smul_eq
import Submission.Work.SSGRoute.PT.continuous_shapiroCoordinates_subtype
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- **Local constancy of the Shapiro lift.**

Let `G` be a topological group, `U ≤ G` an open subgroup of finite index, `M` a
`U`-module and `a : U × U → M` a locally constant `2`-cochain on `U` (with the subspace topology
on `U × U`).  Then the Shapiro lift

  `shapiroLift U a (g, h) = (x ↦ coord x • a (A g (xU), A h (g⁻¹ • xU))) : Coind_U^G M`

is locally constant as a function of `(g, h) ∈ G × G`.

The proof is a finite-intersection argument.  For a fixed coset `C : G ⧸ U`, the point

  `z_C (p) = (A p.1 C, A p.2 (p.1⁻¹ • C)) ∈ U × U`

depends continuously on `p ∈ G × G` (`continuous_shapiroCoordinates_subtype`), so by local
constancy of `a` at `z_C (p₀)` there is an open neighbourhood of `p₀` on which the value
`a (z_C (·))` is constant.  Intersecting over the finitely many cosets `C` (finite index of `U`)
gives an open neighbourhood `W` of `p₀` on which `p ↦ a (z_C p)` is constant for *every* coset
`C`, hence on which `(shapiroLift U a p) x = (shapiroLift U a p₀) x` for every `x ∈ G` (the
`coord x`-factor is common to both sides).  Since elements of `Coind_U^G M` are determined by
their underlying functions, `shapiroLift U a` is constant on `W`. -/
theorem isLocallyConstant_shapiroLift {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (a : U × U → M) (ha : Work.AbsoluteKummer.IsLocallyConstant a) :
    Work.AbsoluteKummer.IsLocallyConstant (Work.SSGRoute.PT.shapiroLift U a) := by
  classical
  intro p₀
  obtain ⟨g₀, h₀⟩ := p₀
  -- Local constancy of `a` around the point of `U × U` attached to each coset
  choose V hV hmem hconst using fun C : G ⧸ U =>
    ha (Shapiro.A 0 G U g₀ C, Shapiro.A 0 G U h₀ (g₀⁻¹ • C))
  -- the finite intersection of the corresponding open neighbourhoods of `p₀`
  refine ⟨⋂ C : G ⧸ U, {p : G × G |
      ((Shapiro.A 0 G U p.1 C, Shapiro.A 0 G U p.2 (p.1⁻¹ • C)) : U × U) ∈ V C},
    ?_, ?_, ?_⟩
  · refine isOpen_iInter_of_finite fun C => ?_
    exact (hV C).preimage (continuous_shapiroCoordinates_subtype U hU C)
  · exact Set.mem_iInter.mpr fun C => hmem C
  · rintro ⟨g, h⟩ hp
    apply Subtype.ext
    funext x
    rw [shapiroLift_apply, shapiroLift_apply]
    rw [hconst (x : G ⧸ U)
      (Shapiro.A 0 G U g (x : G ⧸ U), Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))
      (Set.mem_iInter.mp hp (x : G ⧸ U))]

end

end Work.SSGRoute.PT
