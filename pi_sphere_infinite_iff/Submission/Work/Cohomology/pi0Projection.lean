import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.singularCohomology_zero

/-!
# The component projection `0`-cochain of a space with two components

For a topological space `T` and a connected component `c` of `T` (an element of `π₀`), the
**component projection** is the `0`-cochain which is `1` on the `0`-simplices lying in `c` and `0`
on all others.  It is a `0`-cocycle, because it factors through the cokernel `∐_{π₀ T} ℤ` of the
first differential (this is the same construction as the augmentation of
`Work.Cohomology.singularCohomology_zero`).

This is the general form of the "indicator" cochains of the equatorial band
(`Work.Cohomology.indicMor`, `Work.Cohomology.lambdaMor`): the two-island decompositions of those
files are replaced here by an arbitrary component `c : π₀ T`.

* `Work.Cohomology.pi0ProjMor` — the component projection, as a morphism `C₀(T) ⟶ ℤ`;
* `Work.Cohomology.pi0Proj` — the underlying cochain;
* `Work.Cohomology.pi0ProjMor_comp_d`, `Work.Cohomology.pi0Proj_cocycle` — it is a cocycle.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- The **component projection** onto a component `c ∈ π₀ T`: the morphism `C₀(T) ⟶ ℤ` which is
`1` on the free generators in `c` and `0` on the others.  It is well defined because the first
differential of the chain complex has image exactly the "sum zero" subgroup, so that it factors
through `coker d₁ = ∐_{π₀ T} ℤ`. -/
noncomputable def pi0ProjMor (T : TopCat) (c : SSet.π₀ (TopCat.toSSet.obj T)) :
    ((TopCat.toSSet.obj T).chainComplex (ModuleCat.of ℤ ℤ)).X 0 ⟶ ModuleCat.of ℤ ℤ := by
  classical
  exact SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj T) (ModuleCat.of ℤ ℤ) ≫
    Sigma.desc (fun d : SSet.π₀ (TopCat.toSSet.obj T) =>
      if d = c then 𝟙 (ModuleCat.of ℤ ℤ) else 0)

/-- The component projection, as a linear functional on the `0`-chains. -/
noncomputable def pi0Proj (T : TopCat) (c : SSet.π₀ (TopCat.toSSet.obj T)) :
    Cochain ℤ (TopCat.toSSet.obj T) 0 :=
  (pi0ProjMor T c).hom

/-- The component projection kills the first differential. -/
theorem pi0ProjMor_comp_d (T : TopCat) (c : SSet.π₀ (TopCat.toSSet.obj T)) :
    ((TopCat.toSSet.obj T).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫ pi0ProjMor T c = 0 := by
  classical
  rw [show pi0ProjMor T c = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj T)
      (ModuleCat.of ℤ ℤ) ≫
      Sigma.desc (fun d : SSet.π₀ (TopCat.toSSet.obj T) =>
        if d = c then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl]
  rw [← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]

/-- The component projection is a `0`-cocycle. -/
theorem pi0Proj_cocycle (T : TopCat) (c : SSet.π₀ (TopCat.toSSet.obj T)) :
    cochainDiff ℤ (TopCat.toSSet.obj T) (pi0Proj T c) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (pi0ProjMor_comp_d T c)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact h

end

end Work.Cohomology
