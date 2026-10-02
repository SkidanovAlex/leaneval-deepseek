import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.sphereHomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Injectivity of the zeroth Mayer–Vietoris map when `U ∩ V` is path connected

Let `X` be a topological space and `U V ⊆ X`.  The first map of the Mayer–Vietoris sequence is

`mvLeft U V : C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V)`,

the pair of chain maps induced by the two inclusions `U ∩ V ↪ U` and `U ∩ V ↪ V`.  This file
proves that its induced map in degree `0`,

`H₀(U ∩ V) ⟶ H₀(U) ⊞ H₀(V)`,

is injective as soon as `U ∩ V` is path connected.

The argument is short because Mathlib computes degree-`0` singular homology
(`TopCat.singularHomology₀Iso`): the augmentation `ε X : H₀(X) ⟶ ℤ` is an isomorphism whenever
`X` is path connected (instance `IsIso (X.singularHomology₀ε R)` in
`Mathlib/AlgebraicTopology/SingularHomology/HomologyZero.lean`).  Since

* `mvLeft U V ≫ biprod.fst = chainMap ℤ (U ∩ V) U (inclUVU U V)` (`mvLeft_fst`), and
* the augmentation is natural, `homologyMap (chainMap ℤ Y Z f) 0 ≫ ε Z = ε Y`
  (`epsilonNaturality`),

the composite `homologyMap (mvLeft U V) 0 ≫ biprod.fst ≫ ε U` is the augmentation `ε (U ∩ V)`,
which is a monomorphism.  A composite `g ≫ f` which is mono has `g` mono
(`mono_of_mono_fac`), hence `homologyMap (mvLeft U V) 0` is mono, i.e. injective.

## Main result

* `mvLeft_zero_injective` — injectivity in degree `0` when `U ∩ V` is path connected.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

/-- `homologyMap (mvLeft U V) 0` followed by the first projection of the biproduct is the map
induced by the inclusion `U ∩ V ↪ U`. -/
lemma homologyMap_mvLeft_fst {X : TopCat} (U V : Set X) :
    HomologicalComplex.homologyMap (mvLeft U V) 0
        ≫ HomologicalComplex.homologyMap (biprod.fst
            (X := singularChains ℤ (TopCat.of ↥U))
            (Y := singularChains ℤ (TopCat.of ↥V))) 0
      = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U)
          (inclUVU U V)) 0 := by
  rw [← HomologicalComplex.homologyMap_comp, mvLeft_fst]

/-- **Injectivity of the zeroth Mayer–Vietoris map.**  If `U ∩ V` is path connected, then the map
`H₀(U ∩ V) ⟶ H₀(U) ⊞ H₀(V)` induced by `mvLeft` is injective. -/
theorem mvLeft_zero_injective {X : TopCat} (U V : Set X) [PathConnectedSpace ↥(U ∩ V)] :
    Function.Injective (HomologicalComplex.homologyMap (mvLeft U V) 0).hom := by
  -- The composite `mvLeft ≫ fst ≫ ε U` is the augmentation of `U ∩ V`, which is iso (hence mono)
  -- because `U ∩ V` is path connected; so `mvLeft` itself is mono.
  have hkey : HomologicalComplex.homologyMap (mvLeft U V) 0
        ≫ (HomologicalComplex.homologyMap (biprod.fst
              (X := singularChains ℤ (TopCat.of ↥U))
              (Y := singularChains ℤ (TopCat.of ↥V))) 0
            ≫ TopCat.singularHomology₀ε (TopCat.of ↥U) (ModuleCat.of ℤ ℤ))
      = TopCat.singularHomology₀ε (TopCat.of ↥(U ∩ V)) (ModuleCat.of ℤ ℤ) := by
    rw [← Category.assoc, homologyMap_mvLeft_fst,
      epsilonNaturality (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V)]
  haveI : Mono (TopCat.singularHomology₀ε (TopCat.of ↥(U ∩ V)) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  exact (ModuleCat.mono_iff_injective _).1 (mono_of_mono_fac hkey)

end Work.Cohomology
