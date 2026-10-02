import Mathlib
import Submission.Work.Cohomology.Pullback
import Submission.Work.RatHurewicz.Excision
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Injectivity of the singular chain map induced by an injective continuous map

If `f : X → Y` is an injective continuous map, then the induced chain map
`C_*(X; ℚ) ⟶ C_*(Y; ℚ)` is degreewise injective.

The proof is categorical: an injective continuous map is a monomorphism in `TopCat`
(`TopCat.mono_iff_injective`), and the singular chain complex functor
`(AlgebraicTopology.singularChainComplexFunctor R).obj R` preserves monomorphisms
(Mathlib's instance for `singularChainComplexFunctor`), so the induced chain map is a
monomorphism of chain complexes, hence so is each of its components, and a monomorphism of
`R`-modules is an injective map (`ModuleCat.mono_iff_injective`).

This is the `ℚ`-coefficient, general injective map version of the subspace inclusion
statement `Work.StemsB.injective_chainMap_subtypeIncl_ring` (the argument in fact works over any
commutative ring, but the statement is the `ℚ` one the caller needs).
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology

namespace Work.StemsB

theorem injective_chainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : Function.Injective f) (j : ℕ) :
    Function.Injective ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)).f j) := by
  -- `f` is a monomorphism of topological spaces.
  haveI hfmono : Mono (TopCat.ofHom f) := (TopCat.mono_iff_injective _).mpr hf
  -- The singular chain complex functor preserves monomorphisms, so the chain map is a
  -- monomorphism of chain complexes.
  haveI hchain : Mono (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)) :=
    Functor.map_mono
      (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ))) (TopCat.ofHom f)
  -- Hence its `j`-th component is a monomorphism of `ℚ`-modules, i.e. an injective map.
  haveI hcomp : Mono ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)).f j) :=
    inferInstance
  exact (ModuleCat.mono_iff_injective _).mp hcomp

end Work.StemsB
