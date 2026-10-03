import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

/-!
# Exactness of the functor `X ↦ A ⊗[K] X` (diagonal `K[G]`-structure)

Jaikin-Zapirain--Linton, Lemma 5.2 (2). The functor
`diagTensor A : ModuleCat (K[G]) ⥤ ModuleCat (K[G])`, `X ↦ A ⊗[K] X` (with the
diagonal `K[G]`-module structure), is exact.

The point is that `K` is a *field*: the endofunctor `ModuleCat K ⥤ ModuleCat K`
given by `X ↦ A ⊗[K] X` is exact (`Module.Flat.lTensor_exact`, every `K`-module
being free, hence flat). Exactness of a short complex of `K[G]`-modules is read on
the underlying `K`-linear maps (`ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`),
and on the underlying `K`-modules `diagTensor A` acts by `LinearMap.lTensor A`
(the diagonal structure only remembers the diagonal action of `K[G]` on the
tensor product; it does not change the underlying `K`-linear maps). Hence
`diagTensor A` sends an exact complex to an exact complex, which is exactly
`PreservesHomology` (`Functor.preservesHomology_of_map_exact`).
-/

namespace Work.ORHomAlg.JL52

set_option linter.style.haveILetI false

open CategoryTheory
open scoped TensorProduct

universe u

/-- The functor `X ↦ A ⊗[K] X` (with the diagonal `K[G]`-module structure) is exact. -/
theorem diagTensor_preservesHomology (K : Type u) [Field K] (G : Type u) [Group G]
    (A : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) A).PreservesHomology := by
  -- Over a field, every module is free, hence flat: tensoring with `A` is exact.
  haveI : Module.Free K A := Module.Free.of_divisionRing K A
  -- It suffices to check exactness of short complexes.
  refine CategoryTheory.Functor.preservesHomology_of_map_exact _ (fun S hS => ?_)
  -- Read exactness on the underlying functions (`K`-linear maps).
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  -- `diagTensor A` acts on the underlying functions by `LinearMap.lTensor A`, so the
  -- exactness of `S` transports across `A ⊗[K] -` by flatness of `A`.
  exact Module.Flat.lTensor_exact A hS

end Work.ORHomAlg.JL52
