/-
# Instance-shape transfers for the branch sum

For `K = k(h) ⊆ L = K(C) ⊆ N` (N a finite Galois extension of `K`) the `SMul`/`Module`
structure on `N` over `K` has two candidate instances:

* the *ambient* one, `IntermediateField.instModuleSubtypeMem K`, which only needs `Module L N`
  and is picked by typeclass search as soon as `[Algebra L N]` is in scope at the moment the
  binder `[FiniteDimensional K N]` is elaborated;
* the *canonical* one, `Algebra.toModule` of the local hypothesis `[Algebra ↥K N]`.

Given `hKE : algebraMap ↥K N = (algebraMap L N).comp (algebraMap ↥K L)` the two `smul` functions
coincide, so the two `Module` structures are equal by `Module.ext` (they have the same `SMul` and
all remaining fields are proofs), and `FiniteDimensional` (a `Prop`) transfers.  This file
provides that transfer, fully pinned so that no typeclass search is involved in the statement.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.KeyLemma.Curve.BranchSum

universe u

set_option linter.style.haveILetI false

/-- **Transfer of `FiniteDimensional` from the ambient `Module ↥K N` to the canonical one.**
All instances are pinned, so the caller controls exactly which structures are meant. -/
theorem finiteDimensional_canon {k : Type u} [Field k] {L : Type u} [Field L] (akL : Algebra k L)
    (K : IntermediateField k L) {N : Type u} [Field N] [algK : Algebra ↥K N] [algL : Algebra L N]
    (hKE : @algebraMap ↥K N _ _ algK
      = (@algebraMap L N _ _ algL).comp
        (@algebraMap ↥K L _ _ (IntermediateField.instAlgebraSubtypeMem K)))
    (finKN : @FiniteDimensional ↥K N _ _
      (@IntermediateField.instModuleSubtypeMem k L _ _ akL N _
        (@Algebra.toModule L N _ _ algL) K)) :
    @FiniteDimensional ↥K N _ _ (@Algebra.toModule ↥K N _ _ algK) := by
  have hmod : (@IntermediateField.instModuleSubtypeMem k L _ _ akL N _
        (@Algebra.toModule L N _ _ algL) K)
      = (@Algebra.toModule ↥K N _ _ algK) := by
    apply Module.ext
    funext x n
    -- the ambient `smul`
    rw [show (@SMul.smul ↥K N (@IntermediateField.instSMulSubtypeMem k L _ _ akL N
        (@Algebra.toSMul L N _ _ algL) K) x n : N) = (x : L) • n from rfl]
    -- the canonical `smul`
    rw [show (@SMul.smul ↥K N (@Algebra.toSMul ↥K N _ _ algK) x n : N)
      = (@algebraMap ↥K N _ _ algK) x * n from Algebra.smul_def x n]
    -- the two values agree by `hKE`
    rw [Algebra.smul_def, congrFun (congrArg DFunLike.coe hKE) x]
    simp
  exact hmod ▸ finKN

end Work.KeyLemma.Curve.BranchSum
