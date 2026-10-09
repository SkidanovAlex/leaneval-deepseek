import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.PTdualControl.detectorDescent_algebra
import Submission.Work.SSGRoute.PTdualControl.place_ramification_descent
import Submission.Work.SSGRoute.sylow_in_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-change descent for the unramified detector `C6`

`Work.Sha2Lib.unramifiedDetector` is stated for an arbitrary finite Galois extension `K/k` and
carries **no** hypothesis `μ_p ⊆ K`.  Every arithmetic route to `C6` on disk (the Kummer and
Shapiro/Grünwald routes, `Work.SSGRoute.E7cC.*` / `Work.Sha2Lib.*`) performs Kummer theory over
`K` and therefore needs a primitive `p`-th root of unity in `K`.  This file supplies the *descent*
that recovers the general statement from the `ζ_p ∈ K` case:

    (`C6` for `K' = K(ζ_p)` and the module `res_{K'/K} M`)  ⟹  (`C6` for `K` and `M`),

using only `p ∤ [K' : K]` (which holds for `K' = K(ζ_p)` because `[K(ζ_p) : K] ∣ p - 1`).

The proof is a transport of the data produced by the detector over `K'`:

* the level `L ⊇ K'` is viewed as a level over `K` (`restrictField`), and the place `q'' | w'`
  is viewed as a place over `w` (`place_ramification_descent` also gives `p ∤ e(q''|q)`);
* the detection pairing is transported by `levelPair_inflation` (the algebraic half);
* the detecting class over `D_w` is the *inflation* of the class over `D_{w'}`: every nonzero
  `φ ∈ Ext¹_{D_w}(res M, ℤ)` is `δ μ` for a nonzero functional `μ` (`exists_divRep_of_ext_nonzero_aux`),
  and inflating along `D_{w'} →* D_w` produces `δ (res μ)`, which is nonzero by `extDelta_ne_zero`.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

section RestrictField

/-- **A level over `K'` viewed as a level over `K`.**

For a tower of fields `k ⊆ K ⊆ K' ⊆ Ω` and an intermediate field `L` of `Ω/K'`, the same subset is
an intermediate field of `Ω/K`: the `K`-algebra structure is the composite
`K → K' → L`.  The underlying type is unchanged, so all the `NumberField`, `FiniteDimensional`
and `IsGalois` instances transfer definitionally. -/
def restrictField (k K K' Ω : Type) [Field k] [Field K] [Field K'] [Field Ω]
    [Algebra k K] [Algebra k K'] [Algebra k Ω] [Algebra K K'] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower k K K'] [IsScalarTower k K Ω] [IsScalarTower k K' Ω] [IsScalarTower K K' Ω]
    (L : IntermediateField K' Ω) : IntermediateField K Ω where
  carrier := L
  mul_mem' := L.mul_mem'
  one_mem' := L.one_mem'
  add_mem' := L.add_mem'
  zero_mem' := L.zero_mem'
  inv_mem' := L.inv_mem'
  algebraMap_mem' := fun x => by
    rw [IsScalarTower.algebraMap_apply K K' Ω]
    exact L.algebraMap_mem (algebraMap K K' x)

@[simp] theorem restrictField_coe (k K K' Ω : Type) [Field k] [Field K] [Field K'] [Field Ω]
    [Algebra k K] [Algebra k K'] [Algebra k Ω] [Algebra K K'] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower k K K'] [IsScalarTower k K Ω] [IsScalarTower k K' Ω] [IsScalarTower K K' Ω]
    (L : IntermediateField K' Ω) :
    ((restrictField k K K' Ω L : IntermediateField K Ω) : Set Ω) = L := rfl

end RestrictField

end Work.SSGRoute.PTdualControl
