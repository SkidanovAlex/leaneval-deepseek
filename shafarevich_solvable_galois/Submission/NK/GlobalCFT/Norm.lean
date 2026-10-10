import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm of idèles

For a finite extension `L / K` of number fields, the norm `N_{L/K} : 𝕀 L → 𝕀 K` is defined
componentwise: for a place `v` of `K`,

`(N x)_v = ∏_{w | v} N_{L_w/K_v}(x_w)`,

the product of the local norms over the places `w` of `L` above `v`.  This file contains the
componentwise formula; the packaged homomorphism, its functoriality and the induced map on
idèle class groups are in `NK.GlobalCFT.NormGroup`.

## Main definitions

* `NK.GlobalCFT.Idele.normIdeleFun`: the componentwise formula.

## Main results

* `NK.GlobalCFT.Idele.normIdeleFun_ofInfinite`, `..._ofFinite`: the two cases.

The following are proved in the sibling modules `NK.GlobalCFT.Norm.*`:
* `globalCFT_normIdeleFun_mul`, `globalCFT_normIdeleFun_one`: multiplicativity;
* `globalCFT_localNorm_mem_localUnits`: a local unit has local-unit norm;
* `globalCFT_eventually_normIdeleFun_mem`: the formula lands in the restricted product.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The componentwise norm formula for idèles: at a place `v` of `K`, the product of the local
norms `N_{L_w/K_v}` over the places `w` of `L` above `v`. -/
noncomputable def normIdeleFun (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (x : Idele L) (v : Place K) :
    (Place.localField K v)ˣ :=
  match v with
  | Sum.inl w =>
      ∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) w).attach,
        letI : (w'.1 : InfinitePlace L).LiesOver w :=
          (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2
        Place.localNormInfinite w'.1 w (x (Place.ofInfinite w'.1))
  | Sum.inr q =>
      ∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) q).attach,
        Place.localNormFinite q'.1 q
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := q) (q := q'.1)).mp q'.2)
          (x (Place.ofFinite q'.1))

@[simp] theorem normIdeleFun_ofInfinite (x : Idele L) (w : InfinitePlace K) :
    normIdeleFun K L x (Place.ofInfinite w) =
      ∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) w).attach,
        letI : (w'.1 : InfinitePlace L).LiesOver w :=
          (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2
        Place.localNormInfinite w'.1 w (x (Place.ofInfinite w'.1)) := rfl

@[simp] theorem normIdeleFun_ofFinite (x : Idele L) (q : HeightOneSpectrum (𝓞 K)) :
    normIdeleFun K L x (Place.ofFinite q) =
      ∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) q).attach,
        Place.localNormFinite q'.1 q
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := q) (q := q'.1)).mp q'.2)
          (x (Place.ofFinite q'.1)) := rfl

end Idele

end NK.GlobalCFT
