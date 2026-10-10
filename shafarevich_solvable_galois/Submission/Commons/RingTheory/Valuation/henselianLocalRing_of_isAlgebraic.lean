import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic
import Submission.Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
import Submission.Commons.RingTheory.Valuation.henselianLocalRing_of_unique_extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Henselianity passes to algebraic extensions of the base field

Let `V` be a Henselian valuation subring of a field `F`, let `K/F` be algebraic and let `vK` be a
valuation subring of `K` whose restriction to `F` is `V`.  Then `vK` is Henselian.

The proof uses the characterisation of Henselianity by uniqueness of the extension of the valuation
to a separable closure: it suffices to show that `vK` has a unique extension to the separable
closure `F'` of `K`.  An extension `W` of `vK` to `F'` exists (`exists_valuationSubring_comap_eq`).
If `W'` is any other extension, then both `W` and `W'` restrict to `V` on `F` (because `F'` is a
scalar tower over `F → K → F'`), and `F'/F` is algebraic, so the uniqueness of the extension of the
Henselian valuation `V` to an algebraic extension (`eq_of_comap_eq_of_isAlgebraic`) gives `W' = W`.
-/

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

theorem henselianLocalRing_of_isAlgebraic {F K : Type*} [Field F] [Field K] [Algebra F K]
    (hK : Algebra.IsAlgebraic F K) (V : ValuationSubring F) [HenselianLocalRing V]
    (vK : ValuationSubring K) (h : vK.comap (algebraMap F K) = V) :
    HenselianLocalRing vK := by
  -- Work inside a separable closure `F'` of `K`.
  let F' := SeparableClosure K
  haveI hsc : IsSepClosure K F' := inferInstance
  -- Transport the `F`-algebra structure along `F → K → F'` so that the scalar tower holds.
  letI algFF' : Algebra F F' := ((algebraMap K F').comp (algebraMap F K)).toAlgebra
  haveI hst : IsScalarTower F K F' := IsScalarTower.of_algebraMap_eq' rfl
  haveI halg : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.trans F K F'
  -- An extension `W` of `vK` to `F'` exists.
  obtain ⟨W, hW⟩ := exists_valuationSubring_comap_eq (K := K) (L := F') vK
  -- It suffices to prove that this extension is unique.
  refine henselianLocalRing_of_unique_extension (F := K) (F' := F') vK W hW ?_
  intro W' hW'
  symm
  -- Both `W` and `W'` restrict to `V` on `F`, so uniqueness of the extension of the Henselian
  -- valuation `V` to the algebraic extension `F'/F` forces `W = W'`.
  refine eq_of_comap_eq_of_isAlgebraic (K := F) (L := F') V W W' ?_ ?_
  · have e : W.comap (algebraMap F F') = (W.comap (algebraMap K F')).comap (algebraMap F K) := rfl
    rw [e, hW, h]
  · have e : W'.comap (algebraMap F F') = (W'.comap (algebraMap K F')).comap (algebraMap F K) := rfl
    rw [e, hW', h]

end Commons.RingTheory.Valuation
