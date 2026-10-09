import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A unit of the ring of integers has local norm one at every finite place

Let `K` be a number field and `u ∈ (𝓞 K)ˣ` a unit of its ring of integers.  Viewed in `K`
through the canonical inclusion, `u` has `q`-adic valuation `1` at every nonarchimedean place
`q` (a unit of `𝓞 K` is not contained in any proper ideal, in particular not in the prime
`q.asIdeal`), and hence local absolute value `1`.  Consequently the principal idèle `(u)ᵥ`
belongs to the local units at every finite place.

The main result is `globalCFT_principalIdele_unit_ofFinite_norm_one`, the statement that the
`q`-adic norm of the `q`-component of the principal idèle of `u` is one.  This is the local
input for the description of the kernel of the content map `𝕀 K → ℝ_{>0}` on `Kˣ`: the image of
`(𝓞 K)ˣ` in `𝕀 K` is contained in the idèles which are local units at every finite place.
-/

namespace NK.GlobalCFT.IdeleClassGroup

theorem globalCFT_principalIdele_unit_ofFinite_norm_one {K : Type*} [Field K] [NumberField K]
    (u : (NumberField.RingOfIntegers K)ˣ) (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ‖(NK.GlobalCFT.Idele.principalIdele K
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u)
        (NK.GlobalCFT.Place.ofFinite q) : q.adicCompletion K)‖ = 1 := by
  -- The `q`-component of the principal idèle of `u` is the image of `u` in the completion.
  have hy : ((NK.GlobalCFT.Idele.principalIdele K
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u)
        (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)
      = algebraMap (NumberField.RingOfIntegers K) (q.adicCompletion K)
          (u : NumberField.RingOfIntegers K) := by
    simp [NK.GlobalCFT.Idele.principalIdele_apply,
      IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K (q.adicCompletion K)]
  rw [hy]
  -- The `q`-adic valuation of the unit `u` is one: `u` is a unit, so it lies in no proper ideal.
  have hval : q.valuation K
      (algebraMap (NumberField.RingOfIntegers K) K (u : NumberField.RingOfIntegers K)) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem q).mpr
      (fun h => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit))
  -- The completion's valuation restricts to the global `q`-adic valuation on `K`.
  have hv : Valued.v (algebraMap (NumberField.RingOfIntegers K) (q.adicCompletion K)
      (u : NumberField.RingOfIntegers K)) = 1 := by
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K (q.adicCompletion K)]
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    exact hval
  -- A rank-one valued field has norm one exactly on elements of valuation one.
  refine le_antisymm ?_ ?_
  · rw [Valued.toNormedField.norm_le_one_iff]; exact le_of_eq hv
  · rw [Valued.toNormedField.one_le_norm_iff]; exact le_of_eq hv.symm

end NK.GlobalCFT.IdeleClassGroup
