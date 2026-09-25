import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFT.IdeleNorm

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT

/-- **The product formula for the log vector** (Milne, *CFT*, Chapter VII §3): the log of the
normalized local absolute value of a `T`-unit has sum zero over `T`, provided `T` contains all
infinite places.  Equivalently, `logVecLin` lands in the sum-zero hyperplane
`NK.GlobalCFTdeep.sumZero`.

## Proof sketch

For `a ∈ U(T)` and `w ∉ T` the component `principalIdele L a w` is a local unit, so
`Idele.localAbs L w _ = 1` (`Idele.localAbs_ofFinite_eq_one`; at an infinite place the `TUnits`
condition is vacuous and `hTinf` puts all infinite places in `T`), hence `logVec T a w = 0`.  So
`∑_{w ∈ T} logVec T a w` is the whole product over all places of `L`, i.e. `Real.log 1 = 0` by
the product formula `NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele` together with
`Real.log_prod`/`Finset.sum` bookkeeping (`localAbs L v _ ≠ 0` everywhere). -/
theorem sum_logVec_eq_zero {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (T : Set (NK.GlobalCFT.Place L)) [Fintype ↥T]
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T)
    (a : Lˣ) (ha : a ∈ NK.GlobalCFTdeep.TUnits (L := L) T) :
    ∑ w : ↥T, NK.GlobalCFTdeep.logVec (L := L) T a w = 0 := by
  -- Abbreviation for the local absolute values of the principal idèle of `a`.
  set f : Place L → ℝˣ := fun v => Idele.localAbs L v (Idele.principalIdele L a v) with hf
  -- Outside `T` the local absolute value is `1`: there the place is finite (because `hTinf`
  -- puts every infinite place in `T`) and the component is a local unit by `ha`.
  have hzero : ∀ v : Place L, v ∉ T → f v = 1 := by
    intro v hv
    have hfin : v.IsFinite :=
      Place.isFinite_iff_not_isInfinite.mpr (fun h => hv (hTinf v h))
    obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hfin
    show Idele.localAbs L (Place.ofFinite q) (Idele.principalIdele L a (Place.ofFinite q)) = 1
    refine Idele.localAbs_ofFinite_eq_one ?_
    rw [Idele.principalIdele_apply]
    exact ha (Place.ofFinite q) hv
  have hsupp : Function.mulSupport f ⊆ T := by
    intro v hv
    by_contra h
    exact hv (hzero v h)
  -- The `finprod` over all places is the product over `T`.
  have hfinprod : (∏ᶠ v : Place L, f v) = ∏ w : ↥T, f w := by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := T.toFinset) (by
      rw [Set.coe_toFinset]; exact hsupp)]
    exact (Finset.prod_set_coe (f := f) T).symm
  -- The product formula: the product of the local absolute values is `1`.
  have hfinprod_one : (∏ᶠ v : Place L, f v) = 1 := by
    rw [hf]
    rw [← Idele.abs_apply]
    exact NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele a
  have hprod_one : (∏ w : ↥T, ((f w : ℝˣ) : ℝ)) = 1 := by
    rw [← Units.coe_prod (fun w : ↥T => f w) Finset.univ, ← hfinprod, hfinprod_one]
    rfl
  show ∑ w : ↥T, Real.log ((f w : ℝˣ) : ℝ) = 0
  rw [← Real.log_prod (s := Finset.univ)
      (f := fun w : ↥T => ((f w : ℝˣ) : ℝ)) (fun x _ => Units.ne_zero _), hprod_one,
    Real.log_one]

end NK.GlobalCFTdeep.LogLattice
