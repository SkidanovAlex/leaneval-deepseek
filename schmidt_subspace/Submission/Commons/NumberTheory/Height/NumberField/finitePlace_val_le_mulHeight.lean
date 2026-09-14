import Mathlib.NumberTheory.Height.NumberField

namespace Commons.NumberTheory.Height.NumberField

/-- Every finite place of a number field is bounded by the multiplicative height:
the value of `v` at `x` is at most `max (v x) 1`, which is one of the factors in the
definition of `Height.mulHeight₁ x`, and all the other factors are at least `1`. -/
theorem finitePlace_val_le_mulHeight {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (x : K) :
    v.val x ≤ Height.mulHeight₁ x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [NumberField.mulHeight₁_eq]
  -- the finite-part of the height is a finite product of factors each `≥ 1`
  have hg : (fun w : NumberField.FinitePlace K => max (w.val x) 1).HasFiniteMulSupport := by
    fun_prop
  have hB : v.val x ≤ ∏ᶠ w : NumberField.FinitePlace K, max (w.val x) 1 := by
    have hprod : (∏ᶠ w : NumberField.FinitePlace K, max (w.val x) 1)
        = ∏ w ∈ (insert v hg.toFinset), max (w.val x) 1 := by
      refine finprod_eq_prod_of_mulSupport_subset _ ?_
      intro w hw
      exact Finset.mem_insert_of_mem (hg.mem_toFinset.2 hw)
    rw [hprod]
    exact Finset.le_prod_max_one (Finset.mem_insert_self v hg.toFinset) (fun w => w.val x)
  -- the archimedean part is `≥ 1`, hence the whole height dominates the finite part
  refine hB.trans ?_
  have hA : 1 ≤ ∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult := by
    apply Finset.one_le_prod
    intro w _
    exact one_le_pow₀ (le_max_right _ _)
  have hB0 : 0 ≤ ∏ᶠ w : NumberField.FinitePlace K, max (w.val x) 1 :=
    finprod_nonneg fun w => le_trans zero_le_one (le_max_right _ _)
  calc (∏ᶠ w : NumberField.FinitePlace K, max (w.val x) 1)
      = 1 * ∏ᶠ w : NumberField.FinitePlace K, max (w.val x) 1 := (one_mul _).symm
    _ ≤ (∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult)
          * ∏ᶠ w : NumberField.FinitePlace K, max (w.val x) 1 :=
        mul_le_mul_of_nonneg_right hA hB0

end Commons.NumberTheory.Height.NumberField