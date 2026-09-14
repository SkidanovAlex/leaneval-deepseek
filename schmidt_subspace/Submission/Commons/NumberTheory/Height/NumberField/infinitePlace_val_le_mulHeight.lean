import Mathlib.NumberTheory.Height.NumberField

open _root_.NumberField

namespace Commons.NumberTheory.Height.NumberField

theorem infinitePlace_val_le_mulHeight {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (x : K) :
    w.val x ≤ Height.mulHeight₁ x := by
  rw [NumberField.mulHeight₁_eq x]
  have hwbase : 1 ≤ max (w.val x) 1 := le_max_right _ _
  have hfin : 1 ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
    one_le_finprod (f := fun v : FinitePlace K => max (v x) 1) fun v => le_max_right (v x) 1
  have hprod : (∏ v ∈ ({w} : Finset (InfinitePlace K)), max (v x) 1 ^ v.mult) ≤
      ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult := by
    refine Finset.prod_le_prod_of_subset_of_one_le (R := ℝ)
      (f := fun v : InfinitePlace K => max (v x) 1 ^ v.mult)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ w)) ?_ ?_
    · intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      exact pow_nonneg (le_trans zero_le_one hwbase) _
    · intro i _ _
      exact one_le_pow₀ (le_max_right (i x) 1)
  calc w.val x ≤ max (w.val x) 1 := le_max_left _ _
    _ ≤ max (w.val x) 1 ^ w.mult := by
        simpa using pow_le_pow_right₀ hwbase (show 1 ≤ w.mult from w.mult_pos)
    _ = ∏ v ∈ ({w} : Finset (InfinitePlace K)), max (v x) 1 ^ v.mult := by
        rw [Finset.prod_singleton]
        simp only [InfinitePlace.coe_apply]
    _ ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult := hprod
    _ ≤ (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) *
        ∏ᶠ v : FinitePlace K, max (v x) 1 :=
        le_mul_of_one_le_right
          (Finset.prod_nonneg fun v _ => pow_nonneg (le_trans zero_le_one (le_max_right (v x) 1)) _)
          hfin

end Commons.NumberTheory.Height.NumberField