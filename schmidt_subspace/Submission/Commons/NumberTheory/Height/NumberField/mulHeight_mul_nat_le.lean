import Mathlib.NumberTheory.Height.NumberField

namespace Commons.NumberTheory.Height.NumberField

open _root_.NumberField

/-- If `h : ι → ℕ` takes values at most `C ≥ 1`, then the multiplicative height of the tuple
of their images in a number field `K` is at most the multiplicative height of `C`. -/
theorem mulHeight_natCast_le {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (C : ℕ) (hC : ∀ i, h i ≤ C) (hC1 : 1 ≤ C) :
    Height.mulHeight (fun i => (h i : K)) ≤ Height.mulHeight₁ (C : K) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hz : (fun i : ι => (h i : K)) = 0 := funext fun i => (hι.false i).elim
    rw [hz, Height.mulHeight_zero]
    exact Height.one_le_mulHeight₁ _
  · by_cases hx : (fun i : ι => (h i : K)) = 0
    · rw [hx, Height.mulHeight_zero]
      exact Height.one_le_mulHeight₁ _
    · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
      have hCne : (C : K) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hC1)
      have hfSupp : (fun v : FinitePlace K => ⨆ i, v ((h i : K))).HasFiniteMulSupport := by
        refine (FinitePlace.hasFiniteMulSupport (x := (h i₀ : K)) hi₀).subset ?_
        intro v hv
        simp only [Function.mem_mulSupport] at hv ⊢
        intro hcon
        refine hv (le_antisymm (ciSup_le fun i => ?_) ?_)
        · exact IsNonarchimedean.apply_natCast_le_one (f := v) (FinitePlace.add_le v)
        · rw [← hcon]; exact Finite.le_ciSup_of_le i₀ le_rfl
      have hgSupp : (fun v : FinitePlace K => max (v ((C : K))) 1).HasFiniteMulSupport :=
        (FinitePlace.hasFiniteMulSupport (x := (C : K)) hCne).max
          (Function.hasFiniteMulSupport_fun_one)
      rw [_root_.NumberField.mulHeight_eq hx, _root_.NumberField.mulHeight₁_eq]
      refine mul_le_mul ?_ ?_ ?_ ?_
      · apply Finset.prod_le_prod
        · intro v _
          exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _) _
        · intro v _
          apply pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass v _)
          refine ciSup_le fun i => ?_
          rw [InfinitePlace.map_natCast, InfinitePlace.map_natCast]
          exact le_trans (by exact_mod_cast hC i) (le_max_left _ _)
      · apply finprod_le_finprod hfSupp (fun v => Real.iSup_nonneg_of_nonnegHomClass v _) hgSupp
        intro v
        refine ciSup_le fun i => ?_
        exact le_trans (IsNonarchimedean.apply_natCast_le_one (f := v) (FinitePlace.add_le v))
          (le_max_right _ _)
      · exact finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v _
      · exact Finset.prod_nonneg fun v _ =>
          pow_nonneg (zero_le_one.trans (le_max_right _ _)) _

/-- If a tuple `a : ι → K` over a number field is multiplied pointwise by a tuple of natural
numbers `h i ≤ C`, then its multiplicative height grows by at most the multiplicative height
of `C`. -/
theorem mulHeight_mul_nat_le {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (a : ι → K) (h : ι → ℕ) (C : ℕ) (hC : ∀ i, h i ≤ C) (hC1 : 1 ≤ C) :
    Height.mulHeight (fun i => a i * (h i : K)) ≤
      Height.mulHeight a * Height.mulHeight₁ (C : K) := by
  calc Height.mulHeight (fun i => a i * (h i : K))
      = Height.mulHeight (a * fun i => (h i : K)) := rfl
    _ ≤ Height.mulHeight a * Height.mulHeight (fun i => (h i : K)) :=
        Height.mulHeight_mul_le _ _
    _ ≤ Height.mulHeight a * Height.mulHeight₁ (C : K) :=
        mul_le_mul_of_nonneg_left (mulHeight_natCast_le h C hC hC1) (Height.mulHeight_pos a).le

end Commons.NumberTheory.Height.NumberField