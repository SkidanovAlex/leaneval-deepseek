import Mathlib.NumberTheory.Height.NumberField

namespace Commons.NumberTheory.Height.NumberField

open _root_.NumberField

/-- The infinite place of a number field evaluated at an integer `n` is the usual
absolute value `‖n‖`. -/
lemma infinitePlace_intCast {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) (n : ℤ) : w (n : K) = ‖n‖ := by
  rw [← InfinitePlace.norm_embedding_eq, map_intCast, Complex.norm_intCast, Int.norm_eq_abs]

/-- The multiplicative height of an integer `n`, considered as element of a number field `K`,
equals `(max 1 ‖n‖) ^ [K : ℚ]`. -/
lemma mulHeight₁_intCast {K : Type*} [Field K] [NumberField K] (n : ℤ) :
    Height.mulHeight₁ (n : K) = (max 1 ‖n‖) ^ (Module.finrank ℚ K) := by
  rw [NumberField.mulHeight₁_eq]
  -- archimedean places contribute `max 1 ‖n‖` each, and there are `totalWeight K` of them
  have hinf : ∀ v : InfinitePlace K, max (v (n : K)) 1 = max 1 ‖n‖ := by
    intro v
    rw [infinitePlace_intCast v n, max_comm]
  -- nonarchimedean places contribute `1`
  have hfin : (∏ᶠ v : FinitePlace K, max (v (n : K)) 1) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      rw [max_eq_right]
      exact IsNonarchimedean.apply_intCast_le_one (FinitePlace.add_le v)
  simp_rw [hinf]
  rw [hfin, mul_one, Finset.prod_pow_eq_pow_sum, ← NumberField.totalWeight_eq_sum_mult,
    NumberField.totalWeight_eq_finrank]

theorem mulHeight_sum_mul_int_le_of_nonempty {K : Type*} [Field K] [NumberField K]
    {σ : Type*} [Fintype σ] [Nonempty σ] (a : σ → K) (x : σ → ℤ) :
    Height.mulHeight₁ (∑ j : σ, a j * (x j : K)) ≤
      (Fintype.card σ) ^ (Module.finrank ℚ K) * (∏ j : σ, Height.mulHeight₁ (a j)) *
        (max 1 ‖x‖) ^ (Module.finrank ℚ K * Fintype.card σ) := by
  rw [← NumberField.totalWeight_eq_finrank]
  -- the height of a sum is bounded by `(#σ) ^ totalWeight` times the product of the heights
  have h1 : Height.mulHeight₁ (∑ j : σ, a j * (x j : K)) ≤
      (Fintype.card σ : ℝ) ^ Height.totalWeight K *
        ∏ j : σ, Height.mulHeight₁ (a j * (x j : K)) := by
    have h := Height.mulHeight₁_sum_le (Finset.univ_nonempty (α := σ))
      (fun j : σ => a j * (x j : K))
    simpa using h
  -- each factor `mulHeight₁ (a j) * mulHeight₁ (x j)` contributes, and the `x j` part
  -- is bounded using that every `‖x j‖ ≤ ‖x‖`
  have h2 : (∏ j : σ, Height.mulHeight₁ (a j * (x j : K))) ≤
      (∏ j : σ, Height.mulHeight₁ (a j)) *
        (max 1 ‖x‖) ^ (Height.totalWeight K * Fintype.card σ) := by
    calc ∏ j : σ, Height.mulHeight₁ (a j * (x j : K))
        ≤ ∏ j : σ, Height.mulHeight₁ (a j) * Height.mulHeight₁ ((x j : K)) :=
          Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => Height.mulHeight₁_mul_le _ _)
      _ = (∏ j : σ, Height.mulHeight₁ (a j)) * ∏ j : σ, Height.mulHeight₁ ((x j : K)) := by
          simp [Finset.prod_mul_distrib]
      _ ≤ (∏ j : σ, Height.mulHeight₁ (a j)) *
            (max 1 ‖x‖) ^ (Height.totalWeight K * Fintype.card σ) := by
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun j _ => by positivity)
          calc ∏ j : σ, Height.mulHeight₁ ((x j : K))
              ≤ ∏ j : σ, (max 1 ‖x‖) ^ Height.totalWeight K := by
                refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
                rw [mulHeight₁_intCast, NumberField.totalWeight_eq_finrank]
                exact pow_le_pow_left₀ (by positivity)
                  (max_le_max le_rfl (norm_le_pi_norm x j)) _
            _ = ((max 1 ‖x‖) ^ Height.totalWeight K) ^ Fintype.card σ := by
                rw [Finset.prod_const]; simp
            _ = (max 1 ‖x‖) ^ (Height.totalWeight K * Fintype.card σ) := by
                rw [pow_mul]
  calc Height.mulHeight₁ (∑ j : σ, a j * (x j : K))
      ≤ (Fintype.card σ : ℝ) ^ Height.totalWeight K *
          ∏ j : σ, Height.mulHeight₁ (a j * (x j : K)) := h1
    _ ≤ (Fintype.card σ : ℝ) ^ Height.totalWeight K *
          ((∏ j : σ, Height.mulHeight₁ (a j)) *
            (max 1 ‖x‖) ^ (Height.totalWeight K * Fintype.card σ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Fintype.card σ : ℝ) ^ Height.totalWeight K * (∏ j : σ, Height.mulHeight₁ (a j)) *
          (max 1 ‖x‖) ^ (Height.totalWeight K * Fintype.card σ) := by ring

end Commons.NumberTheory.Height.NumberField