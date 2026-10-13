import Mathlib

namespace Work.WilG4c

/-- Continuity of `g : (Fin (n+1) → ℝ) → ℝ` at `u` is equivalently tested by the
squared Euclidean distance on the domain and the ordinary distance on the codomain,
both written with squares to avoid square roots. -/
theorem continuousAt_iff_sumSq {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) :
    ContinuousAt g u ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin (n + 1) → ℝ,
      (∑ j : Fin (n + 1), (y j - u j) ^ 2) < δ ^ 2 → (g y - g u) ^ 2 < ε ^ 2 := by
  constructor
  · -- Continuity is stronger than the sum-of-squares ε-δ condition.
    intro hc ε hε
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hδprop⟩ := hc ε hε
    refine ⟨δ / 2, by positivity, fun y hy => ?_⟩
    -- The sum-of-squares bound forces every coordinate to be within `δ / 2`.
    have hdist : dist y u ≤ δ / 2 := by
      rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ δ / 2)]
      intro j
      rw [Real.dist_eq]
      have hj : (y j - u j) ^ 2 ≤ ∑ i : Fin (n + 1), (y i - u i) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ) (f := fun i => (y i - u i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      have hj' : (y j - u j) ^ 2 < (δ / 2) ^ 2 := lt_of_le_of_lt hj hy
      have h : |y j - u j| < δ / 2 := by
        rw [sq_lt_sq] at hj'
        rwa [abs_of_pos (by positivity : (0 : ℝ) < δ / 2)] at hj'
      exact le_of_lt h
    have hgd : dist (g y) (g u) < ε := hδprop (lt_of_le_of_lt hdist (by linarith))
    rw [Real.dist_eq] at hgd
    rw [sq_lt_sq]
    rwa [abs_of_pos hε]
  · -- Conversely, the sum-of-squares ε-δ condition controls each coordinate and
    -- hence gives ordinary continuity, after shrinking the radius by the dimension.
    intro h
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := h ε hε
    refine ⟨δ / ((n : ℝ) + 2), by positivity, fun y hy => ?_⟩
    have hcoord : ∀ j : Fin (n + 1), (y j - u j) ^ 2 < (δ / ((n : ℝ) + 2)) ^ 2 := by
      intro j
      have h1 : |y j - u j| < δ / ((n : ℝ) + 2) := by
        have h2 := (dist_pi_lt_iff (by positivity : (0 : ℝ) < δ / ((n : ℝ) + 2))).mp hy j
        rwa [Real.dist_eq] at h2
      rw [sq_lt_sq]
      rwa [abs_of_pos (by positivity : (0 : ℝ) < δ / ((n : ℝ) + 2))]
    -- The squared Euclidean distance is at most `(n+1)` times the square of any
    -- common coordinate bound, and `(n+1) / (n+2)^2 < 1`.
    have hsum : (∑ j : Fin (n + 1), (y j - u j) ^ 2) < δ ^ 2 := by
      calc (∑ j : Fin (n + 1), (y j - u j) ^ 2)
          ≤ ∑ j : Fin (n + 1), (δ / ((n : ℝ) + 2)) ^ 2 :=
            Finset.sum_le_sum (fun j _ => le_of_lt (hcoord j))
        _ = (n + 1 : ℝ) * (δ / ((n : ℝ) + 2)) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ < δ ^ 2 := by
            have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
            have hkey : ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2 < 1 := by
              rw [div_lt_one (by positivity)]
              nlinarith
            have heq : ((n : ℝ) + 1) * (δ / ((n : ℝ) + 2)) ^ 2
                = (((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2) * δ ^ 2 := by
              field_simp
            rw [heq]
            calc (((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2) * δ ^ 2 < 1 * δ ^ 2 :=
                  mul_lt_mul_of_pos_right hkey hδ2
              _ = δ ^ 2 := one_mul _
    have hfinal := hδprop y hsum
    rw [sq_lt_sq] at hfinal
    rw [Real.dist_eq]
    rwa [abs_of_pos hε] at hfinal

end Work.WilG4c
