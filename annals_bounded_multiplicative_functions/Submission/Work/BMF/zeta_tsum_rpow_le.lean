import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory intervalIntegral Finset

namespace Work.BMF

/-- For `σ > 1`, the `p`-series with exponent `σ` (indexed from `0`, the term at `0` being `0`)
is bounded by `1 + 1/(σ - 1)`; this is the elementary integral-test bound for `ζ(σ)`.

Proof. By `Real.tsum_le_of_sum_range_le` it suffices to bound every partial sum
`∑_{i<N} i^{-σ}`. For `N ≥ 2` split off the first two terms (`0^{-σ} = 0`, `1^{-σ} = 1`) and
bound the remaining tail `∑_{j} (j+2)^{-σ}` by the integral `∫_1^{N-1} x^{-σ} dx` using the
antitone integral test `AntitoneOn.sum_le_integral`. Since `x ↦ x^{-σ}` is antitone on `[1, ∞)`,
that integral equals `(1 - (N-1)^{1-σ})/(σ-1) ≤ 1/(σ-1)`. -/
theorem zeta_tsum_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hne : (-σ) ≠ 0 := by linarith
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) ?_
  intro N
  rcases N with _ | _ | k
  · rw [Finset.sum_range_zero]
    have : (0 : ℝ) ≤ 1 / (σ - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  · rw [Finset.sum_range_one, Nat.cast_zero, Real.zero_rpow hne]
    have : (0 : ℝ) ≤ 1 / (σ - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  · have hsplit : (∑ i ∈ Finset.range (k + 2), ((i : ℝ) ^ (-σ)))
        = (∑ i ∈ Finset.range 2, ((i : ℝ) ^ (-σ)))
          + ∑ i ∈ Finset.range k, (((2 + i : ℕ) : ℝ) ^ (-σ)) := by
      rw [show k + 2 = 2 + k by omega, Finset.sum_range_add]
    rw [hsplit]
    have h2 : (∑ i ∈ Finset.range 2, ((i : ℝ) ^ (-σ))) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Real.zero_rpow hne]
      simp
    rw [h2]
    have hbound : (∑ i ∈ Finset.range k, (((2 + i : ℕ) : ℝ) ^ (-σ))) ≤ 1 / (σ - 1) := by
      have hantiIcc : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc (1 : ℝ) (1 + ↑k)) := by
        intro x hx y hy hxy
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
        exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
      have hle := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := k)
        (f := fun x : ℝ => x ^ (-σ)) hantiIcc
      have hsum_eq : (∑ i ∈ Finset.range k, (((2 + i : ℕ) : ℝ) ^ (-σ)))
          = ∑ i ∈ Finset.range k, ((1 : ℝ) + ↑(i + 1)) ^ (-σ) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        push_cast
        ring
      have hint : ∫ x in (1 : ℝ)..(1 + ↑k), x ^ (-σ) = (1 - (1 + ↑k) ^ (1 - σ)) / (σ - 1) := by
        have hne' : (-σ) ≠ -1 := by linarith
        have h0mem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + ↑k) := by
          rw [Set.uIcc_of_le
            (show (1 : ℝ) ≤ 1 + ↑k by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))])]
          intro h
          rw [Set.mem_Icc] at h
          linarith [h.1]
        rw [integral_rpow (a := (1 : ℝ)) (b := 1 + ↑k) (r := -σ) (Or.inr ⟨hne', h0mem⟩)]
        rw [show (-σ) + 1 = 1 - σ by ring, Real.one_rpow]
        rw [div_eq_div_iff (by linarith : (1 : ℝ) - σ ≠ 0) (by linarith : σ - 1 ≠ 0)]
        ring
      rw [hsum_eq]
      calc (∑ i ∈ Finset.range k, ((1 : ℝ) + ↑(i + 1)) ^ (-σ))
          ≤ ∫ x in (1 : ℝ)..(1 + ↑k), x ^ (-σ) := hle
        _ = (1 - (1 + ↑k) ^ (1 - σ)) / (σ - 1) := hint
        _ ≤ 1 / (σ - 1) := div_le_div_of_nonneg_right (by
              have hb_nn : 0 ≤ (1 + ↑k : ℝ) ^ (1 - σ) := Real.rpow_nonneg (by positivity) _
              linarith) (by linarith)
    linarith

end Work.BMF
