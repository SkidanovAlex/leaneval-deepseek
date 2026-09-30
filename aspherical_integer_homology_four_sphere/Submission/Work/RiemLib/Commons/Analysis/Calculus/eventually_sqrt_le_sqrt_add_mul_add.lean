import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Ring.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus

theorem eventually_sqrt_le_sqrt_add_mul_add {A B ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.sqrt (t ^ 2 * A + 2 * (t * Real.sqrt t) * B + t)
        ≤ Real.sqrt t + t * (B + ε) := by
  rw [eventually_nhdsWithin_iff]
  rw [Metric.eventually_nhds_iff]
  set C : ℝ := |A - (B + ε) ^ 2| with hC
  set D : ℝ := |B + ε| with hD
  have hCnn : 0 ≤ C := by rw [hC]; exact abs_nonneg _
  have hDnn : 0 ≤ D := by rw [hD]; exact abs_nonneg _
  have hD1pos : 0 < D + 1 := by linarith
  have hC1pos : 0 < C + 1 := by linarith
  set a : ℝ := 1 / (D + 1) with ha
  set b : ℝ := 2 * ε / (C + 1) with hb
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hb_pos : 0 < b := by rw [hb]; positivity
  set m : ℝ := min a b with hm
  have hm_pos : 0 < m := by rw [hm]; exact lt_min ha_pos hb_pos
  refine ⟨m ^ 2, pow_pos hm_pos 2, ?_⟩
  intro t ht hti
  rw [Set.mem_Ioi] at hti
  have ht_abs : |t| < m ^ 2 := by simpa [Real.dist_eq, sub_zero] using ht
  have ht_lt : t < m ^ 2 := by rwa [abs_of_pos hti] at ht_abs
  have hu_lt : Real.sqrt t < m := (Real.sqrt_lt' hm_pos).mpr ht_lt
  have hu_le : Real.sqrt t ≤ m := le_of_lt hu_lt
  have hu_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hu_le_a : Real.sqrt t ≤ a := le_trans hu_le (min_le_left a b)
  have hu_le_b : Real.sqrt t ≤ b := le_trans hu_le (min_le_right a b)
  have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt hti)
  -- (i) 0 ≤ 1 + √t * (B + ε)
  have hZnn : 0 ≤ 1 + Real.sqrt t * (B + ε) := by
    have hSnn : 0 ≤ 1 - Real.sqrt t * D := by
      have h1 : Real.sqrt t * D ≤ a * D := mul_le_mul_of_nonneg_right hu_le_a hDnn
      have h2 : a * D ≤ 1 := by
        rw [ha, div_mul_eq_mul_div, div_le_one hD1pos]
        linarith
      linarith
    have hBe : -D ≤ B + ε := by
      rw [hD]; exact neg_abs_le _
    have hmul : Real.sqrt t * (-D) ≤ Real.sqrt t * (B + ε) :=
      mul_le_mul_of_nonneg_left hBe hu_nonneg
    linarith
  -- (ii) t * (A - (B+ε)^2) ≤ 2 √t ε
  have hkey : t * (A - (B + ε) ^ 2) ≤ 2 * Real.sqrt t * ε := by
    have hAC : A - (B + ε) ^ 2 ≤ C := by rw [hC]; exact le_abs_self _
    have hbC : b * C ≤ 2 * ε := by
      rw [hb, div_mul_eq_mul_div, div_le_iff₀ hC1pos]
      linarith
    have htC : t * C ≤ 2 * Real.sqrt t * ε := by
      have hs1 : (Real.sqrt t) ^ 2 ≤ Real.sqrt t * b := by
        rw [pow_two]; exact mul_le_mul_of_nonneg_left hu_le_b hu_nonneg
      calc t * C = (Real.sqrt t) ^ 2 * C := by rw [hsq]
        _ ≤ (Real.sqrt t * b) * C := mul_le_mul_of_nonneg_right hs1 hCnn
        _ = Real.sqrt t * (b * C) := by ring
        _ ≤ Real.sqrt t * (2 * ε) := mul_le_mul_of_nonneg_left hbC hu_nonneg
        _ = 2 * Real.sqrt t * ε := by ring
    linarith [mul_le_mul_of_nonneg_left hAC (le_of_lt hti)]
  -- main
  have hZsq : t * A + 2 * Real.sqrt t * B + 1 ≤ (1 + Real.sqrt t * (B + ε)) ^ 2 := by
    nlinarith [hkey]
  have hZ : Real.sqrt (t * A + 2 * Real.sqrt t * B + 1) ≤ 1 + Real.sqrt t * (B + ε) := by
    rw [Real.sqrt_le_iff]; exact ⟨hZnn, hZsq⟩
  have hX : t ^ 2 * A + 2 * (t * Real.sqrt t) * B + t
      = (Real.sqrt t) ^ 2 * (t * A + 2 * Real.sqrt t * B + 1) := by
    rw [Real.sq_sqrt (le_of_lt hti)]; ring
  calc
    Real.sqrt (t ^ 2 * A + 2 * (t * Real.sqrt t) * B + t)
        = Real.sqrt ((Real.sqrt t) ^ 2 * (t * A + 2 * Real.sqrt t * B + 1)) := by
            rw [hX]
    _ = Real.sqrt t * Real.sqrt (t * A + 2 * Real.sqrt t * B + 1) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hu_nonneg]
    _ ≤ Real.sqrt t * (1 + Real.sqrt t * (B + ε)) :=
            mul_le_mul_of_nonneg_left hZ hu_nonneg
    _ = Real.sqrt t + t * (B + ε) := by
            have hsq' : Real.sqrt t * Real.sqrt t = t := by rw [← pow_two, hsq]
            rw [mul_add, mul_one, ← mul_assoc, hsq']

end Commons.Analysis.Calculus