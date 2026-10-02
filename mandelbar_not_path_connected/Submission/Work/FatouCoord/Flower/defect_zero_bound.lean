import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Flower.LambdaBounds
import Submission.Work.FatouCoord.Repelling.second_order_mod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The defect of the corrected ansatz vanishes at `ζ = 0` like `(1 + log ‖y‖)/‖y‖²`

For a parabolic germ `f z = z + z ^ 2 * h z` (`h 0 = 1`, `ParabolicBounds f h a r A A'`) the
repelling coordinate is built from the corrected ansatz `V y = y + (1 - a) Λ y + ζ`, where
`Λ y = log (-y) + π i` is a single-valued branch of the logarithm on the left half-plane.

The chart points that occur in the flower construction are only known to satisfy `Re y < -1`
(they are *not* confined to a far left half-plane `{Re y < -R}` as in
`Repelling/defect_bound`), together with a lower bound on `‖y‖`.  This file proves that on that
region the *defect* `Petal.defect f a y 0` of the ansatz with `ζ = 0` is still
`O((1 + log ‖y‖)/‖y‖²)`.

The proof is the same computation as in `Repelling/defect_bound`, with the hypothesis
`y ∈ LeftHalfPlane R` replaced by `y.re < -1` and `‖y‖ ≥ N`: the only place the real part of
`y` is used is the shift estimate `Λ (y+1) - Λ y ≈ 1/y`, which needs precisely `Re y < -1`.
Everything else only uses `‖V‖ ≥ ‖y‖/2`, where `V = y + (1 - a) Λ y`:

`defect = (wMap f V - V - 1 - (1-a)/V) + (1-a) (1/V - (Λ (y+1) - Λ y))`,

the first summand is `O(1/‖V‖²) = O(1/‖y‖²)` by `second_order_mod`, and for the second one
`1/V` differs from `1/y` by `O(‖V - y‖/‖y‖²) = O(log ‖y‖/‖y‖²)` while `Λ (y+1) - Λ y` differs
from `1/y` by `O(1/‖y‖²)`.
-/

open scoped Topology
open Set Filter Metric
open Work.FatouCoord Work.FatouCoord.Petal

namespace Work.FatouCoord.Flower

noncomputable section

/-! ## A growth threshold -/

/-- For large `t`, `C * (1 + log t) ≤ t / 2`. -/
private lemma log_growth (C : ℝ) (hC : 0 ≤ C) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → C * (1 + Real.log t) ≤ t / 2 := by
  have h1 : ∀ᶠ t : ℝ in Filter.atTop, C * Real.log t ≤ t / 4 := by
    have h := Real.isLittleO_log_id_atTop.const_mul_left (4 * C)
    filter_upwards [h.eventuallyLE, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht0, abs_mul, abs_of_nonneg hC,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at ht
    have h3 : C * Real.log t ≤ C * |Real.log t| := mul_le_mul_of_nonneg_left (le_abs_self _) hC
    linarith
  have h2 : ∀ᶠ t : ℝ in Filter.atTop, (4 : ℝ) * C ≤ t := Filter.eventually_ge_atTop (4 * C)
  have hmain : ∀ᶠ t : ℝ in Filter.atTop, C * (1 + Real.log t) ≤ t / 2 := by
    filter_upwards [h1, h2] with t ht1 ht2
    have hh : C ≤ t / 4 := by linarith
    linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨T, fun t ht => hT t ht⟩

/-! ## The main estimate -/

theorem defect_zero_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') : ∃ K N : ℝ, 0 < K ∧ 0 < N ∧ ∀ y : ℂ, y.re < -1 → N ≤ ‖y‖ → ‖Work.FatouCoord.Petal.defect f a y 0‖ ≤ K * (1 + Real.log ‖y‖) / ‖y‖ ^ 2 := by
  obtain ⟨K2, hK2nn, hK2⟩ := Repelling.second_order_mod hb
  set C : ℝ := ‖1 - a‖ * (1 + 2 * Real.pi) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨T, hT⟩ := log_growth C hCnn
  set K : ℝ := 4 * K2 + ‖1 - a‖ * (2 * C + 2) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 ≤ ‖1 - a‖ * (2 * C + 2) := mul_nonneg (norm_nonneg _) (by linarith)
    linarith
  set N : ℝ := max 8 (max (2 * (1 / r) + 1) (T + 1)) with hNdef
  have hN8 : 8 ≤ N := le_max_left _ _
  have hN2r : 2 * (1 / r) + 1 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNT : T + 1 ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN8
  refine ⟨K, N, hKpos, hNpos, ?_⟩
  intro y hy hNy
  have hyn1 : 1 ≤ ‖y‖ := by linarith
  have hyn2 : 2 ≤ ‖y‖ := by linarith
  have hyn8 : 8 ≤ ‖y‖ := by linarith
  have hyn0 : 0 < ‖y‖ := lt_of_lt_of_le (by norm_num) hyn1
  have hlog0 : 0 ≤ Real.log ‖y‖ := Real.log_nonneg hyn1
  have hyT : T ≤ ‖y‖ := by linarith
  have hy2r : 2 * (1 / r) < ‖y‖ := by linarith
  set V : ℂ := y + (1 - a) * Lambda y with hV
  have hVw : ‖V - y‖ ≤ C * (1 + Real.log ‖y‖) := by
    have h1 : V - y = (1 - a) * Lambda y := by rw [hV]; ring
    rw [h1]
    have h3 : ‖Lambda y‖ ≤ Real.log ‖y‖ + 2 * Real.pi := LambdaBounds.norm_Lambda_le_log hyn1
    have hL : 0 ≤ ‖1 - a‖ := norm_nonneg _
    have key : Real.log ‖y‖ + 2 * Real.pi ≤ (1 + 2 * Real.pi) * (1 + Real.log ‖y‖) := by
      have h1 : 0 ≤ Real.pi * Real.log ‖y‖ := mul_nonneg (le_of_lt Real.pi_pos) hlog0
      nlinarith [h1]
    calc ‖(1 - a) * Lambda y‖ = ‖1 - a‖ * ‖Lambda y‖ := norm_mul _ _
      _ ≤ ‖1 - a‖ * (Real.log ‖y‖ + 2 * Real.pi) := mul_le_mul_of_nonneg_left h3 hL
      _ ≤ ‖1 - a‖ * ((1 + 2 * Real.pi) * (1 + Real.log ‖y‖)) :=
          mul_le_mul_of_nonneg_left key hL
      _ = C * (1 + Real.log ‖y‖) := by rw [hCdef]; ring
  have hVw2 : ‖V - y‖ ≤ ‖y‖ / 2 := le_trans hVw (hT ‖y‖ hyT)
  have hVnorm : ‖y‖ / 2 ≤ ‖V‖ := by
    have h := norm_add_le V (y - V)
    have h2 : V + (y - V) = y := by ring
    rw [h2, norm_sub_rev] at h
    linarith
  have hVne : V ≠ 0 := by
    intro h0; rw [h0] at hVnorm; simp at hVnorm; linarith
  have hVr : 1 / r < ‖V‖ := by
    have h : 1 / r < ‖y‖ / 2 := by linarith
    linarith
  have hV4 : 4 ≤ ‖V‖ := by linarith
  have h2nd := hK2 V hVr hV4
  have hLam : ‖Lambda (y + 1) - Lambda y - 1 / y‖ ≤ 2 / ‖y‖ ^ 2 :=
    LambdaBounds.Lambda_shift_bound hy hyn2
  have hinv : ‖1 / V - 1 / y‖ ≤ 2 * C * (1 + Real.log ‖y‖) / ‖y‖ ^ 2 := by
    have h := LambdaBounds.norm_inv_sub_inv_le (V := V) (w := y) hyn0 hVnorm
    calc ‖1 / V - 1 / y‖ ≤ 2 * ‖V - y‖ / ‖y‖ ^ 2 := h
      _ ≤ 2 * (C * (1 + Real.log ‖y‖)) / ‖y‖ ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
      _ = 2 * C * (1 + Real.log ‖y‖) / ‖y‖ ^ 2 := by ring
  have hbracket : ‖1 / V - (Lambda (y + 1) - Lambda y)‖
      ≤ (2 * C * (1 + Real.log ‖y‖) + 2) / ‖y‖ ^ 2 := by
    have h1 : 1 / V - (Lambda (y + 1) - Lambda y)
        = (1 / V - 1 / y) + (1 / y - (Lambda (y + 1) - Lambda y)) := by ring
    rw [h1]
    have h2 : ‖1 / y - (Lambda (y + 1) - Lambda y)‖ ≤ 2 / ‖y‖ ^ 2 := by
      rw [norm_sub_rev]; exact hLam
    calc ‖(1 / V - 1 / y) + (1 / y - (Lambda (y + 1) - Lambda y))‖
        ≤ ‖1 / V - 1 / y‖ + ‖1 / y - (Lambda (y + 1) - Lambda y)‖ := norm_add_le _ _
      _ ≤ 2 * C * (1 + Real.log ‖y‖) / ‖y‖ ^ 2 + 2 / ‖y‖ ^ 2 := add_le_add hinv h2
      _ = (2 * C * (1 + Real.log ‖y‖) + 2) / ‖y‖ ^ 2 := by ring
  have hdec : defect f a y 0 = (wMap f V - V - 1 - (1 - a) / V)
      + (1 - a) * (1 / V - (Lambda (y + 1) - Lambda y)) := by
    rw [defect_apply, corr_apply]
    have h1 : y + (1 - a) * Lambda y + 0 = V := by rw [hV]; ring
    rw [h1]
    ring
  have hI : K2 / ‖V‖ ^ 2 ≤ 4 * K2 / ‖y‖ ^ 2 := by
    have hV2 : ‖y‖ ^ 2 / 4 ≤ ‖V‖ ^ 2 := by nlinarith [hVnorm, hyn0]
    have h1 : 1 / ‖V‖ ^ 2 ≤ 4 / ‖y‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hV2]
    calc K2 / ‖V‖ ^ 2 = K2 * (1 / ‖V‖ ^ 2) := by ring
      _ ≤ K2 * (4 / ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hK2nn
      _ = 4 * K2 / ‖y‖ ^ 2 := by ring
  have hnum : 4 * K2 + ‖1 - a‖ * (2 * C * (1 + Real.log ‖y‖) + 2)
      ≤ K * (1 + Real.log ‖y‖) := by
    have hL : 0 ≤ ‖1 - a‖ := norm_nonneg _
    have he : K * (1 + Real.log ‖y‖)
        = 4 * K2 + ‖1 - a‖ * (2 * C * (1 + Real.log ‖y‖) + 2)
          + (4 * K2 * Real.log ‖y‖ + 2 * ‖1 - a‖ * Real.log ‖y‖ + (1 + Real.log ‖y‖)) := by
      rw [hKdef]; ring
    rw [he]
    have h4 : 0 ≤ 4 * K2 * Real.log ‖y‖ := mul_nonneg (by linarith) hlog0
    have h5 : 0 ≤ 2 * ‖1 - a‖ * Real.log ‖y‖ := by positivity
    linarith
  calc ‖defect f a y 0‖
      = ‖(wMap f V - V - 1 - (1 - a) / V)
          + (1 - a) * (1 / V - (Lambda (y + 1) - Lambda y))‖ := by rw [hdec]
    _ ≤ ‖wMap f V - V - 1 - (1 - a) / V‖
          + ‖(1 - a) * (1 / V - (Lambda (y + 1) - Lambda y))‖ := norm_add_le _ _
    _ ≤ 4 * K2 / ‖y‖ ^ 2 + ‖1 - a‖ * ((2 * C * (1 + Real.log ‖y‖) + 2) / ‖y‖ ^ 2) := by
        have h3 : ‖(1 - a) * (1 / V - (Lambda (y + 1) - Lambda y))‖
            ≤ ‖1 - a‖ * ((2 * C * (1 + Real.log ‖y‖) + 2) / ‖y‖ ^ 2) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hbracket (norm_nonneg _)
        exact add_le_add (le_trans h2nd hI) h3
    _ ≤ K * (1 + Real.log ‖y‖) / ‖y‖ ^ 2 := by
        have h3 : ‖1 - a‖ * ((2 * C * (1 + Real.log ‖y‖) + 2) / ‖y‖ ^ 2)
            = ‖1 - a‖ * (2 * C * (1 + Real.log ‖y‖) + 2) / ‖y‖ ^ 2 := by ring
        rw [h3, ← add_div]
        exact div_le_div_of_nonneg_right hnum (by positivity)

end

end Work.FatouCoord.Flower
