import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.assembly_aux

/-!
# `supf f ≤ 16 c(2,1) T³ ∫ f` (GM §9, the `ε = 1` case)

Specialisation of `supf_le_of_decay` to the exponent `ε = 1`, giving

  `supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u`.

The statement carries no explicit sign hypothesis on `c 2 1`; instead the decay hypothesis
itself forces `0 ≤ c 2 1`: at `j = 2`, `ε = 1`, `ξ = 1` we have

  `‖Fhat f 1‖ ≤ c 2 1 * T * ((T / |1|) ^ 2) * supf f`

with `0 < T * ((T / |1|) ^ 2) * supf f` (using `T ≥ 1` and `0 < supf f`), and `‖·‖ ≥ 0`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem supf_le_of_decay_three {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hT : 1 ≤ T)
    (hf : Continuous f) (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u)
    (hdec : DecayHyp c T f) (hpos : 0 < supf f) :
    supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  -- decay at `j = 2`, `ε = 1`, `ξ = 1`, with the rpow `T ^ (1 : ℝ)` unfolded
  have hdec1 : ‖Fhat f 1‖ ≤ c 2 1 * T * (T / |(1 : ℝ)|) ^ 2 * supf f := by
    simpa [Real.rpow_one] using hdec 2 1 one_pos 1 one_ne_zero
  have hQ : (0 : ℝ) < T * (T / |(1 : ℝ)|) ^ 2 * supf f := by
    have h1 : (0 : ℝ) < T / |(1 : ℝ)| := by rw [abs_one, div_one]; exact hTpos
    positivity
  -- `DecayHyp` forces `0 ≤ c 2 1`
  have hc : 0 ≤ c 2 1 := by
    refine nonneg_of_mul_nonneg_left ?_ hQ
    calc (0 : ℝ) ≤ ‖Fhat f 1‖ := norm_nonneg _
      _ ≤ c 2 1 * T * (T / |(1 : ℝ)|) ^ 2 * supf f := hdec1
      _ = c 2 1 * (T * (T / |(1 : ℝ)|) ^ 2 * supf f) := by ring
  have hmain :=
    supf_le_of_decay (c := c) (T := T) (f := f) (ε := 1) hf hcs hnn hdec one_pos hc
  calc supf f ≤ 16 * c 2 1 * T ^ (1 : ℝ) * T ^ 2 * ∫ u, f u := hmain
    _ = 16 * c 2 1 * T ^ 3 * ∫ u, f u := by rw [Real.rpow_one]; ring

end

end Work.GM.Affine
