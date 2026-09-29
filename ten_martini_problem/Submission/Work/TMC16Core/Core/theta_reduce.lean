import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-! ## Elementary `fracDist` API

`fracDist x = |x - round x|` is the distance from `x` to the nearest integer.  We record
the few elementary properties used below: nonnegativity, the bound `1/2`, subadditivity,
evenness, the reverse triangle inequality and the bound for integer multiples. -/

lemma fracDist_nonneg' (x : ℝ) : 0 ≤ fracDist x := abs_nonneg _

lemma fracDist_le_half' (x : ℝ) : fracDist x ≤ 1 / 2 := by
  simpa only [fracDist] using abs_sub_round x

lemma fracDist_add_le' (a b : ℝ) : fracDist (a + b) ≤ fracDist a + fracDist b := by
  have h : Basic.nn (a + b) ≤ Basic.nn a + Basic.nn b := Basic.nn_add_le a b
  simpa only [fracDist, Basic.nn] using h

lemma fracDist_neg' (x : ℝ) : fracDist (-x) = fracDist x := by
  apply le_antisymm
  · have h := round_le (-x) (-(round x))
    calc fracDist (-x) = |(-x) - ((round (-x) : ℤ) : ℝ)| := rfl
      _ ≤ |(-x) - ((-(round x) : ℤ) : ℝ)| := h
      _ = |x - ((round x : ℤ) : ℝ)| := by
            rw [show (-x : ℝ) - ((-(round x) : ℤ) : ℝ) = -(x - ((round x : ℤ) : ℝ)) by
                  push_cast; ring, abs_neg]
      _ = fracDist x := rfl
  · have h := round_le x (-(round (-x)))
    calc fracDist x = |x - ((round x : ℤ) : ℝ)| := rfl
      _ ≤ |x - ((-(round (-x)) : ℤ) : ℝ)| := h
      _ = |(-x) - ((round (-x) : ℤ) : ℝ)| := by
            rw [show (x : ℝ) - ((-(round (-x)) : ℤ) : ℝ)
                  = -((-x) - ((round (-x) : ℤ) : ℝ)) by push_cast; ring, abs_neg]
      _ = fracDist (-x) := rfl

/-- Reverse triangle inequality: `fracDist a - fracDist b ≤ fracDist (a + b)`. -/
lemma le_fracDist_add' (a b : ℝ) : fracDist a - fracDist b ≤ fracDist (a + b) := by
  have h := fracDist_add_le' (a + b) (-b)
  rw [add_neg_cancel_right, fracDist_neg'] at h
  linarith

/-- `fracDist (M * x) ≤ |M| * fracDist x` for an integer `M`. -/
lemma fracDist_zmul_le (M : ℤ) (x : ℝ) :
    fracDist ((M : ℝ) * x) ≤ |(M : ℝ)| * fracDist x := by
  have h := round_le ((M : ℝ) * x) (M * round x)
  calc fracDist ((M : ℝ) * x)
      = |(M : ℝ) * x - ((round ((M : ℝ) * x) : ℤ) : ℝ)| := rfl
    _ ≤ |(M : ℝ) * x - ((M * round x : ℤ) : ℝ)| := h
    _ = |(M : ℝ)| * fracDist x := by
        have h2 : (M : ℝ) * x - ((M * round x : ℤ) : ℝ)
            = (M : ℝ) * (x - (round x : ℝ)) := by push_cast; ring
        rw [h2, abs_mul, fracDist]

/-! ## The main reduction -/

/-- **Reduction of the index range.**  Suppose `fracDist (2θ + kα) ≥ c` for all integers
`|k| ≤ B + 2Q`, where `Δ = fracDist (Qα)`.  If the "shift cost"
`2 (|y|/Q + B/(2Q) + 1) Δ` is at most `c/2`, then the same lower bound (with `c` replaced
by `c/2`) holds on the larger range `|k| ≤ 2|y| + B`.

Indeed, for `|k| ≤ 2|y| + B` let `m = round (k/Q)` and `r = k - m Q`.  Then
`|r| ≤ Q/2 ≤ B + 2Q`, so `c ≤ fracDist (2θ + rα)`, while `2θ + rα` differs from
`2θ + kα` by `m Q α`, whose `fracDist` is at most `|m| Δ ≤ 2 (|y|/Q + B/(2Q) + 1) Δ ≤ c/2`. -/
theorem theta_reduce {α θ : ℝ} {Q : ℕ} {Δ c B : ℝ} {y : ℤ}
    (hQ : 0 < Q) (hB : 0 ≤ B) (hc : 0 < c)
    (hΔ : Δ = Work.TMC16Core.fracDist ((Q : ℝ) * α))
    (hred : ∀ k : ℤ, |k| ≤ B + 2 * (Q : ℝ) → c ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hshift : 2 * ((|y| : ℝ) / (Q : ℝ) + B / (2 * (Q : ℝ)) + 1) * Δ ≤ c / 2) :
    ∀ k : ℤ, |k| ≤ 2 * |y| + B → c / 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) := by
  intro k hk
  have hq : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hqne : (Q : ℝ) ≠ 0 := ne_of_gt hq
  set m : ℤ := round ((k : ℝ) / (Q : ℝ)) with hm
  set r : ℤ := k - m * (Q : ℤ) with hr
  -- `r` as a real number
  have hr_cast : (r : ℝ) = (k : ℝ) - (m : ℝ) * (Q : ℝ) := by
    rw [hr]; push_cast; ring
  have hr_mul : (r : ℝ) = (Q : ℝ) * ((k : ℝ) / (Q : ℝ) - (m : ℝ)) := by
    rw [hr_cast, mul_sub, mul_div_cancel₀ (k : ℝ) hqne]
    ring
  have hfd : fracDist ((k : ℝ) / (Q : ℝ)) = |(k : ℝ) / (Q : ℝ) - (m : ℝ)| := by
    rw [fracDist, ← hm]
  -- (A) `|m| ≤ |k|/Q + 1/2`
  have hm_le : |(m : ℝ)| ≤ |(k : ℝ)| / (Q : ℝ) + 1 / 2 := by
    have htri : |(m : ℝ)| ≤
        |(k : ℝ) / (Q : ℝ)| + |(k : ℝ) / (Q : ℝ) - (m : ℝ)| := by
      calc |(m : ℝ)| = |(k : ℝ) / (Q : ℝ) + ((m : ℝ) - (k : ℝ) / (Q : ℝ))| := by
            congr 1; ring
        _ ≤ |(k : ℝ) / (Q : ℝ)| + |(m : ℝ) - (k : ℝ) / (Q : ℝ)| := abs_add_le _ _
        _ = |(k : ℝ) / (Q : ℝ)| + |(k : ℝ) / (Q : ℝ) - (m : ℝ)| := by rw [abs_sub_comm]
    have hxa : |(k : ℝ) / (Q : ℝ)| = |(k : ℝ)| / (Q : ℝ) := by
      rw [abs_div, abs_of_pos hq]
    have hfdle : |(k : ℝ) / (Q : ℝ) - (m : ℝ)| ≤ 1 / 2 := by
      rw [← hfd]; exact fracDist_le_half' _
    rw [hxa] at htri
    linarith [htri, hfdle]
  -- (B) `|r| ≤ Q/2`
  have hr_le : |(r : ℝ)| ≤ (Q : ℝ) / 2 := by
    have h : fracDist ((k : ℝ) / (Q : ℝ)) ≤ 1 / 2 := fracDist_le_half' _
    have h' : |(k : ℝ) / (Q : ℝ) - (m : ℝ)| ≤ 1 / 2 := by rw [← hfd]; exact h
    rw [hr_mul, abs_mul, abs_of_pos hq]
    nlinarith [h', hq]
  -- use the hypothesis `hk` on `k`
  have hkR : |(k : ℝ)| ≤ 2 * |(y : ℝ)| + B := by
    have h := hk
    rw [Int.cast_abs] at h
    simpa using h
  have hk_div : |(k : ℝ)| / (Q : ℝ) ≤ (2 * |(y : ℝ)| + B) / (Q : ℝ) :=
    div_le_div_of_nonneg_right hkR (le_of_lt hq)
  -- (C) `|m| ≤ 2 (|y|/Q + B/(2Q) + 1)`
  have hm_big : |(m : ℝ)| ≤ 2 * (|(y : ℝ)| / (Q : ℝ) + B / (2 * (Q : ℝ)) + 1) := by
    have hT : 2 * (|(y : ℝ)| / (Q : ℝ) + B / (2 * (Q : ℝ)) + 1)
        = (2 * |(y : ℝ)| + B) / (Q : ℝ) + 2 := by
      field_simp
    rw [hT]
    linarith [hm_le, hk_div]
  have hΔnn : 0 ≤ Δ := by rw [hΔ]; exact fracDist_nonneg' _
  have hmΔ : |(m : ℝ)| * Δ ≤ c / 2 := by
    have h1 : |(m : ℝ)| * Δ
        ≤ 2 * (|(y : ℝ)| / (Q : ℝ) + B / (2 * (Q : ℝ)) + 1) * Δ :=
      mul_le_mul_of_nonneg_right hm_big hΔnn
    linarith [h1, hshift]
  -- the reduced index satisfies the hypothesis of `hred`
  have hred_r : c ≤ fracDist (2 * θ + (r : ℝ) * α) := by
    refine hred r ?_
    rw [Int.cast_abs]
    linarith [hr_le, hq, hB]
  have hb_le : fracDist ((m : ℝ) * ((Q : ℝ) * α)) ≤ |(m : ℝ)| * Δ := by
    calc fracDist ((m : ℝ) * ((Q : ℝ) * α))
        ≤ |(m : ℝ)| * fracDist ((Q : ℝ) * α) := fracDist_zmul_le m ((Q : ℝ) * α)
      _ = |(m : ℝ)| * Δ := by rw [hΔ]
  have hkey : fracDist (2 * θ + (k : ℝ) * α)
      ≥ fracDist (2 * θ + (r : ℝ) * α) - |(m : ℝ)| * Δ := by
    have h := le_fracDist_add' (2 * θ + (r : ℝ) * α) ((m : ℝ) * ((Q : ℝ) * α))
    have heq : 2 * θ + (r : ℝ) * α + (m : ℝ) * ((Q : ℝ) * α) = 2 * θ + (k : ℝ) * α := by
      rw [hr_cast]; ring
    rw [heq] at h
    linarith [h, hb_le]
  linarith [hkey, hred_r, hmΔ]

end Work.TMC16Core.Core
