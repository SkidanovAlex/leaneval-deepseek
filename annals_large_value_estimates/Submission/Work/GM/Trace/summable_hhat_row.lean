import Mathlib
import Submission.Work.GM.Trace.Defs
import Submission.Work.GM.Trace.hhat_decay_deriv

namespace Work.GM.Trace

open Submission.GM

-- The dominating sequence `m ↦ (1+|m|)^{-2}` on `ℤ` is summable.
theorem summable_inv_sq_one_add_abs_int : Summable (fun m : ℤ => ((1 + |(m:ℝ)|)^2)⁻¹) := by
  have hf : Summable (fun n : ℤ => ((|(n:ℝ)|)^2)⁻¹) := by
    have h := Real.summable_abs_int_rpow (b := (2:ℝ)) (by norm_num)
    refine h.congr (fun m => ?_)
    rw [Real.rpow_neg (abs_nonneg _)]
    congr 1
    exact Real.rpow_natCast _ 2
  have h0 : Summable (fun n : ℤ => if n = 0 then (1:ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro m hm; simp at hm; simp [hm])
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hf.add h0)
  by_cases hn : n = 0
  · subst hn; simp
  · have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
      have hz : (1:ℤ) ≤ |n| := Int.one_le_abs hn
      rw [← Int.cast_abs]
      exact_mod_cast hz
    simp only [hn, if_false, add_zero]
    have hpos : (0:ℝ) < |(n:ℝ)|^2 := by positivity
    have hle : |(n:ℝ)|^2 ≤ (1 + |(n:ℝ)|)^2 := by nlinarith [abs_nonneg (n:ℝ)]
    exact inv_anti₀ hpos hle

-- Absolute summability of the one-dimensional `m`-sum `m ↦ ĥ_t(mN)` appearing in Poisson
-- summation (needed as the `hsum` hypothesis of `Work.GM.Trace.trace_three_identity`).
-- From the decay hypothesis (take `j = 2`) each term is
-- `≤ C (1+|t|)^2 / (|m| N)^2`, and `Σ_{m ≠ 0} 1/m² < ∞`.
theorem summable_hhat_row (N : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (hdec : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j) :
    Summable (fun m : ℤ => Submission.GM.hhat t ((m : ℝ) * (N : ℝ))) := by
  obtain ⟨C, hCnonneg, hC⟩ := hdec 2
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := by positivity
  -- `B` is the constant of the `j = 2` decay bound, `K` absorbs the `m = 0` term as well.
  set B : ℝ := C * (1 + |t|) ^ 2 with hBdef
  have hBnonneg : 0 ≤ B := by rw [hBdef]; positivity
  set K : ℝ := max (4*B) ‖Submission.GM.hhat t 0‖ with hKdef
  have h4B : 4*B ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK0 : ‖Submission.GM.hhat t 0‖ ≤ K := by rw [hKdef]; exact le_max_right _ _
  refine Summable.of_norm_bounded (summable_inv_sq_one_add_abs_int.mul_left K) (fun m => ?_)
  by_cases hm : m = 0
  · subst hm
    have hsimp : ((1 + |(((0:ℤ)):ℝ)|)^2)⁻¹ = (1:ℝ) := by norm_num
    rw [show (((0:ℤ)):ℝ) * (N:ℝ) = 0 by norm_num, hsimp, mul_one]
    exact hK0
  · have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
    have hξne : (m:ℝ) * (N:ℝ) ≠ 0 := mul_ne_zero hmR hNne
    have hm1 : (1:ℝ) ≤ |(m:ℝ)| := by
      have hz : (1:ℤ) ≤ |m| := Int.one_le_abs hm
      rw [← Int.cast_abs]
      exact_mod_cast hz
    have hb1 : ‖Submission.GM.hhat t ((m:ℝ)*(N:ℝ))‖ ≤ B / |(m:ℝ)*(N:ℝ)|^2 := by
      rw [hBdef]
      exact hC t _ hξne
    have hξabs : |(m:ℝ)*(N:ℝ)| = |(m:ℝ)| * (N:ℝ) := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ))]
    -- `(1+|m|)^2 ≤ 4 (|m| N)^2`, since `|m| ≥ 1` and `N ≥ 1`.
    have hs2 : (1 + |(m:ℝ)|)^2 ≤ 4 * |(m:ℝ)*(N:ℝ)|^2 := by
      rw [hξabs]
      have hx : 0 ≤ |(m:ℝ)| - 1 := by linarith
      have h3x : 0 ≤ 3*|(m:ℝ)| + 1 := by linarith [abs_nonneg (m:ℝ)]
      have hprod : 0 ≤ (|(m:ℝ)| - 1) * (3*|(m:ℝ)| + 1) := mul_nonneg hx h3x
      have hN2 : 1 ≤ (N:ℝ)^2 := by nlinarith [hN1]
      nlinarith [hprod, hN2, abs_nonneg (m:ℝ), hm1]
    have ha2pos : 0 < (1 + |(m:ℝ)|)^2 := by positivity
    have hs2pos : 0 < |(m:ℝ)*(N:ℝ)|^2 := by
      have hne : |(m:ℝ)*(N:ℝ)| ≠ 0 := abs_ne_zero.mpr hξne
      positivity
    have hkey : B / |(m:ℝ)*(N:ℝ)|^2 ≤ K * ((1 + |(m:ℝ)|)^2)⁻¹ := by
      have h1 : B / |(m:ℝ)*(N:ℝ)|^2 ≤ K / (1 + |(m:ℝ)|)^2 := by
        rw [div_le_div_iff₀ hs2pos ha2pos]
        calc B * (1 + |(m:ℝ)|)^2 ≤ B * (4 * |(m:ℝ)*(N:ℝ)|^2) :=
              mul_le_mul_of_nonneg_left hs2 hBnonneg
          _ = (4*B) * |(m:ℝ)*(N:ℝ)|^2 := by ring
          _ ≤ K * |(m:ℝ)*(N:ℝ)|^2 := mul_le_mul_of_nonneg_right h4B (le_of_lt hs2pos)
      rwa [div_eq_mul_inv] at h1
    exact hb1.trans hkey

end Work.GM.Trace
