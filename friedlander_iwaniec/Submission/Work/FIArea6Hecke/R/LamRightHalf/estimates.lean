/-
# `Submission.Work.FIArea6Hecke.R.LamRightHalf.estimates`

Two elementary estimates used in the growth bound for the completed Hecke `L`-function on the
right half-plane:

* `heckeLSeries_bound_re_ge_two`: the Hecke `L`-series is bounded on `re s ≥ 2` (absolute
  convergence of `Σ λ(n)n^{-2}` with `‖λ(n)‖ ≤ 4τ(n)`);

* `logGrowthArith`: the real-variable bookkeeping turning the Stirling growth
  `log‖Γ‖ ≪ (1+t)(1+log t)` plus a linear term and a constant into the shape
  `c·(t+3)·(log(t+5)+1)` used in `lamRightHalf_strict`, with the explicit constant
  `c = (X+1) + C + C(μ+1)(2 + log(μ+1)) + |log A| + 1`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators LSeries.notation

noncomputable section

theorem heckeLSeries_bound_re_ge_two {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s‖ ≤ A := by
  refine ⟨∑' n : ℕ, 4 * (n.divisors.card : ℝ) * (n : ℝ) ^ (-2 : ℝ),
    tsum_nonneg (fun n => by positivity), ?_⟩
  intro s hs
  have hbase : Summable (fun n : ℕ => 4 * (n.divisors.card : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by
    refine ((Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg (σ := 2)
      (by norm_num)).mul_left 4).congr (fun n => ?_)
    ring
  have hbnd : ∀ n : ℕ, ‖LSeries.term (Work.FIArea5.S16Hecke.heckeLam chi (m : ℤ)) s n‖
      ≤ 4 * (n.divisors.card : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · rw [if_pos hn]
      positivity
    · rw [if_neg hn]
      have hn1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hlam := Work.FIArea5.S16Hecke.heckeLam_bound chi (m : ℤ) hchi hn1
      have hexp : (n : ℝ) ^ (-(s.re)) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
      calc ‖Work.FIArea5.S16Hecke.heckeLam chi (m : ℤ) n‖ / (n : ℝ) ^ s.re
          = ‖Work.FIArea5.S16Hecke.heckeLam chi (m : ℤ) n‖ * (n : ℝ) ^ (-(s.re)) := by
            rw [Real.rpow_neg hnpos.le]; ring
        _ ≤ 4 * (n.divisors.card : ℝ) * (n : ℝ) ^ (-(s.re)) :=
            mul_le_mul_of_nonneg_right hlam (Real.rpow_nonneg hnpos.le _)
        _ ≤ 4 * (n.divisors.card : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
  have hsumm : LSeriesSummable (Work.FIArea5.S16Hecke.heckeLam chi (m : ℤ)) s :=
    Summable.of_norm_bounded hbase hbnd
  rw [Work.FIArea5.S16Hecke.heckeLSeries, LSeries]
  exact le_trans (norm_tsum_le_tsum_norm hsumm.norm)
    (Summable.tsum_le_tsum hbnd hsumm.norm hbase)

/-- The real-variable bookkeeping for the right half-plane growth bound. -/
theorem logGrowthArith (X C A μ t : ℝ) (hX : 0 ≤ X) (hC : 0 < C) (hμ : 0 ≤ μ) (ht : 0 ≤ t) :
    t * X + (C * (1 + (t + μ + 1) * (1 + Real.log (2 + t + μ))) + Real.log A)
      ≤ ((X + 1) + C + C * (μ + 1) * (2 + Real.log (μ + 1)) + |Real.log A| + 1)
          * (t + 3) * (Real.log (t + 5) + 1) := by
  have hlogt : 0 ≤ Real.log (t + 5) := Real.log_nonneg (by linarith)
  have hlogμ : 0 ≤ Real.log (μ + 1) := Real.log_nonneg (by linarith)
  set R : ℝ := (t + 3) * (Real.log (t + 5) + 1) with hR
  have hR1 : 1 ≤ R := by rw [hR]; nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hP1 : t * X ≤ (X + 1) * R := by
    have h1 : t * X ≤ (t + 3) * (X + 1) := by nlinarith
    have h4 : (1 : ℝ) ≤ Real.log (t + 5) + 1 := by linarith
    have h5 : (0 : ℝ) ≤ (t + 3) * (X + 1) := by nlinarith
    calc t * X ≤ (t + 3) * (X + 1) := h1
      _ = (t + 3) * (X + 1) * 1 := by ring
      _ ≤ (t + 3) * (X + 1) * (Real.log (t + 5) + 1) := mul_le_mul_of_nonneg_left h4 h5
      _ = (X + 1) * R := by rw [hR]; ring
  have hP2 : C ≤ C * R := by
    calc C = C * 1 := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_left hR1 hC.le
  have ha : t + μ + 1 ≤ (μ + 1) * (t + 3) := by nlinarith
  have hb : 1 + Real.log (2 + t + μ) ≤ (2 + Real.log (μ + 1)) * (Real.log (t + 5) + 1) := by
    have harg : 2 + t + μ ≤ (μ + 1) * (t + 3) := by nlinarith
    have hlog : Real.log (2 + t + μ) ≤ Real.log (μ + 1) + Real.log (t + 3) := by
      rw [← Real.log_mul (by linarith : (μ + 1) ≠ 0) (by linarith : (t + 3) ≠ 0)]
      exact Real.log_le_log (by linarith) harg
    have hlogt3 : Real.log (t + 3) ≤ Real.log (t + 5) :=
      Real.log_le_log (by linarith) (by linarith)
    have hab : 0 ≤ Real.log (μ + 1) * Real.log (t + 5) := mul_nonneg hlogμ hlogt
    nlinarith [hlog, hlogt3, hlogμ, hlogt, hab]
  have hP3 : C * (t + μ + 1) * (1 + Real.log (2 + t + μ))
      ≤ C * (μ + 1) * (2 + Real.log (μ + 1)) * R := by
    have ha0 : (0 : ℝ) ≤ t + μ + 1 := by linarith
    have hb0 : (0 : ℝ) ≤ 1 + Real.log (2 + t + μ) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + t + μ)
      linarith
    have hCa : C * (t + μ + 1) ≤ C * (μ + 1) * (t + 3) := by
      calc C * (t + μ + 1) ≤ C * ((μ + 1) * (t + 3)) := mul_le_mul_of_nonneg_left ha hC.le
        _ = C * (μ + 1) * (t + 3) := by ring
    calc C * (t + μ + 1) * (1 + Real.log (2 + t + μ))
        ≤ (C * (μ + 1) * (t + 3)) * ((2 + Real.log (μ + 1)) * (Real.log (t + 5) + 1)) :=
          mul_le_mul hCa hb hb0 (by positivity)
      _ = C * (μ + 1) * (2 + Real.log (μ + 1)) * R := by rw [hR]; ring
  have hP4 : Real.log A ≤ |Real.log A| * R := by
    have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
    have h2 : |Real.log A| ≤ |Real.log A| * R := by
      calc |Real.log A| = |Real.log A| * 1 := by ring
        _ ≤ |Real.log A| * R := mul_le_mul_of_nonneg_left hR1 (abs_nonneg _)
    linarith
  have key : t * X + (C * (1 + (t + μ + 1) * (1 + Real.log (2 + t + μ))) + Real.log A)
      ≤ ((X + 1) + C + C * (μ + 1) * (2 + Real.log (μ + 1)) + |Real.log A|) * R := by
    have hexp : t * X + (C * (1 + (t + μ + 1) * (1 + Real.log (2 + t + μ))) + Real.log A)
        = t * X + (C + C * (t + μ + 1) * (1 + Real.log (2 + t + μ)) + Real.log A) := by ring
    rw [hexp]
    nlinarith [hP1, hP2, hP3, hP4]
  calc t * X + (C * (1 + (t + μ + 1) * (1 + Real.log (2 + t + μ))) + Real.log A)
      ≤ ((X + 1) + C + C * (μ + 1) * (2 + Real.log (μ + 1)) + |Real.log A|) * R := key
    _ ≤ ((X + 1) + C + C * (μ + 1) * (2 + Real.log (μ + 1)) + |Real.log A| + 1) * R := by
        have hK : (0 : ℝ) ≤ (X + 1) + C + C * (μ + 1) * (2 + Real.log (μ + 1)) + |Real.log A| := by
          have hCm : (0 : ℝ) ≤ C * (μ + 1) * (2 + Real.log (μ + 1)) := by positivity
          linarith [abs_nonneg (Real.log A), hC.le, hμ]
        nlinarith [hK, hR1, hR0]
    _ = ((X + 1) + C + C * (μ + 1) * (2 + Real.log (μ + 1)) + |Real.log A| + 1)
          * (t + 3) * (Real.log (t + 5) + 1) := by rw [hR]; ring

end

end Work.FIArea6Hecke.R
