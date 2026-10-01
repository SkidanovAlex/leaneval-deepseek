import Mathlib

namespace Work.LinnikAreas.l31free

/-- The factor `(2 + |T|)^d · (log(N·(2+|T|)) + 2)` with `0 ≤ d ≤ 1/6` is absorbed by
`C · N^η · (1 + |T|)` for a constant `C` depending only on `η > 0`.

Writing `x = 2 + |T| ≥ 2` and `n = N ≥ 1`, we have `x^d ≤ x^(1/6) = x · x^(-5/6)`, and
`log(n x) + 2 = log n + log x + 2`. The two logarithmic terms are then controlled by
`log n ≤ n^η/η` and `log x ≤ (6/5) x^(5/6)`, so that
`x^(-5/6)(log n + log x + 2) ≤ (1/η + 2 + 6/5) n^η`; multiplying by `x ≤ 2(1 + |T|)`
gives the claim with `C = 2(1/η + 2 + 6/5)`. -/
lemma absorb_log_factor {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T d : ℝ), 1 ≤ N → 0 ≤ d → d ≤ 1/6 →
      (2 + |T|) ^ d * (Real.log ((N : ℝ) * (2 + |T|)) + 2) ≤
        C * (N : ℝ) ^ η * (1 + |T|) := by
  refine ⟨2 * (1/η + 2 + 6/5), ?_, ?_⟩
  · have h1 : 0 < 1/η := one_div_pos.mpr hη
    linarith
  · intro N T d hN hd0 hd6
    set n : ℝ := (N:ℝ) with hn_def
    set x : ℝ := 2 + |T| with hx_def
    have hn1 : (1:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hN
    have hnpos : 0 < n := by linarith
    have hx2 : (2:ℝ) ≤ x := by
      rw [hx_def]; exact le_add_of_nonneg_right (abs_nonneg T)
    have hx1 : (1:ℝ) ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hnη1 : (1:ℝ) ≤ n^η := Real.one_le_rpow hn1 (le_of_lt hη)
    have hnηpos : 0 < n^η := Real.rpow_pos_of_pos hnpos η
    have hlogfact : Real.log (n * x) = Real.log n + Real.log x :=
      Real.log_mul (ne_of_gt hnpos) (ne_of_gt hxpos)
    have hlnn : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlnx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxpow : x^d ≤ x^((1:ℝ)/6) := Real.rpow_le_rpow_of_exponent_le hx1 hd6
    have hbr : 0 ≤ Real.log n + Real.log x + 2 := by linarith
    have hstep1 : x^d * (Real.log (n * x) + 2) ≤ x^((1:ℝ)/6) * (Real.log n + Real.log x + 2) := by
      rw [hlogfact]
      exact mul_le_mul_of_nonneg_right hxpow hbr
    have hpow1 : x^((1:ℝ)/6) = x * x^(((-5:ℝ))/6) := by
      have h := Real.rpow_add hxpos (1:ℝ) ((-5:ℝ)/6)
      rw [show (1:ℝ) + (-5:ℝ)/6 = (1:ℝ)/6 by norm_num, Real.rpow_one] at h
      exact h
    have hsplit : x^((1:ℝ)/6) * (Real.log n + Real.log x + 2)
        = x * (x^(((-5:ℝ))/6) * (Real.log n + Real.log x + 2)) := by
      rw [hpow1]; ring
    have hxnn : 0 ≤ x^(((-5:ℝ))/6) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hxle : x^(((-5:ℝ))/6) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 (show ((-5:ℝ)/6) ≤ 0 by norm_num)
      rwa [Real.rpow_zero] at h
    have hS1 : x^(((-5:ℝ))/6) * (Real.log n + 2) ≤ (1/η + 2) * n^η := by
      have hlogn : Real.log n ≤ (1/η) * n^η := by
        calc Real.log n ≤ n^η / η := Real.log_le_rpow_div (le_of_lt hnpos) hη
          _ = (1/η) * n^η := by ring
      have h2 : (2:ℝ) ≤ 2 * n^η := by linarith
      calc x^(((-5:ℝ))/6) * (Real.log n + 2) ≤ 1 * (Real.log n + 2) := by
            apply mul_le_mul_of_nonneg_right hxle; linarith
        _ = Real.log n + 2 := by ring
        _ ≤ (1/η + 2) * n^η := by nlinarith [hlogn, h2]
    have hS2 : x^(((-5:ℝ))/6) * Real.log x ≤ (6/5) * n^η := by
      have hlogx : Real.log x ≤ x^((5:ℝ)/6) / (5/6) :=
        Real.log_le_rpow_div (le_of_lt hxpos) (show (0:ℝ) < 5/6 by norm_num)
      have hmul : x^(((-5:ℝ))/6) * Real.log x ≤ x^(((-5:ℝ))/6) * (x^((5:ℝ)/6) / (5/6)) :=
        mul_le_mul_of_nonneg_left hlogx hxnn
      have hxx : x^(((-5:ℝ))/6) * x^((5:ℝ)/6) = 1 := by
        have h := Real.rpow_add hxpos ((-5:ℝ)/6) ((5:ℝ)/6)
        rw [show (-5:ℝ)/6 + (5:ℝ)/6 = 0 by norm_num, Real.rpow_zero] at h
        exact h.symm
      have hprod : x^(((-5:ℝ))/6) * (x^((5:ℝ)/6) / (5/6)) = 6/5 := by
        rw [← mul_div_assoc, hxx]; norm_num
      calc x^(((-5:ℝ))/6) * Real.log x ≤ x^(((-5:ℝ))/6) * (x^((5:ℝ)/6) / (5/6)) := hmul
        _ = 6/5 := hprod
        _ ≤ (6/5) * n^η := by nlinarith [hnη1]
    have hS : x^(((-5:ℝ))/6) * (Real.log n + Real.log x + 2) ≤ (1/η + 2 + 6/5) * n^η := by
      have key : x^(((-5:ℝ))/6) * (Real.log n + Real.log x + 2)
          = x^(((-5:ℝ))/6) * (Real.log n + 2) + x^(((-5:ℝ))/6) * Real.log x := by ring
      rw [key]
      linarith [hS1, hS2]
    have hSx : x * (x^(((-5:ℝ))/6) * (Real.log n + Real.log x + 2))
        ≤ x * ((1/η + 2 + 6/5) * n^η) :=
      mul_le_mul_of_nonneg_left hS (le_of_lt hxpos)
    have hmain : x^d * (Real.log (n * x) + 2) ≤ (1/η + 2 + 6/5) * n^η * x := by
      calc x^d * (Real.log (n * x) + 2)
          ≤ x^((1:ℝ)/6) * (Real.log n + Real.log x + 2) := hstep1
        _ = x * (x^(((-5:ℝ))/6) * (Real.log n + Real.log x + 2)) := hsplit
        _ ≤ x * ((1/η + 2 + 6/5) * n^η) := hSx
        _ = (1/η + 2 + 6/5) * n^η * x := by ring
    have hxT : x ≤ 2 * (1 + |T|) := by
      rw [hx_def]; nlinarith [abs_nonneg T]
    have hmidn : 0 ≤ (1/η + 2 + 6/5) * n^η := by
      have h1 : 0 < 1/η := one_div_pos.mpr hη
      positivity
    have hmid : (1/η + 2 + 6/5) * n^η * x ≤ (1/η + 2 + 6/5) * n^η * (2 * (1 + |T|)) :=
      mul_le_mul_of_nonneg_left hxT hmidn
    show x^d * (Real.log (n * x) + 2) ≤ 2 * (1/η + 2 + 6/5) * n^η * (1 + |T|)
    calc x^d * (Real.log (n * x) + 2)
        ≤ (1/η + 2 + 6/5) * n^η * x := hmain
      _ ≤ (1/η + 2 + 6/5) * n^η * (2 * (1 + |T|)) := hmid
      _ = 2 * (1/η + 2 + 6/5) * n^η * (1 + |T|) := by ring

end Work.LinnikAreas.l31free
