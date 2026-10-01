import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds

/-!
# Vertical Stirling bounds for `Γ` in a strip `-1 < Re ≤ 2`

`Gamma_vertical_upper_uniform_sharp` gives
`‖Γ(u+iv)‖ ≤ C·(1+|v|)^{u-1/2}·e^{-(π/2)|v|}` on the strip `1/2 ≤ u ≤ 2`.  Here we extend it to

* the half-open strip `a ≤ Re ≤ b` with `-1 < a`, `b ≤ 2` and `|Im| ≥ 1` (use the monotonicity
  `norm_Gamma_le_shift_nat` to move the argument up into `[1/2,2]`);
* a single vertical line `Re = c` with `-1 < c ≤ 2`, `c ≠ 0` and all real `Im` (for `c < 1/2` use
  the recurrence `Γ(z+k) = z(z+1)···(z+k-1)Γ(z)` to shift the argument up into `[1/2,2]`; the
  factors cost only a constant since `|c+j| ≤ |c+j+it|`).
-/

open Complex

namespace Work.LinnikAreas.JutilaPieces

theorem GammaVerticalDecay :
    (∀ a b : ℝ, -1 < a → b ≤ 2 → ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2) * |t|)) ∧
    (∀ c : ℝ, -1 < c → c ≤ 2 → c ≠ 0 → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2) * |t|)) := by
  have hsharp := Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  have hpow3 : ∀ t : ℝ, (1 : ℝ) ≤ (1 + |t|) ^ (3 / 2 : ℝ) := fun t =>
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  constructor
  · -- strip bound for `|Im| ≥ 1`
    intro a b ha hb
    obtain ⟨C0, hC0pos, hC0⟩ := hsharp
    refine ⟨C0, hC0pos, ?_⟩
    intro x hx t ht
    have hx1 : a ≤ x := hx.1
    have hx2 : x ≤ b := hx.2
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (1 / 2 : ℝ) ≤ x + k ∧ x + k ≤ 2 := by
      rcases le_or_gt (1 / 2 : ℝ) x with h | h
      · exact ⟨0, by simpa using h, by push_cast; linarith⟩
      · rcases le_or_gt (-1 / 2 : ℝ) x with h2 | h2
        · exact ⟨1, by push_cast; linarith, by push_cast; linarith⟩
        · exact ⟨2, by push_cast; linarith, by push_cast; linarith⟩
    have him : (((x : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
    have hshift := Commons.Analysis.Complex.norm_Gamma_le_shift_nat
      ((x : ℂ) + (t : ℂ) * Complex.I) (k := k) (by rw [him]; exact ht)
    have hzk : ((x : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ)
        = (((x + k : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    have hkey := hC0 (x + k) t hk1 hk2
    calc ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ‖Complex.Gamma (((x : ℂ) + (t : ℂ) * Complex.I) + (k : ℂ))‖ := hshift
      _ = ‖Complex.Gamma (((x + k : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by rw [hzk]
      _ ≤ C0 * (1 + |t|) ^ (x + k - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|) := hkey
      _ ≤ C0 * (1 + |t|) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) := by
          have hpow : (1 + |t|) ^ (x + k - 1 / 2) ≤ (1 + |t|) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0pos.le)
            (Real.exp_pos _).le
  · -- line bound
    intro c hc1 hc2 hc0
    obtain ⟨C0, hC0pos, hC0⟩ := hsharp
    rcases le_or_gt (1 / 2 : ℝ) c with hc | hc
    · refine ⟨C0, hC0pos, ?_⟩
      intro t
      have hkey := hC0 c t hc (le_trans hc2 le_rfl)
      refine le_trans hkey ?_
      have hpow : (1 + |t|) ^ (c - 1 / 2) ≤ (1 + |t|) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0pos.le)
        (Real.exp_pos _).le
    · rcases le_or_gt (-1 / 2 : ℝ) c with hc' | hc'
      · -- `-1/2 ≤ c < 1/2`, shift by `1`
        refine ⟨C0 / |c|, div_pos hC0pos (abs_pos.mpr hc0), ?_⟩
        intro t
        set z : ℂ := (c : ℂ) + (t : ℂ) * Complex.I with hz
        have hz0 : z ≠ 0 := by
          intro h0
          have h1 := congrArg Complex.re h0
          rw [hz] at h1
          have hre : c = 0 := by simpa using h1
          exact hc0 hre
        have hzc : |c| ≤ ‖z‖ := by
          have h := Complex.abs_re_le_norm z
          rw [hz] at h
          simpa using h
        have hcpos : 0 < |c| := abs_pos.mpr hc0
        have hnorm : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 1)‖ / |c| := by
          rw [Complex.Gamma_add_one z hz0, norm_mul, le_div_iff₀ hcpos]
          calc ‖Complex.Gamma z‖ * |c| ≤ ‖Complex.Gamma z‖ * ‖z‖ :=
                mul_le_mul_of_nonneg_left hzc (norm_nonneg (Complex.Gamma z))
            _ = ‖z‖ * ‖Complex.Gamma z‖ := by ring
        have harg2 : z + 1 = (((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
          rw [hz]; push_cast; ring
        have hkey := hC0 (c + 1) t (by linarith) (by linarith)
        have hpow : (1 + |t|) ^ (c + 1 - 1 / 2) ≤ (1 + |t|) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
        calc ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 1)‖ / |c| := hnorm
          _ = ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ / |c| := by rw [harg2]
          _ ≤ (C0 * (1 + |t|) ^ (c + 1 - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|)) / |c| :=
              div_le_div_of_nonneg_right hkey (abs_nonneg c)
          _ = (C0 / |c|) * ((1 + |t|) ^ (c + 1 - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|)) := by
              ring
          _ ≤ (C0 / |c|) * ((1 + |t|) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2) * |t|)) := by
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hC0pos.le (abs_nonneg c))
              exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          _ = C0 / |c| * (1 + |t|) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) := by ring
      · -- `c < -1/2`, shift by `2`
        refine ⟨C0 / (|c| * |c + 1|), div_pos hC0pos (mul_pos (abs_pos.mpr hc0) (abs_pos.mpr (by linarith))), ?_⟩
        intro t
        set z : ℂ := (c : ℂ) + (t : ℂ) * Complex.I with hz
        have hz0 : z ≠ 0 := by
          intro h0
          have h1 := congrArg Complex.re h0
          rw [hz] at h1
          have hre : c = 0 := by simpa using h1
          exact hc0 hre
        have hz10 : z + 1 ≠ 0 := by
          intro h0
          have h1 := congrArg Complex.re h0
          rw [hz] at h1
          simp at h1
          linarith
        have hzc : |c| ≤ ‖z‖ := by
          have h := Complex.abs_re_le_norm z
          rw [hz] at h
          simpa using h
        have hzc1 : |c + 1| ≤ ‖z + 1‖ := by
          have h := Complex.abs_re_le_norm (z + 1)
          rw [hz, Complex.add_re, Complex.one_re] at h
          simpa using h
        have hcpos : 0 < |c| := abs_pos.mpr hc0
        have hc1pos : 0 < |c + 1| := abs_pos.mpr (by linarith)
        have hnorm : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 2)‖ / (|c| * |c + 1|) := by
          have hG2 : Complex.Gamma (z + 2) = (z + 1) * z * Complex.Gamma z := by
            rw [show z + 2 = (z + 1) + 1 by ring, Complex.Gamma_add_one (z + 1) hz10,
              Complex.Gamma_add_one z hz0]
            ring
          rw [hG2, norm_mul, norm_mul, le_div_iff₀ (mul_pos hcpos hc1pos)]
          have h2 : |c| * |c + 1| ≤ ‖z‖ * ‖z + 1‖ :=
            mul_le_mul hzc hzc1 (abs_nonneg (c + 1)) (norm_nonneg z)
          have h3 : ‖Complex.Gamma z‖ * (|c| * |c + 1|)
              ≤ ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg (Complex.Gamma z))
          have h4 : ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖)
              = ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by ring
          rw [h4] at h3
          exact h3
        have harg2 : z + 2 = (((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
          rw [hz]; push_cast; ring
        have hkey := hC0 (c + 2) t (by linarith) (by linarith)
        have hpow : (1 + |t|) ^ (c + 2 - 1 / 2) ≤ (1 + |t|) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
        calc ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 2)‖ / (|c| * |c + 1|) := hnorm
          _ = ‖Complex.Gamma ((((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ / (|c| * |c + 1|) := by
              rw [harg2]
          _ ≤ (C0 * (1 + |t|) ^ (c + 2 - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|))
                / (|c| * |c + 1|) :=
              div_le_div_of_nonneg_right hkey (by positivity)
          _ = (C0 / (|c| * |c + 1|))
                * ((1 + |t|) ^ (c + 2 - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|)) := by ring
          _ ≤ (C0 / (|c| * |c + 1|))
                * ((1 + |t|) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2) * |t|)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          _ = C0 / (|c| * |c + 1|) * (1 + |t|) ^ (3 / 2 : ℝ)
                * Real.exp (-(Real.pi / 2) * |t|) := by ring

end Work.LinnikAreas.JutilaPieces
