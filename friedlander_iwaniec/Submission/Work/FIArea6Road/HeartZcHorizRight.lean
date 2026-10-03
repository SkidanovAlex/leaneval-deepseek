import Mathlib
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FITop4.Bridge.area5_6_defs

/-!
# The horizontal (right) segment of the §16 contour shift

We bound the horizontal integral
`∫_{1}^{1+1/log N} mellin p (x + iT) · Z_c(x + iT) dx`
by `10^7 (C_z d) (4 log N)^6 · T^{-1} · N · e/log N`.

The point is the oscillatory decay of the Mellin transform of the mollifier `p` on the line
`Re s = 1 + 1/log N`: two integrations by parts give
`‖mellin p (x + iy)‖ ≤ 10^7 θ N^x (1 + (θy)^2)^{-1}` (`S16MellinVerticalBound`), and for
`x ≤ 1 + 1/log N` one has `N^x ≤ e N` while `θ (1+(θy)^2)^{-1} ≤ 1/|y|` for `θ ≤ 1`.  With
`|y| = T` this yields the pointwise bound `10^7 e N / T`, and the remaining factors are the
given bound on `Z_c` and the length `1/log N` of the segment.
-/

namespace Work.FIArea6Road

theorem HeartZcHorizRight
    (Pa : Work.FITop.Params) (p : ℝ → ℝ) (Zc : ℂ → ℂ) (d : ℕ) (C_z : ℝ) (y : ℝ)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ)))
    (hy : |y| = Work.FIArea6Hecke.heightT Pa)
    (hL : 100 ≤ Real.log Pa.N)
    (hZc : ∀ x : ℝ, 1 ≤ x → x ≤ 1 + 1 / Real.log Pa.N →
        ‖Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ)) :
    ‖∫ x in 1..(1 + 1 / Real.log Pa.N), mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)
          * Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (10 ^ 7 * (C_z * (d : ℝ)) * (4 * Real.log Pa.N) ^ (6 : ℕ))
          * (1 / Work.FIArea6Hecke.heightT Pa) * Pa.N * (Real.exp 1 / Real.log Pa.N) := by
  have hNpos : 0 < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hLpos : 0 < Real.log Pa.N := by linarith
  -- `θ ≤ 1`: `θ = (log x)^{-A'}` with `log x > 1`, `A' > 0`
  have hθ1 : Pa.θ ≤ 1 := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have hlogx : 1 < Real.log (Pa.x : ℝ) := lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx3)
    rw [Pa.hθ]
    have hA'pos : 0 < Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt hlogx) (show -Pa.A' ≤ 0 by linarith)
    simpa [Real.rpow_zero] using h
  -- the second derivative bound in the shape used by (16.28)
  have hd2 : ∀ u : ℝ, |iteratedDeriv 2 p u| ≤ 1048576 / (Pa.θ * Pa.N) ^ 2 := by
    intro u
    have h := hpd 2 le_rfl u
    have hcm : Work.FITop4.cMoll 2 = (1048576 : ℝ) := by
      rw [Work.FITop4.cMoll]; norm_num
    rw [hcm] at h
    have hθN : 0 < Pa.θ * Pa.N := mul_pos hθ0 hNpos
    have hpow : (Pa.θ * Pa.N) ^ (-(↑(2 : ℕ) : ℝ)) = ((Pa.θ * Pa.N) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hθN)]
      norm_num
    rw [hpow] at h
    rw [div_eq_mul_inv]
    exact h
  have hTpos : 0 < Work.FIArea6Hecke.heightT Pa := by
    unfold Work.FIArea6Hecke.heightT
    positivity
  have hyne : y ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hy
    linarith
  have hb1 : (1 : ℝ) ≤ 1 + 1 / Real.log Pa.N := by
    have : 0 < 1 / Real.log Pa.N := by positivity
    linarith
  -- the `Z_c` bound is non-negative (evaluate at `x = 1`)
  have hBd : 0 ≤ C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ) :=
    le_trans (norm_nonneg (Zc (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I))) (hZc 1 le_rfl hb1)
  -- pointwise bound on the segment
  have hpoint : ∀ x ∈ Set.uIoc 1 (1 + 1 / Real.log Pa.N),
      ‖mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)
          * Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ (10 ^ 7 * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ))
              * (Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa)) := by
    intro x hx
    rw [Set.uIoc_of_le hb1] at hx
    obtain ⟨hx1, hxle⟩ := hx
    have hxge : 1 ≤ x := le_of_lt hx1
    have hxhalf : 1 / 2 ≤ x := by linarith
    have hx2 : x ≤ 2 := by
      have hd : 1 / Real.log Pa.N ≤ 1 := by rw [div_le_one hLpos]; linarith
      linarith
    have hmellin' := Work.FIArea6.S16MellinVerticalBound p Pa.N Pa.θ x hNpos hθ0 hθ1 hpC hp0
      hp1 hpsupp hd2 hxhalf hx2 y hyne
    have hcm10 : (10000000 : ℝ) = 10 ^ 7 := by norm_num
    have hmellin : ‖mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ 10 ^ 7 * Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹ := by
      rw [← hcm10]; exact hmellin'
    have hZx := hZc x hxge hxle
    have hNxpos : (0 : ℝ) < Pa.N ^ x := Real.rpow_pos_of_pos hNpos x
    have hinvpos : (0 : ℝ) < (1 + (Pa.θ * y) ^ 2)⁻¹ := by
      rw [inv_pos]; positivity
    -- `θ N^x (1 + (θy)^2)^{-1} ≤ e N / T`
    have hkey : Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹
        ≤ Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa := by
      have hNx : Pa.N ^ x ≤ Real.exp 1 * Pa.N := by
        have h1 : Pa.N ^ x ≤ Pa.N ^ (1 + 1 / Real.log Pa.N) :=
          Real.rpow_le_rpow_of_exponent_le Pa.hN1 hxle
        have hexp : Pa.N ^ (1 / Real.log Pa.N) = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hNpos]
          rw [show Real.log Pa.N * (1 / Real.log Pa.N) = 1 by field_simp]
        have h2 : Pa.N ^ (1 + 1 / Real.log Pa.N) = Real.exp 1 * Pa.N := by
          rw [Real.rpow_add hNpos, Real.rpow_one, hexp]
          ring
        rw [h2] at h1
        exact h1
      have hy2 : y ^ 2 = Work.FIArea6Hecke.heightT Pa ^ 2 := by
        rw [← sq_abs, hy]
      have hsq : (Pa.θ * y) ^ 2 = (Pa.θ * Work.FIArea6Hecke.heightT Pa) ^ 2 := by
        rw [mul_pow, mul_pow, hy2]
      have hratio : Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹
          ≤ 1 / Work.FIArea6Hecke.heightT Pa := by
        rw [hsq, inv_eq_one_div, mul_one_div]
        rw [div_le_div_iff₀ (by positivity) hTpos]
        nlinarith [sq_nonneg (Pa.θ * Work.FIArea6Hecke.heightT Pa - 1 / 2)]
      calc Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹
          = (Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹) * Pa.N ^ x := by ring
        _ ≤ (1 / Work.FIArea6Hecke.heightT Pa) * (Real.exp 1 * Pa.N) :=
            mul_le_mul hratio hNx (le_of_lt hNxpos) (by positivity)
        _ = Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa := by ring
    calc ‖mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)
            * Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
        = ‖mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)‖
            * ‖Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖ := norm_mul _ _
      _ ≤ (10 ^ 7 * Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹)
            * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ)) :=
          mul_le_mul hmellin hZx (norm_nonneg _) (le_trans (norm_nonneg _) hmellin)
      _ ≤ 10 ^ 7 * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ))
            * (Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa) := by
          have h10 : (0 : ℝ) ≤ 10 ^ 7 := by norm_num
          have hstep : 10 ^ 7 * (Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹)
              ≤ 10 ^ 7 * (Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa) :=
            mul_le_mul_of_nonneg_left hkey h10
          calc (10 ^ 7 * Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹)
                  * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ))
              = (10 ^ 7 * (Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹))
                  * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ)) := by ring
            _ ≤ (10 ^ 7 * (Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa))
                  * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ)) :=
                mul_le_mul_of_nonneg_right hstep hBd
            _ = 10 ^ 7 * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ))
                  * (Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa) := by ring
  have habs : |(1 + 1 / Real.log Pa.N) - 1| = 1 / Real.log Pa.N := by
    rw [show (1 + 1 / Real.log Pa.N) - 1 = 1 / Real.log Pa.N by ring]
    exact abs_of_pos (by positivity)
  calc ‖∫ x in 1..(1 + 1 / Real.log Pa.N),
          mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)
            * Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (10 ^ 7 * (C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ))
            * (Real.exp 1 * Pa.N / Work.FIArea6Hecke.heightT Pa))
          * |(1 + 1 / Real.log Pa.N) - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (10 ^ 7 * (C_z * (d : ℝ)) * (4 * Real.log Pa.N) ^ (6 : ℕ))
          * (1 / Work.FIArea6Hecke.heightT Pa) * Pa.N * (Real.exp 1 / Real.log Pa.N) := by
        rw [habs]; ring

end Work.FIArea6Road
