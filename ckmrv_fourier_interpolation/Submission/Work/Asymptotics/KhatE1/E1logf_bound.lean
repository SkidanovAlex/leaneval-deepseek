import Mathlib

/-!
# A fourth order bound for the `E₁` logarithmic combination

For `‖z‖ ≤ 1/2` the combination
`P(z) * log (1 - z) + (9/2) z² (1-z)² (1-z+z²)`, where
`P(z) = (9/2)z - (63/4)z² + (45/2)z³ - (45/2)z⁴ + (45/2)z⁵ - (63/4)z⁶ + (9/2)z⁷`,
vanishes to order `4` at `z = 0`; here we record the resulting `O(‖z‖⁴)` bound.

The proof expands `log (1 - z) = -z - z²/2 - z³/3 + E(z)` with `‖E(z)‖ ≤ ‖z‖⁴/2`
(`Complex.norm_log_sub_logTaylor_le`), and verifies that
`P(z)·(-z - z²/2 - z³/3) + (9/2)z²(1-z)²(1-z+z²) = z⁴·R(z)`
for the explicit polynomial `R(z) = 15/8 + 3z - (57/4)z² + 12z³ - (33/8)z⁴ + 3z⁵ - (3/2)z⁶`.
-/

namespace Work.Asymptotics.KhatE1

open Finset

/-- Sum bound for a polynomial with finitely many monomials on the unit disk. -/
private lemma e1logf_norm_fin_poly_le {n : ℕ} (c : Fin n → ℂ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖∑ k : Fin n, c k * z^(k:ℕ)‖ ≤ ∑ k : Fin n, ‖c k‖ := by
  calc ‖∑ k : Fin n, c k * z^(k:ℕ)‖
      ≤ ∑ k : Fin n, ‖c k * z^(k:ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin n, ‖c k‖ := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_pow]
        calc ‖c k‖ * ‖z‖ ^ (k:ℕ) ≤ ‖c k‖ * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz) (norm_nonneg _)
          _ = ‖c k‖ := by ring

/-- Coefficient vector of the polynomial `P`. -/
private noncomputable def e1logf_Pvec : Fin 8 → ℂ :=
  ![0, 9/2, -63/4, 45/2, -45/2, 45/2, -63/4, 9/2]

/-- Coefficient vector of the polynomial `R`. -/
private noncomputable def e1logf_Rvec : Fin 7 → ℂ :=
  ![15/8, 3, -57/4, 12, -33/8, 3, -3/2]

private lemma e1logf_Pvec_sum (z : ℂ) :
    (∑ k : Fin 8, e1logf_Pvec k * z^(k:ℕ))
      = ((9:ℂ)/2)*z - ((63:ℂ)/4)*z^2 + ((45:ℂ)/2)*z^3 - ((45:ℂ)/2)*z^4
        + ((45:ℂ)/2)*z^5 - ((63:ℂ)/4)*z^6 + ((9:ℂ)/2)*z^7 := by
  unfold e1logf_Pvec
  rw [Fin.sum_univ_eight]
  simp
  ring

private lemma e1logf_Rvec_sum (z : ℂ) :
    (∑ k : Fin 7, e1logf_Rvec k * z^(k:ℕ))
      = ((15:ℂ)/8) + 3*z - ((57:ℂ)/4)*z^2 + 12*z^3 - ((33:ℂ)/8)*z^4 + 3*z^5
        - ((3:ℂ)/2)*z^6 := by
  unfold e1logf_Rvec
  rw [Fin.sum_univ_seven]
  simp
  ring

private lemma e1logf_norm_Pvec_le (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖((9:ℂ)/2)*z - ((63:ℂ)/4)*z^2 + ((45:ℂ)/2)*z^3 - ((45:ℂ)/2)*z^4
        + ((45:ℂ)/2)*z^5 - ((63:ℂ)/4)*z^6 + ((9:ℂ)/2)*z^7‖ ≤ 108 := by
  rw [← e1logf_Pvec_sum z]
  calc ‖∑ k : Fin 8, e1logf_Pvec k * z ^ (k:ℕ)‖
      ≤ ∑ k : Fin 8, ‖e1logf_Pvec k‖ := e1logf_norm_fin_poly_le e1logf_Pvec z hz
    _ = 108 := by unfold e1logf_Pvec; rw [Fin.sum_univ_eight]; simp; norm_num

private lemma e1logf_norm_Rvec_le (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖((15:ℂ)/8) + 3*z - ((57:ℂ)/4)*z^2 + 12*z^3 - ((33:ℂ)/8)*z^4 + 3*z^5
        - ((3:ℂ)/2)*z^6‖ ≤ 159/4 := by
  rw [← e1logf_Rvec_sum z]
  calc ‖∑ k : Fin 7, e1logf_Rvec k * z ^ (k:ℕ)‖
      ≤ ∑ k : Fin 7, ‖e1logf_Rvec k‖ := e1logf_norm_fin_poly_le e1logf_Rvec z hz
    _ = 159/4 := by unfold e1logf_Rvec; rw [Fin.sum_univ_seven]; simp; norm_num

/-- `logTaylor 4 (-z) = -z - z²/2 - z³/3`. -/
private lemma e1logf_logTaylor_four_neg (z : ℂ) :
    Complex.logTaylor 4 (-z) = -z - z^2/2 - z^3/3 := by
  simp [Complex.logTaylor, Finset.sum_range_succ]
  ring

/-- The remainder of the logarithm expansion is `O(‖z‖⁴)` with constant `1/2`. -/
private lemma e1logf_log_one_sub_bound (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖Complex.log (1 - z) + z + z^2/2 + z^3/3‖ ≤ ‖z‖^4 / 2 := by
  have hzlt : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 (z := -z) hzlt
  have h2 : Complex.log (1 + -z) - Complex.logTaylor 4 (-z)
      = Complex.log (1 - z) + z + z^2/2 + z^3/3 := by
    have hz' : (1:ℂ) + -z = 1 - z := by ring
    rw [hz', e1logf_logTaylor_four_neg]
    ring
  rw [show (3:ℕ) + 1 = 4 from rfl] at h
  rw [h2] at h
  simp only [norm_neg] at h
  rw [show ((↑(3:ℕ) : ℝ) + 1) = 4 by norm_num] at h
  refine h.trans ?_
  have hpos : (0:ℝ) < 1 - ‖z‖ := by linarith [norm_nonneg z]
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have hh : (1:ℝ)/2 ≤ 1 - ‖z‖ := by linarith [norm_nonneg z]
    calc (1 - ‖z‖)⁻¹ ≤ ((1:ℝ)/2)⁻¹ := by
          rw [inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 1/2)]
          exact hh
      _ = 2 := by norm_num
  calc ‖z‖ ^ 4 * (1 - ‖z‖)⁻¹ / 4 ≤ ‖z‖ ^ 4 * 2 / 4 := by gcongr
    _ = ‖z‖^4 / 2 := by ring

theorem E1logf_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1/2 →
      ‖(((9:ℂ)/2)*z - ((63:ℂ)/4)*z^2 + ((45:ℂ)/2)*z^3 - ((45:ℂ)/2)*z^4
          + ((45:ℂ)/2)*z^5 - ((63:ℂ)/4)*z^6 + ((9:ℂ)/2)*z^7) * Complex.log (1 - z)
        + ((9:ℂ)/2)*z^2*(1-z)^2*(1-z+z^2)‖ ≤ C * ‖z‖^4 := by
  refine ⟨100, by norm_num, ?_⟩
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by linarith
  have hR := e1logf_norm_Rvec_le z hz1
  have hP := e1logf_norm_Pvec_le z hz1
  have hE := e1logf_log_one_sub_bound z hz
  set R : ℂ := ((15:ℂ)/8) + 3*z - ((57:ℂ)/4)*z^2 + 12*z^3 - ((33:ℂ)/8)*z^4 + 3*z^5
      - ((3:ℂ)/2)*z^6 with hRdef
  set P : ℂ := ((9:ℂ)/2)*z - ((63:ℂ)/4)*z^2 + ((45:ℂ)/2)*z^3 - ((45:ℂ)/2)*z^4
        + ((45:ℂ)/2)*z^5 - ((63:ℂ)/4)*z^6 + ((9:ℂ)/2)*z^7 with hPdef
  set E : ℂ := Complex.log (1 - z) + z + z^2/2 + z^3/3 with hEdef
  have hR' : ‖R‖ ≤ 159/4 := by rw [hRdef]; exact hR
  have hP' : ‖P‖ ≤ 108 := by rw [hPdef]; exact hP
  have hE' : ‖E‖ ≤ ‖z‖^4/2 := by rw [hEdef]; exact hE
  have hkey : P * Complex.log (1 - z) + ((9:ℂ)/2)*z^2*(1-z)^2*(1-z+z^2)
      = z^4 * R + P * E := by
    rw [hPdef, hRdef, hEdef]; ring
  rw [hkey]
  calc ‖z^4 * R + P * E‖
      ≤ ‖z^4 * R‖ + ‖P * E‖ := norm_add_le _ _
    _ = ‖z‖^4 * ‖R‖ + ‖P‖ * ‖E‖ := by rw [norm_mul, norm_mul, norm_pow]
    _ ≤ ‖z‖^4 * (159/4) + 108 * (‖z‖^4/2) := by gcongr
    _ = ‖z‖^4 * (159/4 + 54) := by ring
    _ ≤ 100 * ‖z‖^4 := by nlinarith [pow_nonneg (norm_nonneg z) 4]

end Work.Asymptotics.KhatE1
