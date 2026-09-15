import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Complex.Blaschke

/-- Algebraic identity underlying the Blaschke factor bound:
`|r^2 - ū z|^2 - |r (z-u)|^2 = (r^2 - |z|^2) (r^2 - |u|^2)`. -/
lemma normSq_blaschke_key (r : ℝ) (u z : ℂ) :
    Complex.normSq ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)
        - Complex.normSq ((r : ℂ) * (z - u))
      = (r ^ 2 - Complex.normSq z) * (r ^ 2 - Complex.normSq u) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow]
  ring

/-- The denominator `r^2 - ū z` of the Blaschke factor does not vanish when
`‖z‖ ≤ r` and `‖u‖ < r`. -/
lemma blaschke_denom_ne_zero {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ < r)
    (hz : ‖z‖ ≤ r) :
    (r : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 := by
  intro h
  have hconj : (starRingEnd ℂ) u * z = (r : ℂ) ^ 2 := (sub_eq_zero.mp h).symm
  have hnorm : ‖(starRingEnd ℂ) u * z‖ = r ^ 2 := by
    rw [hconj, norm_pow,
      show ‖(r : ℂ)‖ = r from by simp [abs_of_pos hr]]
  rw [norm_mul, Complex.norm_conj] at hnorm
  have hlt : ‖u‖ * ‖z‖ < r ^ 2 := by
    have h1 : ‖u‖ * ‖z‖ ≤ ‖u‖ * r := mul_le_mul_of_nonneg_left hz (norm_nonneg u)
    have h2 : ‖u‖ * r < r * r := mul_lt_mul_of_pos_right hu hr
    nlinarith [h1, h2]
  linarith [hnorm, hlt]

theorem blaschke_factor_norm {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ < r) :
    ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 ∨ ¬ ‖z‖ ≤ r) ∧
    ((‖z‖ ≤ r ∧ ‖u‖ ≤ r) →
      ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ ≤ 1) ∧
    (‖z‖ = r →
      ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hz : ‖z‖ ≤ r
    · exact Or.inl (blaschke_denom_ne_zero hr hu hz)
    · exact Or.inr hz
  · rintro ⟨hz, -⟩
    have hden_ne : (r : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 :=
      blaschke_denom_ne_zero hr hu hz
    have hden_pos : 0 < ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := norm_pos_iff.mpr hden_ne
    have hle : ‖(r : ℂ) * (z - u)‖ ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
      have hkey := normSq_blaschke_key r u z
      have hnn : 0 ≤ (r ^ 2 - Complex.normSq z) * (r ^ 2 - Complex.normSq u) := by
        apply mul_nonneg
        · rw [← Complex.sq_norm]
          nlinarith [hz, norm_nonneg z]
        · rw [← Complex.sq_norm]
          nlinarith [le_of_lt hu, norm_nonneg u]
      have hsq : ‖(r : ℂ) * (z - u)‖ ^ 2 ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm]
        linarith [hkey, hnn]
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this
    rw [norm_div]
    exact (div_le_one hden_pos).mpr hle
  · intro hz
    have hzle : ‖z‖ ≤ r := le_of_eq hz
    have hden_ne : (r : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 :=
      blaschke_denom_ne_zero hr hu hzle
    have hden_pos : 0 < ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := norm_pos_iff.mpr hden_ne
    have hkey := normSq_blaschke_key r u z
    have hznsq : Complex.normSq z = r ^ 2 := by rw [← Complex.sq_norm, hz]
    have heq : Complex.normSq ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)
        = Complex.normSq ((r : ℂ) * (z - u)) := by
      rw [hznsq] at hkey
      have hz0 : (r ^ 2 - r ^ 2) * (r ^ 2 - Complex.normSq u) = 0 := by ring
      rw [hz0] at hkey
      linarith
    have hsq_eq : ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2
        = ‖(r : ℂ) * (z - u)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, heq]
    have hnorm_eq : ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ = ‖(r : ℂ) * (z - u)‖ := by
      have := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq_eq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this
    rw [norm_div, ← hnorm_eq]
    exact div_self (ne_of_gt hden_pos)

end Commons.Analysis.Complex.Blaschke