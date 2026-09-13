import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Quadratic

theorem bounds_of_value_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (c r K : ℝ) (hr : 0 < r)
    (h : ∀ x : E, ‖x‖ ≤ r → |inner ℝ (M x) x / 2 + L x + c| ≤ K) :
    (∀ v : E, |inner ℝ (M v) v| ≤ 4 * K * ‖v‖ ^ 2 / r ^ 2) ∧
    (∀ v : E, |L v| ≤ 2 * K * ‖v‖ / r) ∧ |c| ≤ K := by
  have hc : |c| ≤ K := by
    have h0 := h 0 (by rw [norm_zero]; exact hr.le)
    simpa using h0
  have hK : 0 ≤ K := le_trans (abs_nonneg c) hc
  have key : ∀ w : E, ‖w‖ ≤ r → |inner ℝ (M w) w| ≤ 4 * K ∧ |L w| ≤ K := by
    intro w hw
    have h1 : |inner ℝ (M w) w / 2 + L w + c| ≤ K := h w hw
    have h2 : |inner ℝ (M w) w / 2 + (-L w) + c| ≤ K := by
      have hh := h (-w) (by rwa [norm_neg])
      simpa [map_neg, inner_neg_neg] using hh
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    have hc' := abs_le.mp hc
    have e1 : inner ℝ (M w) w
        = (inner ℝ (M w) w / 2 + L w + c) + (inner ℝ (M w) w / 2 + (-L w) + c) - 2 * c := by ring
    have e2 : 2 * L w
        = (inner ℝ (M w) w / 2 + L w + c) - (inner ℝ (M w) w / 2 + (-L w) + c) := by ring
    constructor
    · rw [abs_le]
      constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2, hc'.1, hc'.2, e1]
    · rw [abs_le]
      constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2, e2]
  refine ⟨?_, ?_, hc⟩
  · intro v
    rcases eq_or_ne ‖v‖ 0 with h0 | h0
    · have hv : v = 0 := norm_eq_zero.mp h0
      subst hv
      simp
    · set s : ℝ := r / ‖v‖ with hs
      have hnpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm h0)
      have hspos : 0 < s := by rw [hs]; positivity
      have hsnonneg : 0 ≤ s := hspos.le
      set w : E := s • v with hwdef
      have hwnorm : ‖w‖ = r := by
        rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsnonneg, hs]
        field_simp
      have hwk := key w (le_of_eq hwnorm)
      have hMw : inner ℝ (M w) w = s ^ 2 * inner ℝ (M v) v := by
        rw [hwdef, map_smul, real_inner_smul_left, inner_smul_right]
        ring
      have hmul : s ^ 2 * |inner ℝ (M v) v| = |inner ℝ (M w) w| := by
        rw [hMw, abs_mul, abs_of_nonneg (sq_nonneg s)]
      have h1 : s ^ 2 * |inner ℝ (M v) v| ≤ 4 * K := by
        rw [hmul]; exact hwk.1
      have h2 : |inner ℝ (M v) v| ≤ 4 * K / s ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hspos))]
        linarith [h1]
      have h3 : 4 * K / s ^ 2 = 4 * K * ‖v‖ ^ 2 / r ^ 2 := by
        rw [hs]; field_simp
      rw [h3] at h2; exact h2
  · intro v
    rcases eq_or_ne ‖v‖ 0 with h0 | h0
    · have hv : v = 0 := norm_eq_zero.mp h0
      subst hv
      simp
    · set s : ℝ := r / ‖v‖ with hs
      have hnpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm h0)
      have hspos : 0 < s := by rw [hs]; positivity
      have hsnonneg : 0 ≤ s := hspos.le
      set w : E := s • v with hwdef
      have hwnorm : ‖w‖ = r := by
        rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsnonneg, hs]
        field_simp
      have hwk := key w (le_of_eq hwnorm)
      have hLw : L w = s * L v := by
        rw [hwdef, map_smul, smul_eq_mul]
      have hL1 : s * |L v| ≤ K := by
        have := hwk.2
        rwa [hLw, abs_mul, abs_of_nonneg hsnonneg] at this
      have hL2 : |L v| ≤ K / s := by
        rw [le_div_iff₀ hspos]
        linarith [hL1]
      have hL3 : K / s = K * ‖v‖ / r := by
        rw [hs]; field_simp
      have hL4 : K * ‖v‖ / r ≤ 2 * K * ‖v‖ / r := by
        apply div_le_div_of_nonneg_right _ hr.le
        nlinarith [hK, norm_nonneg v]
      calc |L v| ≤ K / s := hL2
        _ = K * ‖v‖ / r := hL3
        _ ≤ 2 * K * ‖v‖ / r := hL4

end Commons.Analysis.Quadratic