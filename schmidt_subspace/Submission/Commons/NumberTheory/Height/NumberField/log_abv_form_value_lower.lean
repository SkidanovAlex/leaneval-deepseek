import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.NumberTheory.Height.NumberField.mulHeight_sum_mul_int_le_of_nonempty
import Submission.Commons.NumberTheory.Height.NumberField.one_le_mulHeight_sq_mul_abv

namespace Commons.NumberTheory.Height.NumberField

open _root_.NumberField

/-- A non-zero integer vector has sup-norm at least `1`. -/
lemma one_le_norm_of_ne_zero {σ : Type*} [Fintype σ] {x : σ → ℤ} (hx : x ≠ 0) :
    (1 : ℝ) ≤ ‖x‖ := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ (|x j| : ℝ) := by
    have : (1 : ℤ) ≤ |x j| := Int.one_le_abs hj
    exact_mod_cast this
  have h2 := norm_le_pi_norm x j
  rw [Int.norm_eq_abs] at h2
  linarith

theorem log_abv_form_value_lower {K : Type*} [Field K] [NumberField K]
    {σ : Type*} [Fintype σ] (hσ : 2 ≤ Fintype.card σ) (a : σ → K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : NumberField.InfinitePlace K) (x : σ → ℤ) (hx : x ≠ 0),
      -C - C * Real.log ‖x‖ ≤
        Real.log (w.val (∑ j : σ, a j * (x j : K))) := by
  classical
  set B : ℝ := (Fintype.card σ : ℝ) ^ (Module.finrank ℚ K) * ∏ j : σ, Height.mulHeight₁ (a j)
    with hBdef
  set M : ℕ := Module.finrank ℚ K * Fintype.card σ with hMdef
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    have h1 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by
      have : (1 : ℕ) ≤ Fintype.card σ := by omega
      exact_mod_cast this
    have h2 : 1 ≤ (Fintype.card σ : ℝ) ^ (Module.finrank ℚ K) := one_le_pow₀ h1
    have h3 : 1 ≤ ∏ j : σ, Height.mulHeight₁ (a j) :=
      Finset.one_le_prod fun j _ => Height.one_le_mulHeight₁ (a j)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Fintype.card σ : ℝ) ^ (Module.finrank ℚ K) * ∏ j : σ, Height.mulHeight₁ (a j) :=
          mul_le_mul h2 h3 zero_le_one (le_trans zero_le_one h2)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  refine ⟨2 * Real.log B + 2 * (M : ℝ) + 1, ?_, ?_⟩
  · have h := Real.log_nonneg hB1
    have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  · intro w x hx
    have hX : (1 : ℝ) ≤ ‖x‖ := one_le_norm_of_ne_zero hx
    have hlogX : 0 ≤ Real.log ‖x‖ := Real.log_nonneg hX
    set L : K := ∑ j : σ, a j * (x j : K) with hLdef
    by_cases hL : L = 0
    · rw [hL]
      simp only [AbsoluteValue.map_zero, Real.log_zero]
      have hCpos : 0 < 2 * Real.log B + 2 * (M : ℝ) + 1 := by
        have h := Real.log_nonneg hB1
        have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        linarith
      nlinarith [mul_nonneg (le_of_lt hCpos) hlogX]
    · have hvalpos : 0 < w.val L := InfinitePlace.pos_iff.mpr hL
      have hHpos : 0 < Height.mulHeight₁ L := Height.mulHeight₁_pos L
      have hHne : Height.mulHeight₁ L ≠ 0 := ne_of_gt hHpos
      have hH1 : 1 ≤ Height.mulHeight₁ L := Height.one_le_mulHeight₁ L
      -- the key inequality of the product formula, at the place `w`
      have hmain : (1 : ℝ) ≤ (Height.mulHeight₁ L) ^ 2 * (w.val L) ^ w.mult :=
        one_le_mulHeight_sq_mul_abv w L hL
      -- hence `1 / H ^ 2 ≤ w.val L`
      have hy : (1 : ℝ) / (Height.mulHeight₁ L) ^ 2 ≤ w.val L := by
        have h2 : (1 : ℝ) / (Height.mulHeight₁ L) ^ 2 ≤ (w.val L) ^ w.mult := by
          rw [div_le_iff₀ (by positivity)]
          linarith [hmain]
        rcases le_or_gt (w.val L) 1 with hle | hlt
        · refine h2.trans ?_
          simpa using pow_le_pow_of_le_one (le_of_lt hvalpos) hle
            (show 1 ≤ w.mult from w.mult_pos)
        · have h3 : (1 : ℝ) / (Height.mulHeight₁ L) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact one_le_pow₀ hH1
          linarith
      -- passing to logarithms
      have hlog : -2 * Real.log (Height.mulHeight₁ L) ≤ Real.log (w.val L) := by
        have hpos : 0 < (1 : ℝ) / (Height.mulHeight₁ L) ^ 2 := by positivity
        have h := Real.log_le_log hpos hy
        rw [Real.log_div one_ne_zero (pow_ne_zero 2 hHne), Real.log_one, Real.log_pow] at h
        norm_num at h
        linarith
      -- and the height of `L` is polynomially bounded in `‖x‖`
      have hHle : Height.mulHeight₁ L ≤ B * ‖x‖ ^ M := by
        have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
        have h := mulHeight_sum_mul_int_le_of_nonempty (a := a) x
        rw [max_eq_right hX] at h
        simpa [hBdef, hMdef, hLdef] using h
      have hlogH : Real.log (Height.mulHeight₁ L) ≤ Real.log B + (M : ℝ) * Real.log ‖x‖ := by
        calc Real.log (Height.mulHeight₁ L) ≤ Real.log (B * ‖x‖ ^ M) :=
              Real.log_le_log hHpos hHle
          _ = Real.log B + Real.log (‖x‖ ^ M) :=
              Real.log_mul hBpos.ne' (pow_ne_zero M (by positivity))
          _ = Real.log B + (M : ℝ) * Real.log ‖x‖ := by rw [Real.log_pow]
      have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith [hlog, hlogH, hlogX, hlogB, hMnn]

end Commons.NumberTheory.Height.NumberField