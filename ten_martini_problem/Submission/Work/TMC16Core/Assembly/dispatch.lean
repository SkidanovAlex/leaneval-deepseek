import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.round_floor_succ
import Submission.Work.TMC16Core.Assembly.tm_arith_scale

namespace Work.TMC16Core.Assembly

/-! `dispatch` is the rounding/level-selection arithmetic step of the `C16`
assembly: it pins the floor `mf` and nearest integer `mr` of `y / qₙ`
together with the `q(n+1)^{8/9}` bound (with the constant `40^9`).

The two reusable ingredients live in their own modules:
`Work.TMC16Core.Assembly.round_floor_succ` (`round x ∈ {⌊x⌋, ⌊x⌋+1}`) and
`Work.TMC16Core.Assembly.tm_arith_scale` (`10 a + 15 b ≤ Q`). -/

theorem dispatch {q : ℕ → ℕ} {n : ℕ} {y : ℤ} (hqn : 0 < q n) (hy : 0 ≤ y)
    (hqnext : 40 ^ 9 ≤ q (n + 1))
    {mr mf : ℤ} (hmr : mr = round ((y : ℝ) / (q n : ℝ)))
    (hmf : mf = ⌊(y : ℝ) / (q n : ℝ)⌋) :
    0 ≤ mr ∧ 0 ≤ mf ∧ mf * (q n : ℤ) ≤ y ∧ y < (mf + 1) * (q n : ℤ) ∧
      (mr = mf ∨ mr = mf + 1) ∧
      (2 : ℤ) * |y - mr * (q n : ℤ)| ≤ (q n : ℤ) ∧
      (∀ ℓ : ℤ, |y - mr * (q n : ℤ)| ≤ |y - ℓ * (q n : ℤ)|) ∧
      (mr ≠ 0 → (q n : ℝ) ≤ 2 * (y : ℝ)) ∧
      (mr ≠ 0 → (y : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) →
        10 * (mr + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) ∧
      (mr = 0 → (y : ℝ) ≤ (q n : ℝ) / 2 + 1 / 2) := by
  subst hmr
  subst hmf
  set x : ℝ := (y : ℝ) / (q n : ℝ) with hxdef
  have hqnR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqn
  have hxnn : 0 ≤ x := by rw [hxdef]; exact div_nonneg (by exact_mod_cast hy) hqnR.le
  have hxy : x * (q n : ℝ) = (y : ℝ) := by
    rw [hxdef]; exact div_mul_cancel₀ _ (ne_of_gt hqnR)
  have hkey (k : ℤ) : ((y - k * (q n : ℤ) : ℤ) : ℝ) = (q n : ℝ) * (x - (k : ℝ)) := by
    push_cast
    rw [← hxy]; ring
  have habs (k : ℤ) : ((|y - k * (q n : ℤ)| : ℤ) : ℝ) = (q n : ℝ) * |x - (k : ℝ)| := by
    rw [Int.cast_abs, hkey k, abs_mul, abs_of_pos hqnR]
  -- `round x ≥ 0`
  have hround_nn : (0 : ℤ) ≤ round x := by
    by_contra h
    push_neg at h
    have h2 : round x ≤ -1 := by omega
    have h3 : (round x : ℝ) ≤ -1 := by exact_mod_cast h2
    have h4 := sub_half_lt_round x
    linarith
  -- floor lower bound
  have h3c : ⌊x⌋ * (q n : ℤ) ≤ y := by
    have hfl : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hm : (⌊x⌋ : ℝ) * (q n : ℝ) ≤ x * (q n : ℝ) := mul_le_mul_of_nonneg_right hfl hqnR.le
    rw [hxy] at hm
    exact_mod_cast hm
  -- floor upper bound
  have h4c : y < (⌊x⌋ + 1) * (q n : ℤ) := by
    have hfl : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    have hgoal : (y : ℝ) < (((⌊x⌋ + 1) * (q n : ℤ) : ℤ) : ℝ) := by
      push_cast
      rw [← hxy]
      exact mul_lt_mul_of_pos_right hfl hqnR
    exact_mod_cast hgoal
  -- round is within 1/2 of x
  have h6c : (2 : ℤ) * |y - round x * (q n : ℤ)| ≤ (q n : ℤ) := by
    have hgoal : (((2 : ℤ) * |y - round x * (q n : ℤ)| : ℤ) : ℝ) ≤ ((q n : ℤ) : ℝ) := by
      rw [show (((2 : ℤ) * |y - round x * (q n : ℤ)| : ℤ) : ℝ)
            = (2 : ℝ) * ((|y - round x * (q n : ℤ)| : ℤ) : ℝ) by push_cast; ring]
      rw [habs (round x)]
      push_cast
      have h := abs_sub_round x
      have hmul := mul_le_mul_of_nonneg_left
        (by linarith : (2 : ℝ) * |x - (round x : ℝ)| ≤ 1) hqnR.le
      linarith
    exact Int.cast_le.mp hgoal
  -- minimality of `round`
  have h7c : ∀ ℓ : ℤ, |y - round x * (q n : ℤ)| ≤ |y - ℓ * (q n : ℤ)| := by
    intro ℓ
    have hgoal : ((|y - round x * (q n : ℤ)| : ℤ) : ℝ) ≤ ((|y - ℓ * (q n : ℤ)| : ℤ) : ℝ) := by
      rw [habs (round x), habs ℓ]
      exact mul_le_mul_of_nonneg_left (round_le x ℓ) hqnR.le
    exact_mod_cast hgoal
  -- nonzero round forces `y ≥ q n / 2`
  have h8c : round x ≠ 0 → (q n : ℝ) ≤ 2 * (y : ℝ) := by
    intro hne
    have hpos : (1 : ℤ) ≤ round x := by omega
    have hcast : (1 : ℝ) ≤ (round x : ℝ) := by exact_mod_cast hpos
    have hxge : (1 : ℝ) / 2 ≤ x := by
      have := round_le_add_half x
      linarith
    rw [← hxy]
    have hmul := mul_le_mul_of_nonneg_right hxge hqnR.le
    linarith
  -- the large alternative
  have h9c : round x ≠ 0 → (y : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) →
      10 * (round x + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
    intro hne hyQ
    have hb2 : (q n : ℝ) ≤ 2 * (y : ℝ) := h8c hne
    have hQ : (40 : ℝ) ^ 9 ≤ (q (n + 1) : ℝ) := by exact_mod_cast hqnext
    have hscale := tm_arith_scale hqnR hb2 hyQ hQ
    have hstep : (round x : ℝ) + 1 ≤ x + 3 / 2 := by
      have := round_le_add_half x; linarith
    have hA : (10 : ℝ) * ((round x : ℝ) + 1) * (q n : ℝ) ≤
        (10 : ℝ) * (x + 3 / 2) * (q n : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (by norm_num)) hqnR.le
    have hB : (10 : ℝ) * (x + 3 / 2) * (q n : ℝ) = 10 * (y : ℝ) + 15 * (q n : ℝ) := by
      rw [← hxy]; ring
    have hgoal : (((10 * (round x + 1) * (q n : ℤ) : ℤ)) : ℝ) ≤ ((q (n + 1) : ℤ) : ℝ) := by
      rw [show ((10 * (round x + 1) * (q n : ℤ) : ℤ) : ℝ)
            = (10 : ℝ) * ((round x : ℝ) + 1) * (q n : ℝ) by push_cast; ring]
      push_cast
      linarith [hA, hB, hscale]
    exact Int.cast_le.mp hgoal
  -- vanishing round
  have h10c : round x = 0 → (y : ℝ) ≤ (q n : ℝ) / 2 + 1 / 2 := by
    intro h0
    have hlt : x < 1 / 2 := (round_eq_zero_iff.mp h0).2
    rw [← hxy]
    have hmul := mul_lt_mul_of_pos_right hlt hqnR
    linarith
  exact ⟨hround_nn, Int.floor_nonneg.mpr hxnn, h3c, h4c, round_floor_succ x,
    h6c, h7c, h8c, h9c, h10c⟩

end Work.TMC16Core.Assembly
