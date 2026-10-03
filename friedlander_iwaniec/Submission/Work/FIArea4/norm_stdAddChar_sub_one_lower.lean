import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

/-- For `0 ≤ a ≤ q`, the distance from `stdAddChar (a : ZMod q)` to `1` is `2 * sin (π * a / q)`.

Indeed `stdAddChar (a : ZMod q) = exp (2 π i a / q)`, and
`‖exp (θ I) - 1‖ = 2 |sin (θ/2)|`; here `θ = 2 π a / q ∈ [0, 2π]` so `θ/2 = π a / q ∈ [0, π]`
and the sine is nonnegative. -/
private lemma norm_stdAddChar_sub_one_eq {q : ℕ} [NeZero q] {a : ℕ} (ha : a ≤ q) :
    ‖ZMod.stdAddChar (a : ZMod q) - 1‖ = 2 * Real.sin (Real.pi * a / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hchar : ZMod.stdAddChar (a : ZMod q)
      = Complex.exp (Complex.I * ((2 * Real.pi * a / q : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
    push_cast
    ring_nf
  rw [hchar, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hx : (2 * Real.pi * a / q : ℝ) / 2 = Real.pi * a / q := by ring
  have hnn : (0 : ℝ) ≤ 2 * Real.sin (Real.pi * a / q) := by
    have h0 : 0 ≤ Real.pi * a / q := by positivity
    have h1 : Real.pi * a / q ≤ Real.pi := by
      rw [div_le_iff₀ hq]
      nlinarith [Real.pi_pos, (by exact_mod_cast ha : (a : ℝ) ≤ q)]
    have := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
    linarith
  rw [hx, Real.norm_of_nonneg hnn]

/-- `sin (π a / q) = sin (π * min a (q - a) / q)` for `a ≤ q`: the factor `a` may be replaced
by `q - a` because `sin (π - x) = sin x`, and by the smaller of the two because they give the
same sine. -/
private lemma sin_cast_min {q : ℕ} [NeZero q] {a : ℕ} (ha : a ≤ q) :
    Real.sin (Real.pi * a / q) = Real.sin (Real.pi * (min a (q - a)) / q) := by
  rcases le_total a (q - a) with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    have hqa : ((q - a : ℕ) : ℝ) = (q : ℝ) - a := Nat.cast_sub ha
    rw [hqa]
    rw [← Real.sin_pi_sub (x := Real.pi * ((q : ℝ) - a) / q)]
    congr 1
    have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    field_simp
    ring

theorem norm_stdAddChar_sub_one_lower {q : ℕ} [NeZero q] {a : ℕ} (ha : a ≤ q) :
    (4 : ℝ) * ((min a (q - a) : ℕ) : ℝ) / (q : ℝ) ≤ ‖ZMod.stdAddChar (a : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set m := min a (q - a) with hm
  have hm_le_a : m ≤ a := by rw [hm]; exact Nat.min_le_left _ _
  have hm_le_qa : m ≤ q - a := by rw [hm]; exact Nat.min_le_right _ _
  have hma : (m : ℝ) ≤ a := by exact_mod_cast hm_le_a
  have hmqa : (m : ℝ) ≤ (q : ℝ) - a := by
    have h : ((m : ℕ) : ℝ) ≤ ((q - a : ℕ) : ℝ) := by exact_mod_cast hm_le_qa
    rwa [Nat.cast_sub ha] at h
  -- `2 * m ≤ q`, since `m ≤ a` and `m ≤ q - a`
  have h2m : 2 * (m : ℝ) ≤ (q : ℝ) := by linarith
  -- the trigonometric inequality `(2/π) x ≤ sin x` on `[0, π/2]`, applied to `x = π m / q`
  have hx0 : 0 ≤ Real.pi * (m : ℝ) / q := by positivity
  have hx1 : Real.pi * (m : ℝ) / q ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hq (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hkey : 2 / Real.pi * (Real.pi * (m : ℝ) / q) ≤ Real.sin (Real.pi * (m : ℝ) / q) :=
    Real.mul_le_sin hx0 hx1
  have hkey' : 2 * (m : ℝ) / q ≤ Real.sin (Real.pi * (m : ℝ) / q) := by
    have he : 2 * (m : ℝ) / q = 2 / Real.pi * (Real.pi * (m : ℝ) / q) := by field_simp
    rw [he]; exact hkey
  have hnorm : ‖ZMod.stdAddChar (a : ZMod q) - 1‖ = 2 * Real.sin (Real.pi * (m : ℝ) / q) := by
    rw [norm_stdAddChar_sub_one_eq ha, sin_cast_min ha, ← hm]
  rw [hnorm]
  have h4 : 4 * (m : ℝ) / q = 2 * (2 * (m : ℝ) / q) := by ring
  rw [h4]
  exact mul_le_mul_of_nonneg_left hkey' (by norm_num : (0 : ℝ) ≤ 2)

end Work.FIArea4
