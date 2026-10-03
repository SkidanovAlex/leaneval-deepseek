import Mathlib

namespace Work.FIArea5.S16

open Filter Asymptotics

/-- A polynomial multiple of a complex quadratic exponential with `0 < Re A` decays faster than any power of `|x|` along the cocompact filter: since `|x| ^ a * |e^{-πAx²+2πbx}| = |x|^a e^{-π Re A x² + 2π Re b x}` and the quadratic term dominates. -/
theorem cexp_quadratic_poly_isBigO {A : ℂ} (hA : 0 < A.re) (b : ℂ) (a : ℕ) {B : ℝ} :
    (fun x : ℝ => (x : ℂ) ^ a * Complex.exp (-Real.pi * A * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ)))
      =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-B)) := by
  -- The quadratic part `-π * A` has negative real part.
  have hc : (-Real.pi * A).re < 0 := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [Real.pi_pos, hA]
  -- Hence the exponential factor decays faster than `|x| ^ (-(B + a + 1))`.
  have hexp : (fun x : ℝ => Complex.exp (-Real.pi * A * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ)))
      =o[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-(B + (a : ℝ) + 1))) :=
    cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (a := -Real.pi * A) (b := 2 * Real.pi * b)
      (s := -(B + (a : ℝ) + 1)) hc
  -- Eventually `1 ≤ |x|` along the cocompact filter.
  have hb1 : ∀ᶠ x : ℝ in Filter.cocompact ℝ, (1 : ℝ) ≤ |x| := by
    have := (tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop (1 : ℝ)
    simpa [Real.norm_eq_abs] using this
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  have hbound := (isLittleO_iff.mp hexp) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, hb1] with x hx hx1
  have hnormg : ‖(fun x : ℝ => |x| ^ (-B)) x‖ = |x| ^ (-B) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rw [hnormg]
  have hxe : ‖Complex.exp (-Real.pi * A * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ))‖
      ≤ |x| ^ (-(B + (a : ℝ) + 1)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)] using hx
  have hnormf : ‖(x : ℂ) ^ a * Complex.exp (-Real.pi * A * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ))‖
      = |x| ^ a * ‖Complex.exp (-Real.pi * A * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ))‖ := by
    rw [norm_mul, Complex.norm_pow]
    congr 1
    simp
  -- For `1 ≤ |x|` we have `|x| ^ a * |x| ^ (-(B + a + 1)) = |x| ^ (-(B+1)) ≤ |x| ^ (-B)`.
  have hpow : |x| ^ a * |x| ^ (-(B + (a : ℝ) + 1)) ≤ |x| ^ (-B) := by
    have hx0 : 0 < |x| := lt_of_lt_of_le zero_lt_one hx1
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    have : (a : ℝ) + -(B + (a : ℝ) + 1) = -(B + 1) := by ring
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  rw [hnormf, one_mul]
  exact le_trans (mul_le_mul_of_nonneg_left hxe (pow_nonneg (abs_nonneg x) a)) hpow

end Work.FIArea5.S16
