import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.Elliptic

open Real

/-- Elementary bound: for `0 < x ≤ 1` and `p ≤ 3`,
`1 - x ^ p ≤ 3 * (1 - x)`.

Proof: since `0 < x ≤ 1`, the map `y ↦ x^y` is antitone, so `x^3 ≤ x^p`;
hence `1 - x^p ≤ 1 - x^3 = (1-x)(1+x+x^2) ≤ 3(1-x)`. -/
lemma one_sub_rpow_le_three_mul {x p : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hp : p ≤ 3) :
    1 - x ^ p ≤ 3 * (1 - x) := by
  have h3p : x ^ (3:ℝ) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hp
  have h13 : 1 - x ^ (3:ℝ) = (1 - x) * (1 + x + x ^ 2) := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  have h1 : 1 - x ^ p ≤ 1 - x ^ (3:ℝ) := by linarith
  have h3 : (1 + x + x ^ 2 : ℝ) ≤ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : (0:ℝ) ≤ x + 1)]
  have h4 : (0:ℝ) ≤ 1 - x := by linarith
  calc 1 - x ^ p ≤ 1 - x ^ (3:ℝ) := h1
    _ = (1 - x) * (1 + x + x ^ 2) := h13
    _ ≤ (1 - x) * 3 := mul_le_mul_of_nonneg_left h3 h4
    _ = 3 * (1 - x) := by ring

/-- The exact algebra of the scaling: for positive `s`, `t` and any real `p`,
`s^{-p} (s/t)^p = t^{-p}`.  Equivalently `t^{-p} = s^{-p} · (s/t)^p`. -/
lemma rpow_neg_mul_div_rpow {s t p : ℝ} (hs : 0 < s) (ht : 0 < t) :
    s ^ (-p) * (s / t) ^ p = t ^ (-p) := by
  rw [Real.div_rpow hs.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv, ← mul_assoc,
      ← Real.rpow_add hs (-p) p, neg_add_cancel, Real.rpow_zero, one_mul]

/-- Comparison of `(sin t)^{-(2+η)}` with `t^{-(2+η)}` and `(sin t)^{-η}` near `t = 0`.

Since `sin t ∼ t` for small `t`, the leading singularities `(sin t)^{-(2+η)}` and
`t^{-(2+η)}` agree up to a bounded correction; the correction is dominated by the
milder singularity `(sin t)^{-η}`, because `sin t ≥ (2/π) t` on `[0, π/2]` and
`t - sin t ≤ t^3/6`.  This is precisely the estimate needed to remove the `r^{-(2+η)}`
singularity of a polar elliptic operator in favour of the `w^{-1}`-type weight. -/
theorem sin_pow_compare {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ Real.pi / 2 →
      (Real.sin t) ^ (-(2 + η)) ≤ t ^ (-(2 + η)) + C * (Real.sin t) ^ (-η) := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht0 htpi
  set s := Real.sin t with hs_def
  have hs0 : 0 < s := by
    rw [hs_def]; exact Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [htpi, Real.pi_pos])
  have hst : s ≤ t := by rw [hs_def]; exact Real.sin_le ht0.le
  have hsπ : 2/π * t ≤ s := by rw [hs_def]; exact Real.mul_le_sin ht0.le htpi
  have hscube : t - t ^ 3 / 6 ≤ s := by rw [hs_def]; exact Real.sin_ge_sub_cube ht0.le
  -- the ratio `x = s / t` lies in `(0, 1]`
  have hx0 : 0 < s / t := div_pos hs0 ht0
  have hx1 : s / t ≤ 1 := (div_le_one ht0).mpr hst
  have hp3 : 2 + η ≤ 3 := by linarith
  have hxp : 1 - (s / t) ^ (2 + η) ≤ 3 * (1 - s / t) :=
    one_sub_rpow_le_three_mul hx0 hx1 hp3
  have hm1 : 1 - s / t = (t - s) / t := by field_simp
  have hupper : (t - s) / t ≤ t ^ 2 / 6 := by
    rw [div_le_iff₀ ht0]; nlinarith [hscube]
  -- the correction is bounded by `t^2 / 2`
  have h1 : 1 - (s / t) ^ (2 + η) ≤ t ^ 2 / 2 := by
    calc 1 - (s / t) ^ (2 + η) ≤ 3 * (1 - s / t) := hxp
      _ = 3 * ((t - s) / t) := by rw [hm1]
      _ ≤ 3 * (t ^ 2 / 6) := by linarith
      _ = t ^ 2 / 2 := by ring
  have hs2 : s ^ (-(2:ℝ)) = (s ^ 2)⁻¹ := by
    rw [Real.rpow_neg hs0.le (2:ℝ), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- and `t / s ≤ π / 2 < 2`
  have hts2 : t / s ≤ 2 := by
    rw [div_le_iff₀ hs0]
    have h2ts : 2 * t ≤ π * s := by
      have h := mul_le_mul_of_nonneg_left hsπ (le_of_lt Real.pi_pos)
      have he : π * (2 / π * t) = 2 * t := by field_simp
      rwa [he] at h
    nlinarith [h2ts, mul_lt_mul_of_pos_right Real.pi_lt_four hs0]
  have htsnn : 0 ≤ t / s := div_nonneg ht0.le hs0.le
  have hC : s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η)) ≤ 2 := by
    calc s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η))
        ≤ s ^ (-(2:ℝ)) * (t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.rpow_pos_of_pos hs0 _))
      _ = (t / s) ^ 2 / 2 := by rw [hs2]; field_simp
      _ ≤ 2 := by nlinarith [hts2, htsnn,
            mul_nonneg (sub_nonneg.mpr hts2) (by linarith : (0:ℝ) ≤ t / s + 2)]
  have hsneg : 0 < s ^ (-η) := Real.rpow_pos_of_pos hs0 (-η)
  have hD : s ^ (-(2 + η)) - t ^ (-(2 + η)) = s ^ (-(2 + η)) * (1 - (s / t) ^ (2 + η)) := by
    rw [mul_sub, mul_one, rpow_neg_mul_div_rpow hs0 ht0]
  have hsp : s ^ (-(2 + η)) = s ^ (-η) * s ^ (-(2:ℝ)) := by
    rw [← Real.rpow_add hs0 (-η) (-(2:ℝ))]; congr 1; ring
  have hfinal : s ^ (-(2 + η)) - t ^ (-(2 + η)) ≤ 2 * s ^ (-η) := by
    rw [hD, hsp]
    calc s ^ (-η) * s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η))
        = s ^ (-η) * (s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η))) := by ring
      _ ≤ s ^ (-η) * 2 := mul_le_mul_of_nonneg_left hC hsneg.le
      _ = 2 * s ^ (-η) := by ring
  linarith

end Work.Elliptic
