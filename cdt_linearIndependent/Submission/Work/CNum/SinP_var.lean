import Mathlib
import Submission.Work.CNum.cosT_bound
import Submission.Work.CNum.SinP_tail

/-!
# Variation bound for the sine Taylor polynomial `sinP · 11` on `[0, π/4]`

For `0 ≤ s ≤ t ≤ π/4` we prove

`(t - s) / 4 - 2 / 25! ≤ sinP t 11 - sinP s 11`,

i.e. the partial sum `sinP · 11` of the sine series increases at least as fast
as `x ↦ x / 4`, up to a tiny error term.

The proof combines two ingredients:

* the two-sided remainder bound `SinP_tail`: `0 ≤ sin x - sinP x 11 ≤ 2/25!`
  on `[0, π/4]`, which lets us replace `sinP · 11` by `sin` up to `2/25!`;
* the mean-value-type inequality `sin_sub_sin_ge_Icc`: `(t - s)/4 ≤ sin t - sin s`,
  proved from the product formula `sin t - sin s = 2 sin((t-s)/2) cos((t+s)/2)`
  together with `sin u ≥ u/2` (Jordan) and `cos v ≥ 1/2` for `v ≤ π/4`.
-/

namespace Work.CNum

/-- On `[0, π/4]` the sine increases by at least a quarter of the increment:
`(t - s)/4 ≤ sin t - sin s` for `0 ≤ s ≤ t ≤ π/4`.  Via the product formula,
the two factors satisfy `sin((t-s)/2) ≥ (t-s)/4` and `cos((t+s)/2) ≥ 1/2`. -/
theorem sin_sub_sin_ge_Icc {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (h1 : t ≤ Real.pi / 4) :
    (t - s) / 4 ≤ Real.sin t - Real.sin s := by
  have hu0 : 0 ≤ (t - s) / 2 := by linarith
  have hup : (t - s) / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hv0 : 0 ≤ (t + s) / 2 := by linarith
  have hvp : (t + s) / 2 ≤ Real.pi / 4 := by linarith
  -- `sin u ≥ u/2` for `u = (t-s)/2` (Jordan's inequality `2u/π ≤ sin u`, `π ≤ 4`)
  have hsin_u : (t - s) / 4 ≤ Real.sin ((t - s) / 2) := by
    have hJ := Real.mul_le_sin hu0 hup
    have hp : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith [Real.pi_lt_four]
    have h2 : (t - s) / 4 ≤ 2 / Real.pi * ((t - s) / 2) := by
      have hm := mul_le_mul_of_nonneg_right hp hu0
      calc (t - s) / 4 = (1 / 2) * ((t - s) / 2) := by ring
        _ ≤ 2 / Real.pi * ((t - s) / 2) := hm
    linarith
  -- `cos v ≥ 1/2` for `v = (t+s)/2 ≤ π/4` (since `cos(π/4) = √2/2 ≥ 1/2`)
  have hcos_v : (1 : ℝ) / 2 ≤ Real.cos ((t + s) / 2) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (x := (t + s) / 2) (y := Real.pi / 4)
      hv0 (by linarith [Real.pi_pos]) hvp
    rw [Real.cos_pi_div_four] at hmono
    have h2 : (1 : ℝ) / 2 ≤ Real.sqrt 2 / 2 := by
      nlinarith [Real.one_lt_sqrt_two, Real.sqrt_nonneg 2]
    linarith
  have hsinu_nn : 0 ≤ Real.sin ((t - s) / 2) := le_trans (by linarith : (0:ℝ) ≤ (t - s)/4) hsin_u
  have hprod : ((t - s) / 4) * ((1 : ℝ) / 2) ≤
      Real.sin ((t - s) / 2) * Real.cos ((t + s) / 2) :=
    mul_le_mul hsin_u hcos_v (by norm_num) hsinu_nn
  have hdouble : 2 * (((t - s) / 4) * ((1 : ℝ) / 2)) ≤
      2 * (Real.sin ((t - s) / 2) * Real.cos ((t + s) / 2)) :=
    mul_le_mul_of_nonneg_left hprod (by norm_num)
  rw [Real.sin_sub_sin]
  have hleft : 2 * (((t - s) / 4) * ((1 : ℝ) / 2)) = (t - s) / 4 := by ring
  have hright : 2 * (Real.sin ((t - s) / 2) * Real.cos ((t + s) / 2)) =
      2 * Real.sin ((t - s) / 2) * Real.cos ((t + s) / 2) := by ring
  linarith [hdouble, hleft, hright]

theorem SinP_var {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (h1 : t ≤ Real.pi / 4) :
    (t - s) / 4 - 2 * ((Nat.factorial 25 : ℝ))⁻¹ ≤ sinP t 11 - sinP s 11 := by
  have ht0 : 0 ≤ t := h0.trans hst
  have hs0 : 0 ≤ s := h0
  have htail_t := SinP_tail ht0 h1
  have htail_s := SinP_tail hs0 (hst.trans h1)
  have hsin := sin_sub_sin_ge_Icc h0 hst h1
  linarith [htail_t.1, htail_t.2, htail_s.1, htail_s.2, hsin]

end Work.CNum
