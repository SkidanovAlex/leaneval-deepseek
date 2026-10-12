import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — `radialMidBetaNonpos`

The `β`-monotonicity of the radial middle integrand

`t ↦ (y + t) - √(y² + 2yt) - t²/(2y)`

for `y > 0` and `t ≥ 0`: it is *antitone*, i.e. for `0 ≤ c ≤ β` the difference
`f β - f c` is `≤ 0`.

The proof is an exact rationalisation.  Writing `s = √(y²+2yt)`,

`(y+t) - s - t²/(2y) = -((s-y)³·(s-y+4y))/(8y³)`,

so `f` is the negative of a function of `v(t) = √(y²+2yt) - y` which is manifestly
nonnegative and increasing in `t`; the cube is monotone on `[0,∞)`.
-/

namespace Work.BoseB6Est

/-- Rationalisation identity: for `y > 0` and `t ≥ 0`, with `s = √(y² + 2yt)`,
`(y+t) - s - t²/(2y) = -((s-y)³(s-y+4y))/(8y³)`. -/
private theorem radialMidId {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    (y + t) - Real.sqrt (y ^ 2 + 2 * y * t) - t ^ 2 / (2 * y)
      = -(((Real.sqrt (y ^ 2 + 2 * y * t) - y) ^ 3
            * ((Real.sqrt (y ^ 2 + 2 * y * t) - y) + 4 * y)) / (8 * y ^ 3)) := by
  set s := Real.sqrt (y ^ 2 + 2 * y * t) with hs
  have hnn : (0 : ℝ) ≤ y ^ 2 + 2 * y * t := by nlinarith
  have hs2 : s ^ 2 = y ^ 2 + 2 * y * t := by rw [hs]; exact Real.sq_sqrt hnn
  have ht' : t = (s ^ 2 - y ^ 2) / (2 * y) := by
    field_simp
    linarith [hs2]
  rw [ht']
  field_simp
  ring

/-- The map `w ↦ w³(w+4y)/(8y³)` is monotone on `[0,∞)`. -/
private theorem radialMidDiv8_mono {y a b : ℝ} (hy : 0 < y) (ha : 0 ≤ a) (hab : a ≤ b) :
    (a ^ 3 * (a + 4 * y)) / (8 * y ^ 3) ≤ (b ^ 3 * (b + 4 * y)) / (8 * y ^ 3) := by
  have hb : 0 ≤ b := le_trans ha hab
  have h1 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha hab 3
  have h2 : a + 4 * y ≤ b + 4 * y := by linarith
  have h3 : 0 ≤ a + 4 * y := by linarith
  have h4 : 0 ≤ b ^ 3 := pow_nonneg hb 3
  have hmul : a ^ 3 * (a + 4 * y) ≤ b ^ 3 * (b + 4 * y) := mul_le_mul h1 h2 h3 h4
  exact div_le_div_of_nonneg_right hmul (by positivity)

theorem radialMidBetaNonpos {y β c : ℝ} (hy : 0 < y) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hcβ : c ≤ β) :
    ((y + β) - Real.sqrt (y ^ 2 + 2 * y * β) - β ^ 2 / (2 * y))
      - ((y + c) - Real.sqrt (y ^ 2 + 2 * y * c) - c ^ 2 / (2 * y)) ≤ 0 := by
  have hβid := radialMidId hy hβ
  have hcid := radialMidId hy hc
  -- `v(t) = √(y²+2yt) - y` is nonnegative for `t ≥ 0` ...
  have hvc0 : (0 : ℝ) ≤ Real.sqrt (y ^ 2 + 2 * y * c) - y := by
    have h1 : Real.sqrt (y ^ 2) ≤ Real.sqrt (y ^ 2 + 2 * y * c) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_sq hy.le] at h1
    linarith
  -- ... and monotone in `t`.
  have hvle : Real.sqrt (y ^ 2 + 2 * y * c) - y
      ≤ Real.sqrt (y ^ 2 + 2 * y * β) - y := by
    have h : y ^ 2 + 2 * y * c ≤ y ^ 2 + 2 * y * β := by nlinarith
    linarith [Real.sqrt_le_sqrt h]
  have hg := radialMidDiv8_mono hy hvc0 hvle
  rw [hβid, hcid]
  linarith

end Work.BoseB6Est
