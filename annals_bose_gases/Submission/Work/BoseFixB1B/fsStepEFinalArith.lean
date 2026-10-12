import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

/-- The cubic `45Y³ + 36Y² - 232Y + 159` is nonnegative on `Y ≥ 0`.  It is the
numerator (after clearing the positive denominator `Y+3`) of `Y ↦ 45Y² - 99Y + 65 - 36/(Y+3)`. -/
lemma fsStepE_cubic_nonneg (Y : ℝ) (hY : 0 ≤ Y) : 0 ≤ 45*Y^3 + 36*Y^2 - 232*Y + 159 := by
  by_cases h1 : Y ≤ 1
  · -- On `[0,1]` the cubic equals `8 + (Y-1)*(45Y²+81Y-151)` with both factors `≤ 0`.
    have hfac : 45*Y^3 + 36*Y^2 - 232*Y + 159 = 8 + (Y-1)*(45*Y^2 + 81*Y - 151) := by ring
    have hY1 : Y - 1 ≤ 0 := by linarith
    have hYY : Y^2 ≤ Y := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hY hY1]
    have hq : 45*Y^2 + 81*Y - 151 ≤ 0 := by nlinarith [hYY, hY, h1]
    have hprod : 0 ≤ (Y-1)*(45*Y^2+81*Y-151) := mul_nonneg_of_nonpos_of_nonpos hY1 hq
    nlinarith [hfac, hprod]
  · -- On `[1,∞)` set `Z = Y-1 ≥ 0`: the cubic is `45Z³ + 171Z² - 25Z + 8`.
    push Not at h1
    have hZ : 0 ≤ Y - 1 := by linarith
    have hfac : 45*Y^3 + 36*Y^2 - 232*Y + 159 = 45*(Y-1)^3 + 171*(Y-1)^2 - 25*(Y-1) + 8 := by ring
    have hc : 0 ≤ 45*(Y-1)^3 := by
      have : 0 ≤ (Y-1)^3 := pow_nonneg hZ 3
      linarith
    have hq : 0 ≤ 171*(Y-1)^2 - 25*(Y-1) + 8 := by
      have hid : 171*(Y-1)^2 - 25*(Y-1) + 8 = 171*((Y-1) - 25/342)^2 + 4847/684 := by ring
      nlinarith [hid, sq_nonneg ((Y-1) - 25/342)]
    nlinarith [hfac, hc, hq]

/-- The numerical core `(★)`: for `U ≥ 2`, `Y ≥ 0`,
`(1/20)*(U+Y-2+4/(U+Y+1)) ≤ (1/4)*(Y-1)^2 + U/18`. -/
lemma fsStepE_num_ineq (U Y : ℝ) (hU : 2 ≤ U) (hY : 0 ≤ Y) :
    (1/20)*(U + Y - 2 + 4/(U+Y+1)) ≤ (1/4)*(Y-1)^2 + U/18 := by
  have hden : 0 < U + Y + 1 := by linarith
  have hden2 : 0 < Y + 3 := by linarith
  -- `180` times the difference of the two sides is `45Y²-99Y+63+U-36/(U+Y+1)`.
  have hE : 0 ≤ 45*Y^2 - 99*Y + 63 + U - 36/(U+Y+1) := by
    -- `U - 36/(U+Y+1) ≥ 2 - 36/(Y+3)` since `U ≥ 2` and `U+Y+1 ≥ Y+3 > 0`.
    have hg : 0 ≤ 45*Y^2 - 99*Y + 65 - 36/(Y+3) := by
      rw [sub_nonneg, div_le_iff₀ hden2]
      have hexp : (45*Y^2 - 99*Y + 65) * (Y+3) = 45*Y^3 + 36*Y^2 - 232*Y + 195 := by ring
      nlinarith [hexp, fsStepE_cubic_nonneg Y hY]
    have h36 : 36/(U+Y+1) ≤ 36/(Y+3) := by
      rw [div_le_div_iff₀ hden hden2]; nlinarith [hU]
    linarith
  rw [← sub_nonneg]
  have hkey : (1/4)*(Y-1)^2 + U/18 - (1/20)*(U + Y - 2 + 4/(U+Y+1))
      = (45*Y^2 - 99*Y + 63 + U - 36/(U+Y+1))/180 := by
    field_simp
    ring
  rw [hkey]
  positivity

/-- The rational identity `s - 2 + 4/(1+s) = (s-1)^2/(1+s) + 1` for `1 + s ≠ 0`,
i.e. `(A-1)^2/(A+1) + 1 = A - 2 + 4/(A+1)` with `A = s`. -/
lemma fsStepE_recip_identity (s : ℝ) (h : 1 + s ≠ 0) : s - 2 + 4/(1+s) = (s-1)^2/(1+s) + 1 := by
  field_simp
  ring

theorem fsStepEFinalArith {μ ρ ρ' ρ'' c : ℝ} {m : ℕ} (hμ : 0 < μ) (hm : 1 ≤ m)
    (hc : 0 < c) (hc20 : c ≤ 1 / 20) (hp' : 2 * μ ≤ ρ') (hp''0 : 0 ≤ ρ'')
    (hp'' : ρ'' < ρ') (hρ : ρ = (m : ℝ) * ρ' + ρ'') :
    c * ((ρ - μ) ^ 2 / (1 + ρ / μ) + μ ^ 2) ≤ (1 / 4) * (ρ'' - μ) ^ 2 + (1 / 18) * μ * (ρ - ρ'') := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hρ'0 : 0 ≤ ρ' := by linarith [hp']
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  -- `U := m·ρ'/μ ≥ 2` and `Y := ρ''/μ ≥ 0`.
  have hU2 : 2 ≤ (m:ℝ) * ρ' / μ := by
    rw [le_div_iff₀ hμ]
    have hprod : 0 ≤ ((m:ℝ) - 1) * ρ' := mul_nonneg (by linarith) hρ'0
    nlinarith [hp', hprod]
  have hY0 : 0 ≤ ρ'' / μ := div_nonneg hp''0 (le_of_lt hμ)
  have hnum := fsStepE_num_ineq ((m:ℝ)*ρ'/μ) (ρ''/μ) hU2 hY0
  have hρpos : 0 < ρ := by
    have hle : ρ' ≤ ρ := by rw [hρ]; nlinarith [hρ'0, hm1]
    linarith
  have h1p : 0 < 1 + ρ/μ := by
    have : 0 < ρ/μ := div_pos hρpos hμ
    linarith
  have hden : 1 + ρ/μ ≠ 0 := ne_of_gt h1p
  -- Normalisation by `μ²` of the two sides.
  have hL : μ^2 * ((1/20)*((m:ℝ)*ρ'/μ + ρ''/μ - 2 + 4/((m:ℝ)*ρ'/μ + ρ''/μ + 1)))
      = (1/20)*((ρ-μ)^2/(1+ρ/μ) + μ^2) := by
    have hsum : (m:ℝ)*ρ'/μ + ρ''/μ = ρ/μ := by rw [hρ, add_div]
    rw [hsum]
    rw [show ρ/μ + 1 = (1:ℝ) + ρ/μ from by ring]
    rw [fsStepE_recip_identity (ρ/μ) hden]
    have h2 : (ρ-μ)^2 = μ^2*(ρ/μ-1)^2 := by
      have h3 : ρ - μ = μ*(ρ/μ - 1) := by field_simp
      rw [h3, mul_pow]
    rw [h2]
    ring
  have hR : μ^2 * ((1/4)*(ρ''/μ-1)^2 + ((m:ℝ)*ρ'/μ)/18)
      = (1/4)*(ρ''-μ)^2 + (1/18)*μ*(ρ-ρ'') := by
    have hsub : ρ - ρ'' = (m:ℝ)*ρ' := by rw [hρ]; ring
    rw [hsub]
    field_simp
  have hmain : (1/20)*((ρ-μ)^2/(1+ρ/μ) + μ^2) ≤ (1/4)*(ρ''-μ)^2 + (1/18)*μ*(ρ-ρ'') := by
    rw [← hL, ← hR]
    exact mul_le_mul_of_nonneg_left hnum (sq_nonneg μ)
  have hX : 0 ≤ (ρ-μ)^2/(1+ρ/μ) + μ^2 := by positivity
  calc c * ((ρ-μ)^2/(1+ρ/μ) + μ^2) ≤ (1/20)*((ρ-μ)^2/(1+ρ/μ) + μ^2) := mul_le_mul_of_nonneg_right hc20 hX
    _ ≤ (1/4)*(ρ''-μ)^2 + (1/18)*μ*(ρ-ρ'') := hmain

end Work.BoseFixB1B
