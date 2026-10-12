import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the radial middle/τ-difference bound

The elementary real-variable estimate behind the split of the radial `I₁` integrand
`Work.BoseB6Est.fsGR` between the model value and the two corrections: for
`4 < r`, `r²/2 ≤ τ ≤ r²`, `0 ≤ β ≤ 26.2`, `0 ≤ s` and `r² − τ ≤ 2rs`,

  `r²·(g(τ) − g(r²)) ≤ 8·26.2²·s/r`,  where `g(x) = (x+β) − √(x²+2xβ)`.

The proof rationalises `g(x) = β²/D(x)` with `D(x) = x + β + √(x²+2xβ)`, bounds the
increment of `D` on `[τ, r²]` by `(r²−τ)(3+2β/r²)` (concavity of `√` in the form
`√A − √B ≤ (A−B)/√A`), lower bounds `D ≥ 2x + β ≥ r² + β`, and finishes with
elementary arithmetic.
-/

namespace Work.BoseB6Est

/-- Rationalisation of the radial bracket: for `x > 0`,
`(x+β) − √(x²+2xβ) = β²/(x+β+√(x²+2xβ))`. -/
lemma rat (x β : ℝ) (hx : 0 < x) (hβ : 0 ≤ β) :
    (x + β) - Real.sqrt (x ^ 2 + 2 * x * β)
      = β ^ 2 / (x + β + Real.sqrt (x ^ 2 + 2 * x * β)) := by
  have hB2 : 0 ≤ x ^ 2 + 2 * x * β := by nlinarith [sq_nonneg x, hx, hβ]
  have hden : 0 < x + β + Real.sqrt (x ^ 2 + 2 * x * β) := by
    have := Real.sqrt_nonneg (x ^ 2 + 2 * x * β); linarith
  rw [eq_div_iff hden.ne']
  have h1 : (x + β - Real.sqrt (x ^ 2 + 2 * x * β)) * (x + β + Real.sqrt (x ^ 2 + 2 * x * β))
      = (x + β) ^ 2 - (Real.sqrt (x ^ 2 + 2 * x * β)) ^ 2 := by ring
  rw [h1, Real.sq_sqrt hB2]
  ring

/-- Concavity of the square root in the form used below: for `0 < A`, `0 ≤ b ≤ A`,
`√A − √b ≤ (A−b)/√A`. -/
lemma sqrt_sub_sqrt_le_div_sqrt {A b : ℝ} (hA : 0 < A) (hb0 : 0 ≤ b) (hbA : b ≤ A) :
    Real.sqrt A - Real.sqrt b ≤ (A - b) / Real.sqrt A := by
  have hA0 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  rw [le_div_iff₀ hA0]
  have hb' : Real.sqrt b * Real.sqrt b = b := by rw [← pow_two, Real.sq_sqrt hb0]
  have hle : Real.sqrt b ≤ Real.sqrt A := Real.sqrt_le_sqrt hbA
  have h : Real.sqrt b * Real.sqrt b ≤ Real.sqrt b * Real.sqrt A :=
    mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg b)
  have hAs : Real.sqrt A * Real.sqrt A = A := by rw [← pow_two, Real.sq_sqrt hA.le]
  calc (Real.sqrt A - Real.sqrt b) * Real.sqrt A
      = Real.sqrt A * Real.sqrt A - Real.sqrt b * Real.sqrt A := by ring
    _ = A - Real.sqrt b * Real.sqrt A := by rw [hAs]
    _ ≤ A - b := by linarith

/-- `D(x) = x + β + √(x²+2xβ) ≥ 2x + β`. -/
lemma D_lower (x β : ℝ) (hx : 0 ≤ x) (hβ : 0 ≤ β) :
    2 * x + β ≤ x + β + Real.sqrt (x ^ 2 + 2 * x * β) := by
  have h : Real.sqrt (x ^ 2) ≤ Real.sqrt (x ^ 2 + 2 * x * β) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx] at h
  linarith

/-- Increment bound for `D` on `[τ, r²]`: `D(r²) − D(τ) ≤ (r²−τ)(3+2β/r²)`. -/
lemma D_diff_le {r τ β : ℝ} (hr : 4 < r) (hτ0 : 0 ≤ τ) (hβ0 : 0 ≤ β) (hτy : τ ≤ r ^ 2) :
    (r ^ 2 + β + Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β))
      - (τ + β + Real.sqrt (τ ^ 2 + 2 * τ * β))
      ≤ (r ^ 2 - τ) * (3 + 2 * β / r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hA : 0 < (r ^ 2) ^ 2 + 2 * r ^ 2 * β := by positivity
  have hb0 : 0 ≤ τ ^ 2 + 2 * τ * β := by positivity
  have hbA : τ ^ 2 + 2 * τ * β ≤ (r ^ 2) ^ 2 + 2 * r ^ 2 * β := by nlinarith
  have h1 : Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - Real.sqrt (τ ^ 2 + 2 * τ * β)
      ≤ (((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - (τ ^ 2 + 2 * τ * β))
          / Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) :=
    sqrt_sub_sqrt_le_div_sqrt hA hb0 hbA
  have hsq : r ^ 2 ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) := by
    have h := Real.sqrt_le_sqrt (show (r ^ 2) ^ 2 ≤ (r ^ 2) ^ 2 + 2 * r ^ 2 * β by nlinarith)
    rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ r ^ 2)] at h
  have hAmB : ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - (τ ^ 2 + 2 * τ * β)
      = (r ^ 2 - τ) * (r ^ 2 + τ + 2 * β) := by ring
  have hnum : 0 ≤ (r ^ 2 - τ) * (r ^ 2 + τ + 2 * β) := by nlinarith
  have h2 : (((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - (τ ^ 2 + 2 * τ * β))
        / Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β)
      ≤ ((r ^ 2 - τ) * (r ^ 2 + τ + 2 * β)) / r ^ 2 := by
    rw [hAmB]
    exact div_le_div_of_nonneg_left hnum hr2 hsq
  have hdiv : (r ^ 2 + τ + 2 * β) / r ^ 2 ≤ 2 + 2 * β / r ^ 2 := by
    rw [div_le_iff₀ hr2]
    have : (2 + 2 * β / r ^ 2) * r ^ 2 = 2 * r ^ 2 + 2 * β := by field_simp
    rw [this]; linarith
  have h3 : ((r ^ 2 - τ) * (r ^ 2 + τ + 2 * β)) / r ^ 2
      ≤ (r ^ 2 - τ) * (2 + 2 * β / r ^ 2) := by
    calc ((r ^ 2 - τ) * (r ^ 2 + τ + 2 * β)) / r ^ 2
        = (r ^ 2 - τ) * ((r ^ 2 + τ + 2 * β) / r ^ 2) := by rw [mul_div_assoc]
      _ ≤ (r ^ 2 - τ) * (2 + 2 * β / r ^ 2) := mul_le_mul_of_nonneg_left hdiv (by linarith)
  have hchain : Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - Real.sqrt (τ ^ 2 + 2 * τ * β)
      ≤ (r ^ 2 - τ) * (2 + 2 * β / r ^ 2) := le_trans (le_trans h1 h2) h3
  have hkey : (r ^ 2 + β + Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β))
      - (τ + β + Real.sqrt (τ ^ 2 + 2 * τ * β))
      = (r ^ 2 - τ)
        + (Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - Real.sqrt (τ ^ 2 + 2 * τ * β)) := by
    ring
  rw [hkey]
  have hfin : (r ^ 2 - τ) * (3 + 2 * β / r ^ 2)
      = (r ^ 2 - τ) + (r ^ 2 - τ) * (2 + 2 * β / r ^ 2) := by ring
  rw [hfin]
  linarith

/-- The final elementary arithmetic step. -/
lemma midTau_arith {r τ β s : ℝ} (hr : 4 < r) (hβ0 : 0 ≤ β) (hβc : β ≤ 26.2) (hs : 0 ≤ s)
    (hu : r ^ 2 - τ ≤ 2 * r * s) :
    β ^ 2 * (r ^ 2 - τ) * (3 * r ^ 2 + 2 * β) / (r ^ 2 + β) ^ 2 ≤ 8 * 26.2 ^ 2 * s / r := by
  have hr0 : 0 < r := by linarith
  have hden : 0 < (r ^ 2 + β) ^ 2 := by positivity
  rw [le_div_iff₀ hr0]
  have hrewrite : (β ^ 2 * (r ^ 2 - τ) * (3 * r ^ 2 + 2 * β) / (r ^ 2 + β) ^ 2) * r
      = (β ^ 2 * (r ^ 2 - τ) * (3 * r ^ 2 + 2 * β)) * r / (r ^ 2 + β) ^ 2 := by ring
  rw [hrewrite, div_le_iff₀ hden]
  have hb2 : β ^ 2 ≤ 26.2 ^ 2 := by nlinarith
  have hb3 : β ^ 3 ≤ 26.2 ^ 2 * β := by nlinarith
  have hr4 : (0:ℝ) ≤ r ^ 4 := by positivity
  have hr2 : (0:ℝ) ≤ r ^ 2 := by positivity
  have hA : 2 * β ^ 2 * (3 * r ^ 2 + 2 * β) * r ^ 2 ≤ 8 * 26.2 ^ 2 * (r ^ 2 + β) ^ 2 :=
    by nlinarith [mul_le_mul_of_nonneg_left hb2 hr4, mul_le_mul_of_nonneg_right hb3 hr2]
  have h1 : 0 ≤ β ^ 2 * (3 * r ^ 2 + 2 * β) := by
    have : 0 ≤ 3 * r ^ 2 + 2 * β := by positivity
    positivity
  have h2 : (r ^ 2 - τ) * r ≤ 2 * r ^ 2 * s := by nlinarith
  have h3 : β ^ 2 * (3 * r ^ 2 + 2 * β) * ((r ^ 2 - τ) * r)
      ≤ β ^ 2 * (3 * r ^ 2 + 2 * β) * (2 * r ^ 2 * s) :=
    mul_le_mul_of_nonneg_left h2 h1
  calc (β ^ 2 * (r ^ 2 - τ) * (3 * r ^ 2 + 2 * β)) * r
      = β ^ 2 * (3 * r ^ 2 + 2 * β) * ((r ^ 2 - τ) * r) := by ring
    _ ≤ β ^ 2 * (3 * r ^ 2 + 2 * β) * (2 * r ^ 2 * s) := h3
    _ = s * (2 * β ^ 2 * (3 * r ^ 2 + 2 * β) * r ^ 2) := by ring
    _ ≤ s * (8 * 26.2 ^ 2 * (r ^ 2 + β) ^ 2) := mul_le_mul_of_nonneg_left hA hs
    _ = 8 * 26.2 ^ 2 * s * (r ^ 2 + β) ^ 2 := by ring

theorem radialMidTauBound {r τ β s : ℝ} (hr : 4 < r) (hτ0 : 0 ≤ τ) (hτhalf : r ^ 2 / 2 ≤ τ)
    (hτy : τ ≤ r ^ 2) (hβ0 : 0 ≤ β) (hβc : β ≤ 26.2) (hs : 0 ≤ s)
    (hu : r ^ 2 - τ ≤ 2 * r * s) :
    r ^ 2 * (((τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β))
        - ((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β)))
      ≤ 8 * 26.2 ^ 2 * s / r := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hτpos : 0 < τ := by nlinarith
  set Dτ := τ + β + Real.sqrt (τ ^ 2 + 2 * τ * β) with hDτdef
  set D2 := r ^ 2 + β + Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) with hD2def
  have hDτpos : 0 < Dτ := by
    rw [hDτdef]; have := Real.sqrt_nonneg (τ ^ 2 + 2 * τ * β); linarith
  have hD2pos : 0 < D2 := by
    rw [hD2def]; have := Real.sqrt_nonneg ((r ^ 2) ^ 2 + 2 * r ^ 2 * β); linarith
  have hratτ : (τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β) = β ^ 2 / Dτ := by
    rw [hDτdef]; exact rat τ β hτpos hβ0
  have hrat2 : (r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) = β ^ 2 / D2 := by
    rw [hD2def]; exact rat (r ^ 2) β hr2 hβ0
  rw [hratτ, hrat2]
  have hfac : β ^ 2 / Dτ - β ^ 2 / D2 = β ^ 2 * (D2 - Dτ) / (Dτ * D2) := by
    field_simp
  rw [hfac]
  have hA : 0 ≤ r ^ 2 - τ := by linarith
  have hDle : Dτ ≤ D2 := by
    rw [hDτdef, hD2def]
    have hbA : τ ^ 2 + 2 * τ * β ≤ (r ^ 2) ^ 2 + 2 * r ^ 2 * β := by nlinarith
    have h1 : Real.sqrt (τ ^ 2 + 2 * τ * β)
        ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) := Real.sqrt_le_sqrt hbA
    linarith
  have hDdiff : D2 - Dτ ≤ (r ^ 2 - τ) * (3 + 2 * β / r ^ 2) := by
    rw [hD2def, hDτdef]; exact D_diff_le hr hτ0 hβ0 hτy
  have hDτlb : r ^ 2 + β ≤ Dτ := by
    rw [hDτdef]
    have h := D_lower τ β hτ0 hβ0
    linarith
  have hD2lb : r ^ 2 + β ≤ D2 := by
    rw [hD2def]
    have h := D_lower (r ^ 2) β hr2.le hβ0
    linarith
  have hden : (r ^ 2 + β) ^ 2 ≤ Dτ * D2 := by
    have h1 : 0 ≤ r ^ 2 + β := by positivity
    nlinarith
  have hquot : β ^ 2 * (D2 - Dτ) / (Dτ * D2)
      ≤ β ^ 2 * ((r ^ 2 - τ) * (3 + 2 * β / r ^ 2)) / (r ^ 2 + β) ^ 2 := by
    apply div_le_div₀ _ _ _ hden
    · positivity
    · exact mul_le_mul_of_nonneg_left hDdiff (by positivity)
    · positivity
  calc r ^ 2 * (β ^ 2 * (D2 - Dτ) / (Dτ * D2))
      ≤ r ^ 2 * (β ^ 2 * ((r ^ 2 - τ) * (3 + 2 * β / r ^ 2)) / (r ^ 2 + β) ^ 2) :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = β ^ 2 * (r ^ 2 - τ) * (3 * r ^ 2 + 2 * β) / (r ^ 2 + β) ^ 2 := by
        field_simp
    _ ≤ 8 * 26.2 ^ 2 * s / r := midTau_arith hr hβ0 hβc hs hu

end Work.BoseB6Est
