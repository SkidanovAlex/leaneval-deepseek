import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6Est.GFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `τ`-increment of FS's Bogoliubov bracket `gFun` (node B6-est)

`gFun τ b r = (τ+b) − √((τ+b)²−b²) − b²/(2r²)`, and `gFun_eq_phi` (module
`Submission.Work.BoseB6Est.GFun`) computes the `r`-dependent term *out* of the
bracket:

  `gFun τ b r = b² (1/D τ − 1/(2r²))`,  `D σ = (σ + b) + √(σ² + 2σb)`.

Hence the difference of `gFun` at the two `τ`-values `τ` and `r²` is

  `b² (1/D τ − 1/D r²)`,

and the `1/r²` part cancels: the whole estimate is an estimate on `D`.  Since
`D σ ≥ 2σ + b` and (for `σ ≤ r²`) `D σ ≤ 2(r² + b)`, while the *difference* of
the square roots carries an exact factor `r² − τ` (this is `sqrt_sq_sub_mul_le`:
`(√(r⁴+2r²b) − √(τ²+2τb))(r²+τ) ≤ (r²−τ)(r²+τ+2b)`), one gets the sharp
inflation of `D`:

  `(D r² − D τ)(r² + τ) ≤ (r² + τ + 2b)·2(r² − τ)`,

and the elementary arithmetic `recip_sub_bound` of the last ingredients
`Dt ≥ 2τ+b`, `Dr ≥ r²+b`, `r² + τ + 2b` gives the requested bound.

The statement is the `τ`-part of the two-variable increment estimate of FS
`lem:BogIntegral` (see the chapter README: `GTau`/`GBeta`).
-/

noncomputable section

namespace Work.BoseB6Est

/-- `σ ≤ √(σ² + 2σβ)` for `0 ≤ σ`, `0 ≤ β`. -/
lemma self_le_sqrt_sq_add {σ β : ℝ} (hσ : 0 ≤ σ) (hβ : 0 ≤ β) :
    σ ≤ Real.sqrt (σ ^ 2 + 2 * σ * β) := by
  have h1 : Real.sqrt (σ ^ 2) ≤ Real.sqrt (σ ^ 2 + 2 * σ * β) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hσ] at h1

/-- `√(σ² + 2σβ) ≤ σ + β` for `0 ≤ σ`, `0 ≤ β`. -/
lemma sqrt_sq_add_le {σ β : ℝ} (hσ : 0 ≤ σ) (hβ : 0 ≤ β) :
    Real.sqrt (σ ^ 2 + 2 * σ * β) ≤ σ + β := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- **The square-root increment.**  For `0 ≤ τ ≤ r²` and `b ≥ 0`,
`(√(r⁴+2r²b) − √(τ²+2τb))(r²+τ) ≤ (r²−τ)(r²+τ+2b)`: the difference of the two
square roots inside `D σ = σ + b + √(σ²+2σb)` carries an exact factor `r²−τ`. -/
lemma sqrt_sq_sub_mul_le {τ b r : ℝ} (hb : 0 ≤ b) (hτ : 0 ≤ τ) (hτr : τ ≤ r ^ 2) :
    (Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) - Real.sqrt (τ ^ 2 + 2 * τ * b)) * (r ^ 2 + τ)
      ≤ (r ^ 2 - τ) * (r ^ 2 + τ + 2 * b) := by
  have hA : (0 : ℝ) ≤ r ^ 2 := by linarith
  have hs2 : Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) ^ 2 = (r ^ 2) ^ 2 + 2 * (r ^ 2) * b :=
    Real.sq_sqrt (by positivity)
  have ht2 : Real.sqrt (τ ^ 2 + 2 * τ * b) ^ 2 = τ ^ 2 + 2 * τ * b :=
    Real.sq_sqrt (by positivity)
  have hfloor : r ^ 2 + τ ≤
      Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) + Real.sqrt (τ ^ 2 + 2 * τ * b) := by
    have h1 := self_le_sqrt_sq_add (σ := r ^ 2) (β := b) hA hb
    have h2 := self_le_sqrt_sq_add (σ := τ) (β := b) hτ hb
    linarith
  have hsub : 0 ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) - Real.sqrt (τ ^ 2 + 2 * τ * b) := by
    have hst : Real.sqrt (τ ^ 2 + 2 * τ * b) ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r ^ 2 - τ by linarith)
        (show (0 : ℝ) ≤ r ^ 2 + τ + 2 * b by linarith)]
    linarith
  have hkey : (Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) - Real.sqrt (τ ^ 2 + 2 * τ * b))
      * (Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) + Real.sqrt (τ ^ 2 + 2 * τ * b))
      = (r ^ 2 - τ) * (r ^ 2 + τ + 2 * b) := by
    nlinarith [hs2, ht2]
  calc (Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) - Real.sqrt (τ ^ 2 + 2 * τ * b)) * (r ^ 2 + τ)
      ≤ (Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) - Real.sqrt (τ ^ 2 + 2 * τ * b))
          * (Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) + Real.sqrt (τ ^ 2 + 2 * τ * b)) :=
        mul_le_mul_of_nonneg_left hfloor hsub
    _ = (r ^ 2 - τ) * (r ^ 2 + τ + 2 * b) := hkey

/-- **The arithmetic core.**  If `Dt`, `Dr` dominate `2τ+b`, `r²+b` and their
increment obeys the bound of `sqrt_sq_sub_mul_le`, then `b²(1/Dt − 1/Dr)` obeys
the requested estimate. -/
lemma recip_sub_bound {Dt Dr τ b r : ℝ} (hb : 0 < b) (hτ : 0 ≤ τ) (hτr : τ ≤ r ^ 2)
    (hr : 0 < r) (hDt : 2 * τ + b ≤ Dt) (hDr : r ^ 2 + b ≤ Dr)
    (hdiff : (Dr - Dt) * (r ^ 2 + τ) ≤ 2 * (r ^ 2 - τ) * (r ^ 2 + τ + b)) :
    b ^ 2 * (1 / Dt - 1 / Dr) ≤ 2 * b ^ 2 * (r ^ 2 - τ) / (r ^ 2 * (2 * τ + b)) := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have h2τb : (0 : ℝ) < 2 * τ + b := by linarith
  have hr2b : (0 : ℝ) < r ^ 2 + b := by linarith
  have hr2τ : (0 : ℝ) < r ^ 2 + τ := by linarith
  have hDtpos : (0 : ℝ) < Dt := lt_of_lt_of_le h2τb hDt
  have hDrpos : (0 : ℝ) < Dr := lt_of_lt_of_le hr2b hDr
  have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
  have hc : (0 : ℝ) ≤ r ^ 2 - τ := by linarith
  -- the polynomial form of the goal, all denominators cleared
  have hnum : b ^ 2 * (Dr - Dt) * (r ^ 2 * (2 * τ + b)) ≤ 2 * b ^ 2 * (r ^ 2 - τ) * (Dt * Dr) := by
    have hpoly : (r ^ 2 + τ + b) * r ^ 2 ≤ (r ^ 2 + b) * (r ^ 2 + τ) := by nlinarith
    have hprod : (2 * τ + b) * (r ^ 2 + b) ≤ Dt * Dr :=
      mul_le_mul hDt hDr (by linarith) (by linarith)
    have hm : (b ^ 2 * (Dr - Dt) * (r ^ 2 * (2 * τ + b))) * (r ^ 2 + τ)
        ≤ (2 * b ^ 2 * (r ^ 2 - τ) * (Dt * Dr)) * (r ^ 2 + τ) := by
      have s1 : b ^ 2 * ((Dr - Dt) * (r ^ 2 + τ)) * (r ^ 2 * (2 * τ + b))
          ≤ b ^ 2 * (2 * (r ^ 2 - τ) * (r ^ 2 + τ + b)) * (r ^ 2 * (2 * τ + b)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff hb2) (by positivity)
      have s2 : b ^ 2 * (2 * (r ^ 2 - τ) * (r ^ 2 + τ + b)) * (r ^ 2 * (2 * τ + b))
          ≤ b ^ 2 * (2 * (r ^ 2 - τ) * ((r ^ 2 + b) * (r ^ 2 + τ))) * (2 * τ + b) := by
        have h3 : (r ^ 2 + τ + b) * r ^ 2 * (2 * τ + b)
            ≤ (r ^ 2 + b) * (r ^ 2 + τ) * (2 * τ + b) :=
          mul_le_mul_of_nonneg_right hpoly (by linarith)
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ b ^ 2 * (2 * (r ^ 2 - τ)))
        nlinarith [h4]
      have s3 : b ^ 2 * (2 * (r ^ 2 - τ) * ((r ^ 2 + b) * (r ^ 2 + τ))) * (2 * τ + b)
          ≤ b ^ 2 * (2 * (r ^ 2 - τ) * (Dt * Dr)) * (r ^ 2 + τ) := by
        have h3 : (r ^ 2 + b) * (2 * τ + b) * (r ^ 2 + τ) ≤ Dr * Dt * (r ^ 2 + τ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hDr hDt (by linarith) (by linarith)) (by linarith)
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ b ^ 2 * (2 * (r ^ 2 - τ)))
        nlinarith [h4]
      linarith [s1, s2, s3]
    exact (mul_le_mul_iff_left₀ hr2τ).mp hm
  have h1 : 1 / Dt - 1 / Dr = (Dr - Dt) / (Dt * Dr) := by
    have hDtne : Dt ≠ 0 := ne_of_gt hDtpos
    have hDrne : Dr ≠ 0 := ne_of_gt hDrpos
    field_simp
  have h2 : b ^ 2 * (1 / Dt - 1 / Dr) = b ^ 2 * (Dr - Dt) / (Dt * Dr) := by
    rw [h1]; ring
  rw [h2, div_le_div_iff₀ (by positivity : (0 : ℝ) < Dt * Dr)
    (by positivity : (0 : ℝ) < r ^ 2 * (2 * τ + b))]
  exact hnum

/-- **The `τ`-increment of `gFun`**: comparing the bracket at `τ` with its value
at `τ = r²` (the model point of `lem:BogIntegral`) costs at most
`2b²(r²−τ)/(r²(2τ+b))`. -/
theorem gFun_tau_diff {τ b r : ℝ} (hτ : 0 ≤ τ) (hτr : τ ≤ r ^ 2) (hb : 0 ≤ b) (hr : 0 < r) :
    |gFun τ b r - gFun (r ^ 2) b r| ≤ 2 * b ^ 2 * (r ^ 2 - τ) / (r ^ 2 * (2 * τ + b)) := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- degenerate case `b = 0`: both brackets vanish
    subst hb0
    have hz1 : gFun τ 0 r = 0 := by
      rw [gFun_eq_phi hτ hb]
      ring
    have hz2 : gFun (r ^ 2) 0 r = 0 := by
      rw [gFun_eq_phi (by positivity : (0 : ℝ) ≤ r ^ 2) hb]
      ring
    rw [hz1, hz2]
    simp
  · set Dt : ℝ := τ + b + Real.sqrt (τ ^ 2 + 2 * τ * b) with hDt
    set Dr : ℝ := r ^ 2 + b + Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) with hDr
    have hDt_ge : 2 * τ + b ≤ Dt := by
      rw [hDt]
      have h := self_le_sqrt_sq_add (σ := τ) (β := b) hτ hb
      linarith
    have hDr_ge : r ^ 2 + b ≤ Dr := by
      rw [hDr]
      have h := Real.sqrt_nonneg ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b)
      linarith
    have hDtpos : (0 : ℝ) < Dt := lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * τ + b) hDt_ge
    have hDt_le_Dr : Dt ≤ Dr := by
      rw [hDt, hDr]
      have h1 : Real.sqrt (τ ^ 2 + 2 * τ * b) ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) := by
        apply Real.sqrt_le_sqrt
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ r ^ 2 - τ by linarith)
          (show (0 : ℝ) ≤ r ^ 2 + τ + 2 * b by linarith)]
      linarith
    have hdiff : gFun τ b r - gFun (r ^ 2) b r = b ^ 2 * (1 / Dt - 1 / Dr) := by
      rw [gFun_eq_phi (τ := τ) (b := b) (r := r) hτ hb,
        gFun_eq_phi (τ := r ^ 2) (b := b) (r := r) (by positivity : (0 : ℝ) ≤ r ^ 2) hb,
        ← hDt, ← hDr]
      ring
    have hsign : 0 ≤ b ^ 2 * (1 / Dt - 1 / Dr) := by
      have h1 : (1 : ℝ) / Dr ≤ 1 / Dt := one_div_le_one_div_of_le hDtpos hDt_le_Dr
      exact mul_nonneg hb2 (by linarith)
    have hc : (Dr - Dt) * (r ^ 2 + τ) ≤ 2 * (r ^ 2 - τ) * (r ^ 2 + τ + b) := by
      rw [hDt, hDr]
      have hkey := sqrt_sq_sub_mul_le hb hτ hτr
      linarith [hkey]
    rw [hdiff, abs_of_nonneg hsign]
    exact recip_sub_bound hbpos hτ hτr hr hDt_ge hDr_ge hc

end Work.BoseB6Est
