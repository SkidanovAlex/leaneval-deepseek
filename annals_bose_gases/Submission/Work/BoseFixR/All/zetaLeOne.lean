import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.All.zetaLeOne` — the `S (R/ℓ)² ≤ 1` row of the far leg

The far leg of the `R`-subproject (`Work.BoseFixR.All.extraLeA`/`extraLeB`,
`massDeficit_taylor`) inflates its mass rows by the factor `1 + S (R/ℓ)²`,
where `S` is a fixed parameter and `R` a fixed radius.  Those rows are consumed
in the form "`1 + S (R/ℓ)² ≤ 2`", i.e. they need

  `S (R / ℓ)² ≤ 1`,   `ℓ = sideAt μ (a v)`.

This module proves it from the smallness hypothesis `hε` on `ε₀` together with
admissibility `Work.BoseBoxFix.Adm v ε₀ μ` (which gives `μ > 0` and
`μ (a v)³ ≤ ε₀`).

## The arithmetic

Write `A = a v`, `t = μ A³ ≤ 1` and `D = A²/((S+1)R²10¹⁵)`.  From
`t ≤ ε₀ ≤ D^{323/320}` and `0 ≤ D` we get, raising to the `320/323`-th power,

  `t^{320/323} ≤ (D^{323/320})^{320/323} = D`,

i.e. `t^{320/323}·(S+1)R²10¹⁵ ≤ A²`, whence

  `S R² ≤ A²/(t^{320/323}·10¹⁵)`.

Since `0 < t ≤ 1` the map `c ↦ t^{c/323}` is antitone, so
`t^{326/323} ≤ t^{320/323} ≤ t^{320/323}·10¹⁵`, and therefore

  `S R² ≤ A²/t^{326/323} = A²·t^{-326/323} = ℓ²`

(`ℓ = A t^{-163/323}`, `BoseBox.sideAt_eq_rpow`, and `(t^{-163/323})² = t^{-326/323}`).
Dividing by `ℓ² > 0` gives `S (R/ℓ)² ≤ 1`.

Nothing here is specific to the far leg: the only inputs are `Adm` and `hε`.
The arithmetic is carried out here self-contained (in `extraLeA` the same chain
is `private`).
-/

namespace Work.BoseFixR.All

/-- **Closed form of `ℓ²`**: `ℓ² = (a v)² (μ (a v)³)^{-326/323}`. -/
private lemma ell_sq_zeta {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (Work.BoseFixR.ell v μ) ^ 2
      = (BoseGases.a v) ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (-(326 / 323) : ℝ) := by
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have h1 : Work.BoseFixR.ell v μ
      = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by
    rw [Work.BoseFixR.ell]
    exact Work.BoseBox.sideAt_eq_rpow hav hμ
  have hp : ((μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ)) ^ 2
      = (μ * (BoseGases.a v) ^ 3) ^ (-(326 / 323) : ℝ) := by
    rw [← Real.rpow_natCast ((μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ)) 2,
      ← Real.rpow_mul ht0.le]
    norm_num
  rw [h1, mul_pow, hp]

theorem zetaLeOne {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ε₀ μ S : ℝ}
    (hR : 0 < R) (hav : 0 < BoseGases.a v) (hS : 0 ≤ S) (hε₁ : ε₀ ≤ 1)
    (hε : ε₀ ≤ (BoseGases.a v ^ 2 / ((S + 1) * R ^ 2 * 10 ^ 15)) ^ (323 / 320 : ℝ))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) :
    S * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 := by
  obtain ⟨hμ, htε, _⟩ := hAdm
  -- `t = μ A³`, `0 < t ≤ 1`
  set t : ℝ := μ * BoseGases.a v ^ 3 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht]; exact le_trans htε hε₁
  -- `D = A²/((S+1)R²10¹⁵)`
  set D : ℝ := BoseGases.a v ^ 2 / ((S + 1) * R ^ 2 * 10 ^ 15) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  -- `t^{320/323} ≤ D`
  have hkey : t ^ (320 / 323 : ℝ) ≤ D := by
    have h1 : t ≤ D ^ (323 / 320 : ℝ) := by
      rw [ht, hD] at *
      exact le_trans htε hε
    have h2 : t ^ (320 / 323 : ℝ) ≤ (D ^ (323 / 320 : ℝ)) ^ (320 / 323 : ℝ) :=
      Real.rpow_le_rpow ht0.le h1 (by norm_num)
    have h3 : (D ^ (323 / 320 : ℝ)) ^ (320 / 323 : ℝ) = D := by
      rw [← Real.rpow_mul hD0,
        show (323 / 320 : ℝ) * (320 / 323) = 1 by norm_num, Real.rpow_one]
    rwa [h3] at h2
  -- the `S`-row: `S R² t^{320/323} 10¹⁵ ≤ A²`
  have hSR : S * R ^ 2 * t ^ (320 / 323 : ℝ) * 10 ^ 15 ≤ BoseGases.a v ^ 2 := by
    have hmul : t ^ (320 / 323 : ℝ) * ((S + 1) * R ^ 2 * 10 ^ 15)
        ≤ D * ((S + 1) * R ^ 2 * 10 ^ 15) :=
      mul_le_mul_of_nonneg_right hkey
        (mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num))
    have hDa : D * ((S + 1) * R ^ 2 * 10 ^ 15) = BoseGases.a v ^ 2 := by
      rw [hD]
      exact div_mul_cancel₀ _
        (mul_ne_zero (mul_ne_zero (by linarith) (by positivity)) (by norm_num))
    have h3 : t ^ (320 / 323 : ℝ) * ((S + 1) * R ^ 2 * 10 ^ 15) ≤ BoseGases.a v ^ 2 :=
      hmul.trans (le_of_eq hDa)
    have hSRm : S * R ^ 2 ≤ (S + 1) * R ^ 2 := by nlinarith [hS, hR]
    have h2 : S * R ^ 2 * (t ^ (320 / 323 : ℝ) * 10 ^ 15)
        ≤ (S + 1) * R ^ 2 * (t ^ (320 / 323 : ℝ) * 10 ^ 15) :=
      mul_le_mul_of_nonneg_right hSRm
        (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos ht0 _)) (by norm_num))
    nlinarith [h2, h3]
  -- `S R² ≤ A²/(t^{320/323} 10¹⁵)`
  have hdiv : S * R ^ 2 ≤ BoseGases.a v ^ 2 / (t ^ (320 / 323 : ℝ) * 10 ^ 15) := by
    rw [le_div_iff₀ (mul_pos (Real.rpow_pos_of_pos ht0 _) (by norm_num))]
    nlinarith [hSR]
  -- the two denominators
  have hden : t ^ (326 / 323 : ℝ) ≤ t ^ (320 / 323 : ℝ) * 10 ^ 15 := by
    have h1 : t ^ (326 / 323 : ℝ) ≤ t ^ (320 / 323 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
    have h2 : t ^ (320 / 323 : ℝ) ≤ t ^ (320 / 323 : ℝ) * 10 ^ 15 :=
      le_mul_of_one_le_right (le_of_lt (Real.rpow_pos_of_pos ht0 _)) (by norm_num)
    linarith
  have hcmp : BoseGases.a v ^ 2 / (t ^ (320 / 323 : ℝ) * 10 ^ 15)
      ≤ BoseGases.a v ^ 2 / t ^ (326 / 323 : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos ht0 _) hden
  have hellsq : BoseGases.a v ^ 2 / t ^ (326 / 323 : ℝ) = (Work.BoseFixR.ell v μ) ^ 2 := by
    rw [ell_sq_zeta hμ hav, div_eq_mul_inv, Real.rpow_neg ht0.le]
  have hSRle : S * R ^ 2 ≤ (Work.BoseFixR.ell v μ) ^ 2 :=
    hdiv.trans (hcmp.trans (le_of_eq hellsq))
  -- divide by `ℓ²`
  have hℓpos : 0 < (Work.BoseFixR.ell v μ) ^ 2 := by
    rw [← hellsq]
    positivity
  rw [div_pow, show S * (R ^ 2 / (Work.BoseFixR.ell v μ) ^ 2)
      = S * R ^ 2 / (Work.BoseFixR.ell v μ) ^ 2 by ring]
  exact (div_le_one hℓpos).mpr hSRle

end Work.BoseFixR.All
