import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBimg_J_le` — the `ℓ⁻⁴`-moment bound for a `(1 + Λ‖a‖)⁴`-weighted state

The statement is a purely measure-theoretic (and, up to the two elementary real inequalities
below, purely arithmetic) consequence of the *weighted* `L¹` bound

    ∫ a, ‖ψ a‖ (1 + Λ‖a‖)^4 ≤ Bm   for some  Λ ≥ 1:

    ℓ ^ (-(4 : ℤ)) * ∫ a, (R + ‖a‖)^4 ‖ψ a‖
      ≤ 16 * Bm * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ)))        (ℓ > 0, R > 0).

The pointwise mechanism (with `t = ‖a‖` and `L = ℓ ^ (-(4:ℤ))`) is

    L (R + t)^4 ≤ L · 16 (R^4 + t^4)          (`(x+y)^4 ≤ 16(x^4+y^4)` for `x,y ≥ 0`)
                = 16 (L R^4 + L t^4)
                = 16 ((R/ℓ)^4 + (t/ℓ)^4)
                ≤ 16 ((R/ℓ)^4 + (Λℓ)^(-4) (1 + Λt)^4)      (`t/ℓ ≤ (1+Λt)/(Λℓ)`)
                ≤ 16 ((R/ℓ)^4 + (Λℓ)^(-4)) (1 + Λt)^4      (`1 ≤ (1+Λt)^4`),

and the constant `16` is exactly the one appearing in the statement (the sharper constant `8`
would do, as would `(1+Λt)^4 ≥ 1` on the `R`-term).  Integrating against `‖ψ a‖ ≥ 0` with
`MeasureTheory.integral_mono_of_nonneg` and pulling the constants out of the integral
(`MeasureTheory.integral_const_mul`) gives the claim.  Note that no integrability of
`a ↦ (R + ‖a‖)^4 ‖ψ a‖` has to be assumed or proved: the majorant
`a ↦ 16 ((R/ℓ)^4 + (Λℓ)^(-4)) (‖ψ a‖ (1 + Λ‖a‖)^4)` is integrable by hypothesis, and
`integral_mono_of_nonneg` is stated for arbitrary (possibly non-integrable) minorants.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The elementary power inequality `(x + y)^4 ≤ 16 (x^4 + y^4)` for `x, y ≥ 0`
(since `x + y ≤ 2 * max x y`). -/
private lemma pow4_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 4 ≤ 16 * (x ^ 4 + y ^ 4) := by
  have hxM : x ≤ max x y := le_max_left _ _
  have hyM : y ≤ max x y := le_max_right _ _
  have hsum : x + y ≤ 2 * max x y := by linarith
  have h1 : (x + y) ^ 4 ≤ (2 * max x y) ^ 4 := pow_le_pow_left₀ (by linarith) hsum 4
  have h2 : (2 * max x y) ^ 4 = 16 * (max x y) ^ 4 := by ring
  have h3 : (max x y) ^ 4 ≤ x ^ 4 + y ^ 4 := by
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy]; nlinarith [pow_nonneg hx 4]
    · rw [max_eq_left hyx]; nlinarith [pow_nonneg hy 4]
  calc (x + y) ^ 4 ≤ (2 * max x y) ^ 4 := h1
    _ = 16 * (max x y) ^ 4 := h2
    _ ≤ 16 * (x ^ 4 + y ^ 4) := by linarith

/-- The pointwise core of the target: for `ℓ > 0`, `Λ ≥ 1`, `R, t ≥ 0`,

    ℓ ^ (-(4:ℤ)) (R + t)^4 ≤ 16 ((R/ℓ)^4 + (Λℓ)^(-(4:ℤ))) (1 + Λt)^4 . -/
private lemma zpow_mul_pow4_le {ℓ Λ R t : ℝ} (hℓ : 0 < ℓ) (hΛ : 1 ≤ Λ) (hR : 0 ≤ R)
    (ht : 0 ≤ t) :
    ℓ ^ (-(4 : ℤ)) * (R + t) ^ 4
      ≤ 16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (1 + Λ * t) ^ 4 := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hL : 0 < ℓ ^ (-(4 : ℤ)) := zpow_pos hℓ _
  have hbig : (R + t) ^ 4 ≤ 16 * (R ^ 4 + t ^ 4) := pow4_add_le R t hR ht
  -- the `R`-term: `ℓ^{-4} R^4 = (R/ℓ)^4`
  have hR4 : ℓ ^ (-(4 : ℤ)) * R ^ 4 = (R / ℓ) ^ 4 := by
    rw [zpow_neg]; norm_num; rw [div_pow, div_eq_mul_inv]; ring
  -- the `t`-term: `ℓ^{-4} t^4 ≤ (Λℓ)^{-4} (1 + Λt)^4`
  have ht4 : ℓ ^ (-(4 : ℤ)) * t ^ 4 ≤ (Λ * ℓ) ^ (-(4 : ℤ)) * (1 + Λ * t) ^ 4 := by
    have hΛℓ : (0 : ℝ) < Λ * ℓ := by positivity
    have h1 : ℓ ^ (-(4 : ℤ)) * t ^ 4 = (t / ℓ) ^ 4 := by
      rw [zpow_neg]; norm_num; rw [div_pow, div_eq_mul_inv]; ring
    have h2 : (Λ * ℓ) ^ (-(4 : ℤ)) * (1 + Λ * t) ^ 4 = ((1 + Λ * t) / (Λ * ℓ)) ^ 4 := by
      rw [zpow_neg]; norm_num; rw [div_pow, div_eq_mul_inv]; ring
    rw [h1, h2]
    apply pow_le_pow_left₀ (div_nonneg ht hℓ.le)
    rw [div_le_div_iff₀ hℓ hΛℓ]
    nlinarith [mul_nonneg hΛ0 ht, hℓ]
  -- absorb the `(R/ℓ)^4` into `(R/ℓ)^4 (1 + Λt)^4`
  have hA : (R / ℓ) ^ 4 ≤ (R / ℓ) ^ 4 * (1 + Λ * t) ^ 4 := by
    have h1 : (1 : ℝ) ≤ (1 + Λ * t) ^ 4 := by
      have : 1 ≤ 1 + Λ * t := by linarith [mul_nonneg hΛ0 ht]
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ (1 + Λ * t) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
    have hRl : 0 ≤ (R / ℓ) ^ 4 := by positivity
    calc (R / ℓ) ^ 4 = (R / ℓ) ^ 4 * 1 := by ring
      _ ≤ (R / ℓ) ^ 4 * (1 + Λ * t) ^ 4 := mul_le_mul_of_nonneg_left h1 hRl
  have h4 : ℓ ^ (-(4 : ℤ)) * R ^ 4 + ℓ ^ (-(4 : ℤ)) * t ^ 4
      ≤ ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (1 + Λ * t) ^ 4 := by
    rw [hR4]
    have h5 : (R / ℓ) ^ 4 * (1 + Λ * t) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ)) * (1 + Λ * t) ^ 4
        = ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (1 + Λ * t) ^ 4 := by ring
    linarith [hA, ht4, h5]
  calc ℓ ^ (-(4 : ℤ)) * (R + t) ^ 4
      ≤ ℓ ^ (-(4 : ℤ)) * (16 * (R ^ 4 + t ^ 4)) := mul_le_mul_of_nonneg_left hbig hL.le
    _ = 16 * (ℓ ^ (-(4 : ℤ)) * R ^ 4 + ℓ ^ (-(4 : ℤ)) * t ^ 4) := by ring
    _ ≤ 16 * (((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (1 + Λ * t) ^ 4) := by linarith [h4]
    _ = 16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (1 + Λ * t) ^ 4 := by ring

theorem chBimg_J_le {Λ ℓ R Bm : ℝ} (hℓ : 0 < ℓ) (hΛ : 1 ≤ Λ) (hR : 0 < R)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψi : MeasureTheory.Integrable
      (fun a : EuclideanSpace ℝ (Fin 3) => ‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4))
    (hψ : ∫ a : EuclideanSpace ℝ (Fin 3), ‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4 ≤ Bm) :
    ℓ ^ (-(4 : ℤ)) * (∫ a : EuclideanSpace ℝ (Fin 3), (R + ‖a‖) ^ 4 * ‖ψ a‖)
      ≤ 16 * Bm * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) := by
  have hℓ4 : (0 : ℝ) < ℓ ^ (-(4 : ℤ)) := zpow_pos hℓ _
  have hKnn : 0 ≤ (R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ)) := by
    have h1 : 0 ≤ (R / ℓ) ^ 4 := pow_nonneg (div_nonneg hR.le hℓ.le) 4
    have h2 : 0 ≤ (Λ * ℓ) ^ (-(4 : ℤ)) :=
      le_of_lt (zpow_pos (by positivity : (0 : ℝ) < Λ * ℓ) _)
    linarith
  have hgi : MeasureTheory.Integrable (fun a : E3 =>
      16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4)) :=
    hψi.const_mul _
  have hpt : ∀ a : E3,
      ℓ ^ (-(4 : ℤ)) * ((R + ‖a‖) ^ 4 * ‖ψ a‖)
        ≤ 16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4) := by
    intro a
    have h := zpow_mul_pow4_le hℓ hΛ hR.le (norm_nonneg a)
    calc ℓ ^ (-(4 : ℤ)) * ((R + ‖a‖) ^ 4 * ‖ψ a‖)
        = (ℓ ^ (-(4 : ℤ)) * (R + ‖a‖) ^ 4) * ‖ψ a‖ := by ring
      _ ≤ (16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (1 + Λ * ‖a‖) ^ 4) * ‖ψ a‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = 16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4) := by ring
  have hnn : ∀ a : E3, 0 ≤ ℓ ^ (-(4 : ℤ)) * ((R + ‖a‖) ^ 4 * ‖ψ a‖) := by
    intro a
    refine mul_nonneg hℓ4.le (mul_nonneg ?_ (norm_nonneg _))
    exact pow_nonneg (add_nonneg hR.le (norm_nonneg a)) 4
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall hnn) hgi (Filter.Eventually.of_forall hpt)
  rw [← MeasureTheory.integral_const_mul]
  calc ∫ a : E3, ℓ ^ (-(4 : ℤ)) * ((R + ‖a‖) ^ 4 * ‖ψ a‖)
      ≤ ∫ a : E3,
          16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * (‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4) := hmono
    _ = 16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) *
          ∫ a : E3, ‖ψ a‖ * (1 + Λ * ‖a‖) ^ 4 :=
          MeasureTheory.integral_const_mul _ _
    _ ≤ 16 * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) * Bm :=
          mul_le_mul_of_nonneg_left hψ (mul_nonneg (by norm_num) hKnn)
    _ = 16 * Bm * ((R / ℓ) ^ 4 + (Λ * ℓ) ^ (-(4 : ℤ))) := by ring

end Work.BoseBoxFock.PCFU
