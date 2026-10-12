import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1B.LocalisedModes
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem abs_wSmallInner_le_of_lower {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ d : ℝ} {M : ℕ} {c : ℝ}
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hc : 0 < c)
    (hR : R ≤ ℓ * d / 16)
    (hconv : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R → c ≤ Submission.BoseGases.convScale ℓ z)
    (h : Work.UBB.ScatSol v)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0) (z : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixB1B.wSmallInner M ℓ d (Submission.BoseGases.g0 v h) z|
      ≤ (1 / (Work.SmallBoxSliding.smallConvLower M * c)) * |Submission.BoseGases.g0 v h z| := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hlc : 0 < ℓ * d := mul_pos hℓ hd
  -- on the support of `g₀`, the renormalised numerator is dominated by `|g₀|/smallConvLower M`
  have hD : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
      ≤ |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hlc hsupp hR z
  by_cases hnorm : ‖z‖ ≤ R
  · -- inside the ball: `convScale ℓ z ≥ c > 0`, so `(convScale ℓ z)⁻¹ ≤ c⁻¹`
    have hcv : c ≤ Submission.BoseGases.convScale ℓ z := hconv z hnorm
    have hpos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le hc hcv
    have hinv : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ c⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr hpos)]
      exact (inv_le_inv₀ hpos hc).mpr hcv
    rw [show Work.BoseFixB1B.wSmallInner M ℓ d (Submission.BoseGases.g0 v h) z
        = Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
            / Submission.BoseGases.convScale ℓ z from rfl, div_eq_mul_inv, abs_mul]
    calc
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
            * |(Submission.BoseGases.convScale ℓ z)⁻¹|
          ≤ (|Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M) * c⁻¹ :=
            mul_le_mul hD hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) hSpos.le)
      _ = (1 / (Work.SmallBoxSliding.smallConvLower M * c)) * |Submission.BoseGases.g0 v h z| := by
            rw [div_eq_mul_inv, one_div, mul_inv_rev]
            ring
  · -- outside the ball both sides vanish
    have hz0 : Submission.BoseGases.g0 v h z = 0 := hsupp z (le_of_lt (lt_of_not_ge hnorm))
    have hw0 : Work.BoseFixB1B.wSmallInner M ℓ d (Submission.BoseGases.g0 v h) z = 0 := by
      rw [show Work.BoseFixB1B.wSmallInner M ℓ d (Submission.BoseGases.g0 v h) z
          = Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
              / Submission.BoseGases.convScale ℓ z from rfl,
        show Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          = Submission.BoseGases.g0 v h z / Submission.BoseGases.convScaleSmall M (ℓ * d) z
          from rfl,
        hz0, zero_div, zero_div]
    rw [hw0, hz0, abs_zero, mul_zero]

end Work.BoseFixB1S
