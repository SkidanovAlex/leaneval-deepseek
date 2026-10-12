import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxSliding.Assembly
import Submission.Work.SmallBoxSliding.Band
import Submission.Work.SmallBoxSliding.Jensen
import Submission.Work.SmallBoxSliding.boxMass_integral_u
import Submission.Work.SmallBoxSliding.chiSmallB_continuous_joint
import Submission.Work.SmallBoxSliding.integral_chiMass_eq
import Submission.Work.SmallBoxSliding.integral_chiSmallB_sq_u
import Submission.Work.SmallBoxSliding.nBoxInd_integral_u
import Submission.Work.SmallBoxSliding.qLHSwordB_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem abs_wSmallScaled_div_convScale_le {M : ℕ} (hM : 1 ≤ M) {ℓ d R Bv : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0)
    (hfb : ∀ z : EuclideanSpace ℝ (Fin 3), |f z| ≤ Bv) (hR : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (z : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallScaled M (ℓ * d) f z / Submission.BoseGases.convScale ℓ z|
      ≤ 2 * Bv / Work.SmallBoxSliding.smallConvLower M := by
  have hlc : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  -- the numerator is dominated by the function itself, via the small-convolution
  -- lower bound on the `ℓd`-support of `f`
  have hD : |Submission.BoseGases.wSmallScaled M (ℓ * d) f z|
      ≤ |f z| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hlc hfsupp hR z
  by_cases hnorm : ‖z‖ ≤ R
  · -- on the support, `(χ⋆χ)(·/ℓ) ≥ 1/2` (the `chiR0` diluteness regime)
    have hcv : (1 : ℝ) / 2 ≤ Submission.BoseGases.convScale ℓ z :=
      Submission.BoseGases.convScale_ge_half_ball hℓ (norm_nonneg z)
        (le_trans hnorm hRχ) le_rfl
    have hpos : 0 < Submission.BoseGases.convScale ℓ z := by linarith
    have hinv : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ 2 := by
      rw [abs_of_pos (inv_pos.mpr hpos)]
      rw [inv_le_iff_one_le_mul₀ hpos]
      linarith
    rw [div_eq_mul_inv, abs_mul]
    calc |Submission.BoseGases.wSmallScaled M (ℓ * d) f z|
            * |(Submission.BoseGases.convScale ℓ z)⁻¹|
        ≤ (|f z| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
          mul_le_mul hD hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) hSpos.le)
      _ = 2 * |f z| / Work.SmallBoxSliding.smallConvLower M := by ring
      _ ≤ 2 * Bv / Work.SmallBoxSliding.smallConvLower M :=
          div_le_div_of_nonneg_right (by linarith [hfb z]) hSpos.le
  · -- off the support both the numerator and its renormalised version vanish
    have hz0 : f z = 0 := hfsupp z (le_of_lt (lt_of_not_ge hnorm))
    have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) f z = 0 := by
      dsimp [Submission.BoseGases.wSmallScaled]
      rw [hz0, zero_div]
    rw [hw0, zero_div, abs_zero]
    exact div_nonneg (by linarith [le_trans (abs_nonneg (f z)) (hfb z)]) hSpos.le

end Work.BoseFixB1
