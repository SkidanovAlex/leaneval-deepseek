import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxSliding.qLHSBAux
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem abs_wSmallScaled_div_convScale_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ d : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hR0 : 0 < R)
    (hR : R ≤ ℓ * d / 16)
    (hconv : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R → 1 / 2 ≤ Submission.BoseGases.convScale ℓ z)
    (h : Work.UBB.ScatSol v)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0)
    (z : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z|
      ≤ 2 * |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hlc : 0 < ℓ * d := mul_pos hℓ hd
  have hD : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
      ≤ |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hlc hsupp hR z
  by_cases hnorm : ‖z‖ ≤ R
  · have hcv : (1 : ℝ) / 2 ≤ Submission.BoseGases.convScale ℓ z := hconv z hnorm
    have hpos : 0 < Submission.BoseGases.convScale ℓ z := by linarith
    have hinv : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ 2 := by
      rw [abs_of_pos (inv_pos.mpr hpos), inv_le_comm₀ hpos (by norm_num)]
      norm_num
      exact hcv
    rw [div_eq_mul_inv, abs_mul]
    calc
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
            * |(Submission.BoseGases.convScale ℓ z)⁻¹|
          ≤ (|Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hD hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) hSpos.le)
      _ = 2 * |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M := by ring
  · have hz0 : Submission.BoseGases.g0 v h z = 0 := hsupp z (le_of_lt (lt_of_not_ge hnorm))
    have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z = 0 := by
      dsimp [Submission.BoseGases.wSmallScaled]
      rw [hz0]
      ring
    rw [hw0, hz0, zero_div, abs_zero]
    simp

end Work.BoseFixB1S
