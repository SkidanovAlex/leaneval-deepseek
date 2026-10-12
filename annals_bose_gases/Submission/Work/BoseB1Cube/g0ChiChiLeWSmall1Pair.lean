import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.g0_chi_chi_le_wSmall1Pair`

The pointwise comparison underlying the lower bound for the localised one-body mass `boxM1`
(`Work.BoseB1Cube.boxM1GeConvChiMass`): for `z = x − y` with `g₀ z ≥ 0`,

    g₀ z · χ_B(x) · χ_B(y)  ≤  w_{1,B(u)}(x,y) ,

where `χ_B = chiSmallB M ℓ d u` and `w_{1,B(u)} = wSmall1Pair h M ℓ d u`.

This is the `ω₀ ↔ 1`-free half of the proof of `Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass`
(FS `lm:w2>w1`); the argument is reproduced here because the version in that module is
`private`.  If `‖x − y‖ < R ≤ ℓd/16` both renormalisation denominators lie in `(0,1]`
(`smallConvLower M ≤ (χ_M⋆χ_M)((x−y)/(ℓd)) ≤ 1` and `1/2 ≤ (χ⋆χ)((x−y)/ℓ) ≤ 1`), so
`1/(ab) ≥ 1` and `g₀ z/(ab) ≥ g₀ z`; if `‖x − y‖ ≥ R` then `g₀ z = 0` and both sides vanish.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000

/-- **Pointwise comparison of the localised kernel with `g₀ ⊗ χ_B ⊗ χ_B`.**

For `z = x − y` with `g₀ z ≥ 0` one has

    g₀ z · χ_B(x) · χ_B(y) ≤ w_{1,B(u)}(x,y) .

Indeed, if `‖z‖ < R ≤ ℓd/16` both renormalisation denominators are in `(0,1]`
(`smallConvLower M ≤ (χ_M⋆χ_M)(z/(ℓd)) ≤ 1` and `1/2 ≤ (χ⋆χ)(z/ℓ) ≤ 1`), so
`1/(ab) ≥ 1` and `g₀ z/(ab) ≥ g₀ z`; if `‖z‖ ≥ R` then `g₀ z = 0` and both sides vanish. -/
lemma g0_chi_chi_le_wSmall1Pair {v : E3 → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR0 : 0 < R)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : E3) (hg : 0 ≤ Submission.BoseGases.g0 v h (x - y)) :
    Submission.BoseGases.g0 v h (x - y) * Submission.BoseGases.chiSmallB M ℓ d u x
        * Submission.BoseGases.chiSmallB M ℓ d u y
      ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  have hfac : Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
        * (Submission.BoseGases.g0 v h (x - y)
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                * Submission.BoseGases.convScale ℓ (x - y)))
        * Submission.BoseGases.chiSmallB M ℓ d u y := by
    rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
      Submission.BoseGases.wSmallScaled, div_div]
  have hXx : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hXy : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  by_cases hz : ‖x - y‖ < R
  · have hzR : ‖x - y‖ ≤ R := le_of_lt hz
    have hld : 0 < ℓ * d := mul_pos hℓ hd
    -- the `ℓd`-denominator is `≥ smallConvLower M`
    have hcoord : ∀ j : Fin 3, |(((ℓ * d)⁻¹) • (x - y)).ofLp j| ≤ 1 / 16 := by
      intro j
      have hnorm : ‖((ℓ * d)⁻¹) • (x - y)‖ ≤ 1 / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hld)]
        calc (ℓ * d)⁻¹ * ‖x - y‖ ≤ (ℓ * d)⁻¹ * R :=
              mul_le_mul_of_nonneg_left hzR (inv_pos.mpr hld).le
          _ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) := mul_le_mul_of_nonneg_left hR (inv_pos.mpr hld).le
          _ = 1 / 16 := by field_simp
      exact le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hnorm
    have ha : Work.SmallBoxSliding.smallConvLower M
        ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
      Work.SmallBoxSliding.conv3Small_coord_lower hM _ hcoord
    have hapos : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
      lt_of_lt_of_le (Work.SmallBoxSliding.smallConvLower_pos M) ha
    have ha1 : Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) ≤ 1 := by
      have h' := Submission.BoseGases.conv3Small_abs_le_one hM (((ℓ * d)⁻¹) • (x - y))
      rw [abs_le] at h'
      exact h'.2
    have hb : 1 / 2 ≤ Submission.BoseGases.convScale ℓ (x - y) :=
      Submission.BoseGases.convScale_ge_half_of_le hℓ hRχ hzR
    have hbpos : 0 < Submission.BoseGases.convScale ℓ (x - y) :=
      lt_of_lt_of_le (by norm_num) hb
    have hb1 : Submission.BoseGases.convScale ℓ (x - y) ≤ 1 :=
      Submission.BoseGases.conv3chi_le_one ((ℓ⁻¹) • (x - y))
    have hab : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
        * Submission.BoseGases.convScale ℓ (x - y) := mul_pos hapos hbpos
    have hab1 : Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
        * Submission.BoseGases.convScale ℓ (x - y) ≤ 1 := by
      nlinarith [ha1, hb1, hapos.le, hbpos.le]
    have hmid : Submission.BoseGases.g0 v h (x - y)
        ≤ Submission.BoseGases.g0 v h (x - y)
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                * Submission.BoseGases.convScale ℓ (x - y)) := by
      rw [le_div_iff₀ hab]
      nlinarith [hg, hab1]
    rw [hfac]
    calc Submission.BoseGases.g0 v h (x - y) * Submission.BoseGases.chiSmallB M ℓ d u x
          * Submission.BoseGases.chiSmallB M ℓ d u y
        = Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.g0 v h (x - y)
            * Submission.BoseGases.chiSmallB M ℓ d u y := by ring
      _ ≤ Submission.BoseGases.chiSmallB M ℓ d u x
            * (Submission.BoseGases.g0 v h (x - y)
                / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                    * Submission.BoseGases.convScale ℓ (x - y)))
            * Submission.BoseGases.chiSmallB M ℓ d u y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid hXx) hXy
  · have hg0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_not_gt hz) h
    rw [hfac, hg0]
    simp
end Work.BoseB1Cube
