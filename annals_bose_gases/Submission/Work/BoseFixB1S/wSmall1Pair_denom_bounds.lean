import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxSliding.Sliding
import Submission.Work.SmallBoxSliding.qLHSBAux
import Submission.Work.SmallBoxSliding.wSmall1Pair_mass_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bounds on the two-scale renormalisation denominator

The localised sliding kernel `wSmallPair` carries the *product* denominator

    denom(z) = (χ_M ⋆ χ_M)(z/(ℓd)) · (χ⋆χ)(z/ℓ)
             = convScaleSmall M (ℓd) z · convScale ℓ z

(`convScaleSmall_mul_wSmallScaled` cancels only the `ℓd`-factor; the remaining
`ℓ`-factor is the corpus `convScale`).  For the domination/integrability lemmas
of the sliding layer one needs `denom > 0` (so that the reciprocal is bounded
on the support of the numerator) and `denom ≤ 1` (the crude sup bound).

Both are elementary once the two factors are estimated separately, on the
regime of the statement (`‖z‖ ≤ R`, `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`):

* `convScaleSmall M (ℓd) z = (χ_M ⋆ χ_M)((ℓd)⁻¹ z)`, and `‖(ℓd)⁻¹ z‖ ≤ 1/16`
  puts the argument in the polydisc where the *positive* lower bound
  `smallConvLower M > 0` holds (`conv3Small_coord_lower`);
* `1/2 ≤ convScale ℓ z` on `‖z‖ ≤ R` (`convScale_ge_half_ball`, the `chiR0`
  regime);
* `convScaleSmall M (ℓd) z ≤ 1` (`conv3Small_abs_le_one`) and
  `convScale ℓ z ≤ 1` (`convScale_le_one`).
-/

namespace Work.BoseFixB1S

theorem wSmall1Pair_denom_bounds {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ‖z‖ ≤ R) :
    0 < Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z ∧
      Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z ≤ 1 := by
  have hlc : 0 < ℓ * d := mul_pos hℓ hd
  have hRnn : 0 ≤ R := le_trans (norm_nonneg z) hz
  -- the `ℓd`-scaled argument lies in the polydisc `|·_j| ≤ 1/16`
  have hcoord : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z).ofLp j| ≤ 1 / 16 := by
    intro j
    refine le_trans (Submission.BoseGases.coord_abs_le_norm _ j) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlc)]
    calc (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) :=
          mul_le_mul_of_nonneg_left (le_trans hz hR) (le_of_lt (inv_pos.mpr hlc))
      _ = 1 / 16 := by field_simp
  have hsmall : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
    have h1 := Work.SmallBoxSliding.conv3Small_coord_lower hM ((ℓ * d)⁻¹ • z) hcoord
    have h2 := Work.SmallBoxSliding.smallConvLower_pos M
    exact lt_of_lt_of_le h2 h1
  have hconv : 0 < Submission.BoseGases.convScale ℓ z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (Submission.BoseGases.convScale_ge_half_ball hℓ hRnn hRχ hz)
  have hub1 : Submission.BoseGases.convScaleSmall M (ℓ * d) z ≤ 1 := by
    have h := Submission.BoseGases.conv3Small_abs_le_one hM ((ℓ * d)⁻¹ • z)
    exact le_of_abs_le h
  have hub2 : Submission.BoseGases.convScale ℓ z ≤ 1 :=
    Submission.BoseGases.convScale_le_one ℓ z
  exact ⟨mul_pos hsmall hconv,
    by simpa using mul_le_mul hub1 hub2 (le_of_lt hconv) (by norm_num : (0 : ℝ) ≤ 1)⟩

end Work.BoseFixB1S
