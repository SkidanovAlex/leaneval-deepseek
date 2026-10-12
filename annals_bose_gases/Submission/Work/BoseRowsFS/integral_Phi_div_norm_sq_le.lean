import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.integral_inv2_inv4_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.integral_Phi_div_norm_sq_le`

The bound `|∫_{ℝ³} Φ(p)/‖p‖² dp| ≤ 100 A` for a function obeying the pointwise decay
`|Φ p| ≤ A (1 + ‖p‖)⁻⁴`.

The dominating function `p ↦ (‖p‖²)⁻¹ (1 + ‖p‖)⁻⁴` has integral `4π/3 ≤ 100`
(`Work.BoseRowsFS.integral_inv2_inv4_le`); here we add the integrability of the
dominating function (`Submission.BoseGases.integrable_radial_r3` plus the one
dimensional integrability of `(1 + r)⁻⁴` on `(0,∞)`) and run the standard
chain `|∫ Φ| ≤ ∫ |Φ| ≤ A ∫ (1+‖p‖)⁻⁴/‖p‖² ≤ 100 A`.

The division by `‖p‖²` is Lean's total division, so at `p = 0` both the
integrand and the dominator take the value `0`; no separate treatment of the
origin is needed.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseRowsFS

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The dominating radial profile `(‖p‖²)⁻¹ (1 + ‖p‖)⁻⁴` is integrable on `ℝ³`. -/
lemma integrable_inv2_inv4_r3 :
    Integrable (fun p : ℝ³ => (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹) volume := by
  -- integrability of `r ↦ (1 + r)⁻⁴` on `(0,∞)`
  have hbase : IntegrableOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num)
    refine h.congr ?_
    change ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (r + 1) ^ (-4 : ℝ) = ((1 + r) ^ 4)⁻¹
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hr1 : 0 ≤ 1 + r := by linarith
    rw [add_comm r 1, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr1,
      Real.rpow_natCast]
  -- the radial profile of the ℝ³-integrand: `r² · (r²)⁻¹ (1+r)⁻⁴ = (1+r)⁻⁴` for `r > 0`
  have hprod : IntegrableOn
      (fun r : ℝ => r ^ 2 * ((r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹)) (Set.Ioi (0 : ℝ)) := by
    refine hbase.congr ?_
    change ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ((1 + r) ^ 4)⁻¹ = r ^ 2 * ((r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹)
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hr0 : (0 : ℝ) < r := hr
    have h2 : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr0)
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  exact (Submission.BoseGases.integrable_radial_r3
    (f := fun r : ℝ => (r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹)).mpr hprod

theorem integral_Phi_div_norm_sq_le {Φ : EuclideanSpace ℝ (Fin 3) → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hΦ : ∀ p : EuclideanSpace ℝ (Fin 3), |Φ p| ≤ A * ((1 + ‖p‖) ^ 4)⁻¹) :
    |(∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)| ≤ A * 100 := by
  -- the pointwise bound, with the two factors of the dominator written in the
  -- order used by `integral_inv2_inv4_le`
  have key : ∀ p : ℝ³, |Φ p / ‖p‖ ^ 2| ≤ A * ((‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹) := by
    intro p
    have h1 : |Φ p / ‖p‖ ^ 2| = |Φ p| * (‖p‖ ^ 2)⁻¹ := by
      rw [abs_div, abs_of_nonneg (sq_nonneg ‖p‖), div_eq_mul_inv]
    rw [h1]
    calc |Φ p| * (‖p‖ ^ 2)⁻¹
        ≤ (A * ((1 + ‖p‖) ^ 4)⁻¹) * (‖p‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (hΦ p) (inv_nonneg.mpr (sq_nonneg ‖p‖))
      _ = A * ((‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹) := by ring
  have hint : Integrable (fun p : ℝ³ => A * ((‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹)) volume :=
    integrable_inv2_inv4_r3.const_mul A
  calc |(∫ p : ℝ³, Φ p / ‖p‖ ^ 2)|
      ≤ ∫ p : ℝ³, |Φ p / ‖p‖ ^ 2| := abs_integral_le_integral_abs
    _ ≤ ∫ p : ℝ³, A * ((‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹) :=
        integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _) hint
          (Eventually.of_forall key)
    _ = A * ∫ p : ℝ³, (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹ :=
        integral_const_mul A _
    _ ≤ A * 100 := mul_le_mul_of_nonneg_left integral_inv2_inv4_le hA

end Work.BoseRowsFS
