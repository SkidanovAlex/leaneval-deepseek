import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FockBridge.Defs
import Submission.Work.FockBridge.convexOn_inv_Ioi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.convexOn_dlDensityCoeff`

FS's convex density factor `F(t) = c(t−μ)²/(1 + tμ⁻¹)` (`final_v2.tex` l. 4121,
`Work.FockBridge.dlDensityCoeff`) is **convex on the density half-line** `t ≥ 0`, for every
`c ≥ 0` and `μ > 0`.  This is what lets the DL per-box threshold be minimised/bounded by
convexity in the local density `t = n/|B|`.

## The mathematics

For `μ > 0` and `t ≥ 0` the denominators are positive and

    c(t−μ)²/(1 + tμ⁻¹) = cμ(t−μ)²/(t+μ) = cμ(t+μ) − 4cμ² + 4cμ³/(t+μ)
                       = cμ·t − 3cμ² + 4cμ³·(t+μ)⁻¹ .

The right-hand side is an affine function of `t` plus the non-negative multiple `4cμ³ ≥ 0` of
the *shifted inverse* `t ↦ (t+μ)⁻¹`, and `x ↦ x⁻¹` is convex on `(0,∞)`
(`Work.FockBridge.convexOn_inv_Ioi`), which the shift `t ↦ t+μ` maps `[0,∞)` into.  Hence the
sum is convex on `[0,∞)`.
-/

namespace Work.FockBridge

/-- The inverse is convex on the positive half-line, so its composition with the (positive)
shift `t ↦ t + μ` is convex on `[0, ∞)`. -/
theorem convexOn_shifted_inv {μ : ℝ} (hμ : 0 < μ) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t => (t + μ)⁻¹) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro t ht u hu a b ha hb hab
  simp only [smul_eq_mul]
  have ht0 : (0 : ℝ) ≤ t := ht
  have hu0 : (0 : ℝ) ≤ u := hu
  have htμ : 0 < t + μ := by linarith
  have huμ : 0 < u + μ := by linarith
  have h := convexOn_inv_Ioi.2 htμ huμ ha hb hab
  simp only [smul_eq_mul] at h
  have heq : a * (t + μ) + b * (u + μ) = a * t + b * u + μ := by
    rw [mul_add, mul_add]; nlinarith [hab]
  rwa [heq] at h

/-- The algebraic normal form of the DL density factor: an affine part plus a multiple of the
shifted inverse `(t+μ)⁻¹`, valid for `μ > 0` and `t ≥ 0`. -/
theorem dlDensityCoeff_decomp {c μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    dlDensityCoeff c μ t = c * μ * t - 3 * c * μ ^ 2 + 4 * c * μ ^ 3 * (t + μ)⁻¹ := by
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have htμ : t + μ ≠ 0 := by positivity
  unfold dlDensityCoeff
  rw [show 1 + t * μ⁻¹ = (t + μ) * μ⁻¹ by field_simp; ring]
  field_simp
  ring

/-- **The DL density factor is convex on `[0, ∞)`** (FS `final_v2.tex` l. 4121). -/
theorem convexOn_dlDensityCoeff {c μ : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t => Work.FockBridge.dlDensityCoeff c μ t) := by
  have hshift := convexOn_shifted_inv hμ
  have hscaled : ConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun t => 4 * c * μ ^ 3 * (t + μ)⁻¹) := by
    have h := hshift.smul (show (0 : ℝ) ≤ 4 * c * μ ^ 3 by positivity)
    simpa [smul_eq_mul] using h
  have hlin : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => c * μ * t) := by
    have h := (convexOn_id (convex_Ici (0 : ℝ))).smul (show (0 : ℝ) ≤ c * μ by positivity)
    simpa [smul_eq_mul] using h
  have hcst : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun _ : ℝ => -(3 * c * μ ^ 2)) :=
    convexOn_const _ (convex_Ici 0)
  have hmain : ConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun t => c * μ * t - 3 * c * μ ^ 2 + 4 * c * μ ^ 3 * (t + μ)⁻¹) :=
    ((hlin.add hcst).add hscaled).congr (fun t _ => by simp only [Pi.add_apply]; ring)
  exact hmain.congr (fun t ht => (dlDensityCoeff_decomp hμ ht).symm)

end Work.FockBridge
