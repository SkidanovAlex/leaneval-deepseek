import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.ChiWitness
import Submission.ConvChiBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le`

The renormalisation factor `convScale ℓ z = (χ⋆χ)(z/ℓ)` (with the corpus's cubic bump `χ`,
`Submission.KernelIds`) is bounded below by a **positive constant, uniformly in `ℓ > 0`**, on the
closed ball of radius `ℓ/8`:

    ∃ c > 0, ∀ ℓ > 0, ∀ z, ‖z‖ ≤ ℓ/8 → c ≤ convScale ℓ z .

The proof has two parts.

* *Pointwise strict positivity.*  For `‖w‖ ≤ 1/8` the integrand `y ↦ χ y · χ (w − y)` of
  `conv3 χ χ w = ∫ y, χ y · χ (w − y)` is continuous, nonnegative, compactly supported and is
  **nonzero at the single point `y₀ := (1/2) • w`**: both `y₀` and `w − y₀ = (1/2) • w` have norm
  `‖w‖/2 ≤ 1/16 ≤ 1/4`, where the bump equals the positive constant `1/√chiNormSq`
  (`chiBase_eq_one_of_norm_le`).  Hence `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`
  gives `0 < conv3 χ χ w`.
* *Uniformity.*  `conv3 χ χ` is continuous (`conv_contDiff`) and the closed ball of radius `1/8`
  is compact and nonempty, so `IsCompact.exists_isMinOn` yields a point `w₀` of the closed ball
  minimising `conv3 χ χ` there; the constant `c := conv3 χ χ w₀` is positive by the previous step
  and is the required uniform lower bound.

Rescaling `z ↦ (ℓ⁻¹) • z` converts `‖z‖ ≤ ℓ/8` into `‖(ℓ⁻¹) • z‖ ≤ 1/8`, which is where the
uniformity in `ℓ` comes from.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Metric
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **Pointwise strict positivity of the bump self-convolution on the `1/8`-ball.**
For `‖w‖ ≤ 1/8`, `conv3 chi chi w = ∫ y, chi y · chi (w − y) > 0`: at `y₀ := (1/2) • w` both
arguments have norm `‖w‖/2 ≤ 1/16 ≤ 1/4`, so both factors of the integrand equal the positive
constant `1/√chiNormSq` there, and continuity of the (nonnegative, compactly supported) integrand
upgrades a single positive value to a positive integral. -/
private lemma conv3_chi_pos_of_norm_le_eighth {w : ℝ³} (hw : ‖w‖ ≤ 1 / 8) :
    0 < conv3 chi chi w := by
  have hy₀norm : ‖(1 / 2 : ℝ) • w‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  have hwmy₀ : w - (1 / 2 : ℝ) • w = (1 / 2 : ℝ) • w := by module
  have hwy₀norm : ‖w - (1 / 2 : ℝ) • w‖ ≤ 1 / 4 := by
    rw [hwmy₀]; exact hy₀norm
  have hchi_y : chi ((1 / 2 : ℝ) • w) = (Real.sqrt chiNormSq)⁻¹ := by
    rw [chi, chiBase_eq_one_of_norm_le hy₀norm, one_div]
  have hchi_wy : chi (w - (1 / 2 : ℝ) • w) = (Real.sqrt chiNormSq)⁻¹ := by
    rw [chi, chiBase_eq_one_of_norm_le hwy₀norm, one_div]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun y : ℝ³ => chi y * chi (w - y)) (x := (1 / 2 : ℝ) • w) ?_ ?_ ?_ ?_
  · exact chi_continuous.mul (chi_continuous.comp (continuous_const.sub continuous_id))
  · exact chi_hasCompactSupport.mul_right (f' := fun y : ℝ³ => chi (w - y))
  · intro y; exact mul_nonneg (chi_nonneg y) (chi_nonneg (w - y))
  · show chi ((1 / 2 : ℝ) • w) * chi (w - (1 / 2 : ℝ) • w) ≠ 0
    rw [hchi_y, hchi_wy]
    exact mul_ne_zero (inv_ne_zero chi_sqrt_ne_zero) (inv_ne_zero chi_sqrt_ne_zero)

/-- **Uniform positive lower bound for `conv3 chi chi` on the `1/8`-ball.**  This is the analytic
content of `convScale_ge_of_norm_le`, with the scaling `z ↦ (ℓ⁻¹) • z` stripped off. -/
theorem exists_pos_le_conv3_chi_eighth :
    ∃ c : ℝ, 0 < c ∧ ∀ w : ℝ³, ‖w‖ ≤ 1 / 8 → c ≤ conv3 chi chi w := by
  obtain ⟨w₀, hw₀mem, hw₀min⟩ :=
    (isCompact_closedBall (0 : ℝ³) (1 / 8)).exists_isMinOn
      ⟨0, by simp [Metric.mem_closedBall]⟩
      conv_contDiff.continuous.continuousOn
  refine ⟨conv3 chi chi w₀,
    conv3_chi_pos_of_norm_le_eighth (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw₀mem),
    ?_⟩
  intro w hw
  exact hw₀min (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)

theorem convScale_ge_of_norm_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖z‖ ≤ ℓ / 8 → c ≤ Submission.BoseGases.convScale ℓ z := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_conv3_chi_eighth
  refine ⟨c, hcpos, ?_⟩
  intro ℓ hℓ z hz
  have hwn : ‖(ℓ⁻¹) • z‖ ≤ 1 / 8 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    calc ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * (ℓ / 8) := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hℓ.le)
      _ = 1 / 8 := by field_simp
  have hmin := hc ((ℓ⁻¹) • z) hwn
  simpa [Submission.BoseGases.convScale] using hmin

end Work.BoseFixB3.CS.Pieces
