import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.fsTBumpDefs` — the plateau constant of the localisation window

The corpus's localisation window is `chiScale ℓ = χ(·/ℓ)`, with `χ` the `L²`-normalised
corpus bump (`Submission.BoseGases.chi`, `∫χ² = 1`, `chi_L2`).  On its plateau — the ball
of radius `ℓ/4`, where `chiBase = 1` (`chiBase_eq_one_of_norm_le`) — it is *not* equal to
`1` but to the constant

    `chiPlateau = (√chiNormSq)⁻¹`        (`chiNormSq = ∫chiBase²`).

This is the constant that appears when a fixed bump `θ` (supported in a ball of radius
`r ≪ ℓ`) is measured against `chiScale ℓ`: the kinetic word built from `chiScale ℓ` sees
`chiPlateau²·∫|∇θ|²` on the plateau.  The file records the two facts about it that the
proof of `Work.BoseFixB1S.fsT_bump_ge_dirichlet` consumes directly:

* `chiScale_eq_chiPlateau` — the window equals `chiPlateau` on the closed ball of radius
  `ℓ/4` (for `0 < ℓ`);
* `chiPlateau_pos` — the constant is positive.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB1S

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The plateau value of the localisation window**: `chiScale ℓ x = chiPlateau` for
`‖x‖ ≤ ℓ/4`.  Equal to `(√chiNormSq)⁻¹` (`= Work.ChiSmall.chiSupAbs`). -/
noncomputable def chiPlateau : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹

lemma chiPlateau_nonneg : 0 ≤ chiPlateau :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma chiPlateau_pos : 0 < chiPlateau :=
  inv_pos.mpr (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos)

lemma chiPlateau_sq : chiPlateau ^ 2 = (Submission.BoseGases.chiNormSq)⁻¹ := by
  rw [chiPlateau, inv_pow, Real.sq_sqrt (le_of_lt Submission.BoseGases.chiNormSq_pos)]

/-- **The window is flat on the ball of radius `ℓ/4`**: `chiScale ℓ x = chiPlateau`
whenever `‖x‖ ≤ ℓ/4` (`0 < ℓ`). -/
lemma chiScale_eq_chiPlateau {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ³} (hx : ‖x‖ ≤ ℓ / 4) :
    Submission.BoseGases.chiScale ℓ x = chiPlateau := by
  rw [Submission.BoseGases.chiScale, Submission.BoseGases.chi, chiPlateau]
  have hnorm : ‖(ℓ⁻¹ : ℝ) • x‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    have h1 : (ℓ⁻¹) * ‖x‖ ≤ ℓ⁻¹ * (ℓ / 4) :=
      mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hℓ))
    have h2 : ℓ⁻¹ * (ℓ / 4) = 1 / 4 := by field_simp
    linarith
  rw [Submission.BoseGases.chiBase_eq_one_of_norm_le hnorm, one_div]

end Work.BoseFixB1S
