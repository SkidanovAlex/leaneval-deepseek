import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.corpusBox.chiLam` is constant on the small ball

`Work.BoseK15.corpusBox` presents the corpus localisation function
`Submission.BoseGases.chi` as FS's `Work.BoseB4.BoxData`; its scaled version is
`corpusBox.chiLam ℓ x = chi (ℓ⁻¹ • x)`.

Since `chi = chiBase / √chiNormSq` and Mathlib's `ContDiffBump` `chiBase`
equals `1` on the ball of radius `1/4`, the scaled bump is identically
`(√chiNormSq)⁻¹` on the ball of radius `ℓ/4`:

  `‖x‖ < ℓ/4  →  chiLam ℓ x = (√chiNormSq)⁻¹`.

This is the "plateau" input used whenever a state is localised away from the
boundary shell of the box.
-/

open scoped Real

namespace Work.BoseBoxFock

/-- On the ball of radius `ℓ/4` the scaled corpus bump is the constant
`(√chiNormSq)⁻¹`. -/
theorem corpusChiLam_eq_of_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ‖x‖ < ℓ / 4) :
    Work.BoseK15.corpusBox.chiLam ℓ x = (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  -- `chiLam ℓ x = chi (ℓ⁻¹ • x)`
  have h1 : Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) := rfl
  -- the scaled point lies in the ball of radius `1/4`
  have hle : ‖(ℓ⁻¹ : ℝ) • x‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div]
    have hlt : ‖x‖ / ℓ < 1 / 4 := by
      rw [div_lt_iff₀ hℓ]
      linarith
    linarith
  rw [h1, Submission.BoseGases.chi,
      Submission.BoseGases.chiBase_eq_one_of_norm_le hle, one_div]

end Work.BoseBoxFock
