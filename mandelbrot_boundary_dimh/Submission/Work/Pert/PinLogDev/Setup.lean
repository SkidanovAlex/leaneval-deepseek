import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.F0f_eq_model
import Submission.Work.Pert.Ksub2.defect_le_fix
import Submission.Work.Pert.Ksub2.liftF_sub_model_le_pointwise
import Submission.Work.Pert.LiftExp.liftF_sub_translation_le_explicit
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.PinLogDev.Setup`

The language layer for the *logarithmic* deviation bound of the pinned gate coordinate
(`Work.Pert.PinLogDev.anchor_dev_le`).

The pinned coordinate `Φ` of the perturbed lift `F = liftF u σ α` on the gate `Qm Ξ α` satisfies,
along a legal walk, the **exact** difference equation

  `D (F z) - D z = -(F z - (z + 1))`,  `D := Φ - id`,

whose right-hand side is the *defect* `deltaF u σ α`.  The two objects studied here are

* `deltaF u σ α z = liftF u σ α z - (z + 1)`, and
* `modelA hF = 1 - deriv hF 0`, the coefficient of `τ_f` in the defect, where
  `f₀ z = z + z² * hF z` is the model germ of `f₀` (`Work.Pert.Ksub2.exists_model_data`).

The mathematical content of the deviation bound is that the *exact* antiderivative

  `τ_f = σ - (σ / (2πiα)) · (d/dw) log (1 - exp (-2πiα w))`

makes the leading `A/τ`-part of the deviation computable in closed form, so that the logarithmic
divergences of the pin and of the path integral cancel *exactly*; what is left is controlled by the
integrability of `‖τ_f‖²` on the two legs of the path (a "spike" estimate at the lattice `ℤ/α`).
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-- The defect `δ_f = F_f - (id + 1)` of the perturbed lift. -/
def deltaF (u : ℂ → ℂ) (σ α : ℂ) : ℂ → ℂ := fun w => liftF u σ α w - (w + 1)

/-- `δ_f z = liftF u σ α z - (z+1)`. -/
theorem deltaF_apply (u : ℂ → ℂ) (σ α w : ℂ) :
    deltaF u σ α w = liftF u σ α w - (w + 1) := rfl

/-- The coefficient `A = 1 - hF'(0)` of the model defect. -/
def modelA (hF : ℂ → ℂ) : ℂ := 1 - deriv hF 0

/-- The model defect function `t ↦ hF t / (1 + t hF t) - 1` (the defect of the limit model
`F0f f₀`, read in the coordinate `t`). -/
def modelDelta (hF : ℂ → ℂ) : ℂ → ℂ := fun t => hF t / (1 + t * hF t) - 1

/-- The explicit (a priori) solution of the difference equation: on the gate the defect is
`δ z = δ (z - 1)`-periodic… in particular `δ (z + 1/α) = δ z`. -/
theorem deltaF_add_period (u : ℂ → ℂ) (σ α w : ℂ) (hα : α ≠ 0) :
    deltaF u σ α (w + 1 / α) = deltaF u σ α w := by
  unfold deltaF
  have h := liftF_sub_period u σ α (w + 1 / α) hα
  simp only [add_sub_cancel_right] at h
  rw [h]; ring

/-- The `τ_f`-difference quotient: `τ_f (z + 1/α) = τ_f z`. -/
theorem tauC_add_period' (σ α w : ℂ) (hα : α ≠ 0) :
    tauC σ α (w + 1 / α) = tauC σ α w := tauC_add_period σ α w hα

end

end Work.Pert.PinLogDev
