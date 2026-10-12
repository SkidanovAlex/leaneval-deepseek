import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKinDefs` — the vocabulary of the identity `sqrtKin_diffForm`

Target (FS's identification of `‖p‖` with the Riesz kernel `‖x−y‖^{-4}`):

`(2π)^{-3}∫_p ‖p‖‖kinFT g p‖² = (2π²)^{-1}∬ ‖x−y‖^{-4}‖g x − g y‖²`.

Writing `f = kinFT g` (the corpus's `p`-convention Fourier transform) and

* `kinMass g = (2π)^{-3}∫_p ‖f p‖²` (the mass; `= ∫‖g‖²` by Plancherel),
* `kinFirst g = (2π)^{-3}∫_p ‖p‖‖f p‖²` (**the left-hand side** of the target),
* `kinHeat g t = (2π)^{-3}∫_p e^{-t‖p‖²}‖f p‖²` (the heat-regularised mass),
* `diffHeat g t = ∬ heatK t (x−y)‖g x − g y‖²`,
* `diffKernel g = ∬ ‖x−y‖^{-4}‖g x − g y‖²` (**the right-hand side** core),

the proof has three pieces:

1. *(subordination, `t`–`p` Tonelli)* `∫_0^∞ t^{-3/2}(kinMass g − kinHeat g t)dt = 2√π·kinFirst g`;
2. *(heat pairing)* for `t > 0`, `kinMass g − kinHeat g t = ⅟₂·diffHeat g t`;
3. *(radial kernel integral + Tonelli)*
   `∫_0^∞ t^{-3/2}diffHeat g t dt = 2π^{-3/2}·diffKernel g`.

The constants then combine: `(2√π)^{-1}·⅟₂·2π^{-3/2} = (2π²)^{-1}`.

The definitions of this file are deliberately elementary (no `sorry`, no heavy imports) so that
the several independent lemmas about them can be proved in parallel.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The heat kernel in the corpus's `p`-convention**:
`heatK t z = (4πt)^{-3/2} exp(−‖z‖²/(4t))`, i.e. the inverse `p`-Fourier transform of the
Gaussian symbol `p ↦ e^{−t‖p‖²}` (in the normalisation `(2π)^{-3}∫_p e^{i⟪p,z⟫}·e^{−t‖p‖²}dp`). -/
noncomputable def heatK (t : ℝ) (z : ℝ³) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))

/-- The (Plancherel) mass `kinMass g = (2π)^{-3}∫_p ‖kinFT g p‖² = ∫_x ‖g x‖²`. -/
noncomputable def kinMass (g : ℝ³ → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- **The left-hand side of the target**: `(2π)^{-3}∫_p ‖p‖‖kinFT g p‖²`. -/
noncomputable def kinFirst (g : ℝ³ → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The heat-regularised mass `kinHeat g t = (2π)^{-3}∫_p e^{−t‖p‖²}‖kinFT g p‖²`. -/
noncomputable def kinHeat (g : ℝ³ → ℂ) (t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The heat-regularised difference form `diffHeat g t = ∬ heatK t (x−y)‖g x − g y‖²`. -/
noncomputable def diffHeat (g : ℝ³ → ℂ) (t : ℝ) : ℝ :=
  ∫ x : ℝ³, ∫ y : ℝ³, heatK t (x - y) * ‖g x - g y‖ ^ 2

/-- **The right-hand side core of the target**: `∬ ‖x−y‖^{−4}‖g x − g y‖²`. -/
noncomputable def diffKernel (g : ℝ³ → ℂ) : ℝ :=
  ∫ x : ℝ³, ∫ y : ℝ³, ‖x - y‖ ^ (-(4 : ℝ)) * ‖g x - g y‖ ^ 2

/-! ## Elementary facts about `heatK` -/

lemma heatK_nonneg {t : ℝ} (ht : 0 ≤ t) (z : ℝ³) : 0 ≤ heatK t z := by
  unfold heatK
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

lemma heatK_even (t : ℝ) (z : ℝ³) : heatK t (-z) = heatK t z := by
  simp [heatK]

lemma heatK_pos {t : ℝ} (ht : 0 < t) (z : ℝ³) : 0 < heatK t z := by
  unfold heatK
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

lemma heatK_continuous {t : ℝ} (ht : 0 < t) : Continuous fun z : ℝ³ => heatK t z := by
  unfold heatK
  have h1 : Continuous fun z : ℝ³ => ‖z‖ ^ 2 := continuous_norm.pow 2
  exact Continuous.mul continuous_const
    (Real.continuous_exp.comp (h1.div_const (4 * t)).neg)

end Work.BoseBoxFock
