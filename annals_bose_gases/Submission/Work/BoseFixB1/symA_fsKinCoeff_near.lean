import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.symA_fsKinCoeff_near` — the *near*-regime monotonicity of the unprojected symbol

The unprojected symbol of the moving-box family at scale `ℓ = 1` is

    `symA 1 F ρ = (2π)⁻³ ∫_p F ‖ρ + p‖ · profHat(p)² dp`

(`Work.OneBodyKin.Defs`), and the FS cut-off is `fsKinCoeff c r = [r − c]₊²`.  The claim

    `symA 1 (fsKinCoeff C) ρ ≤ symA 1 (fsKinCoeff (C − ‖ρ‖)) 0`

says exactly that *lowering the cut-off by the momentum `‖ρ‖` and evaluating at `ρ` is no worse
than the radial symbol at the origin with that lowered cut-off*.  It is the pointwise
(near-regime) input of the two-regime decomposition of the kinetic symbol, and — unlike
`symA_far_sharp`/`symA_fsKinCoeff_far_le` — it needs **no** hypothesis on `‖ρ‖` versus `C`.

## The mechanism

Everything is the single elementary scalar inequality: for `ρ, p : ℝ³`,

    `[‖ρ+p‖ − C]₊² ≤ [‖p‖ − (C − ‖ρ‖)]₊²`,

because `‖ρ+p‖ ≤ ‖ρ‖ + ‖p‖` gives `‖ρ+p‖ − C ≤ ‖p‖ − (C − ‖ρ‖)` and `r ↦ r₊²` is monotone.
Multiplying by the nonnegative weight `profHat(p)² ≥ 0` and integrating the pointwise inequality
(`integral_mono`) yields the statement, since both integrands are integrable
(`integrable_fsKinCoeff_shift_mul_profHat_sq`) and `symA 1 F 0` unfolds to
`(2π)⁻³ ∫_p F ‖p‖ profHat(p)² dp`.
-/

namespace Work.BoseFixB1

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
-- the hypothesis `hC : 0 ≤ C` is part of the requested statement but not needed by the proof
set_option linter.unusedVariables false

/-- **The shift only costs `‖ρ‖` in the cut-off.**  Since `‖ρ+p‖ ≤ ‖ρ‖ + ‖p‖`, the excess of
`‖ρ+p‖` over `C` is at most the excess of `‖p‖` over `C − ‖ρ‖`:
`[‖ρ+p‖−C]₊ ≤ [‖p‖−(C−‖ρ‖)]₊`, and squaring preserves the inequality (both sides are
nonnegative). -/
lemma fsKinCoeff_shift_le (C : ℝ) (ρ p : ℝ³) :
    Submission.BoseGases.fsKinCoeff C ‖ρ + p‖
      ≤ Submission.BoseGases.fsKinCoeff (C - ‖ρ‖) ‖p‖ := by
  have h1 : ‖ρ + p‖ - C ≤ ‖p‖ - (C - ‖ρ‖) := by
    have h := norm_add_le ρ p
    linarith
  have h2 : max (‖ρ + p‖ - C) 0 ≤ max (‖p‖ - (C - ‖ρ‖)) 0 :=
    max_le (h1.trans (le_max_left _ _)) (le_max_right _ _)
  exact pow_le_pow_left₀ (le_max_right _ _) h2 2

/-- **The cut-off weight at the *reduced* cut-off is integrable.**  This is
`integrable_fsKinCoeff_shift_mul_profHat_sq` at shift `0`, made syntactically literal for the
integration argument below. -/
private lemma integrable_fsKinCoeff_reduced (C : ℝ) (ρ : ℝ³) :
    Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff (C - ‖ρ‖) ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2) := by
  simpa using
    Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq (C - ‖ρ‖) (0 : ℝ³)

/-- **The near-regime bound on the unprojected symbol.**  For every cut-off `C ≥ 0` and every
momentum `ρ`, the symbol at `ρ` with cut-off `C` is dominated by the symbol at the origin with
cut-off `C − ‖ρ‖`. -/
theorem symA_fsKinCoeff_near {C : ℝ} (hC : 0 ≤ C) (ρ : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      ≤ Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (C - ‖ρ‖)) 0 := by
  have hpt : ∀ p : ℝ³,
      Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (Work.OneBodyKin.profHat p) ^ 2
        ≤ Submission.BoseGases.fsKinCoeff (C - ‖ρ‖) ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 :=
    fun p => mul_le_mul_of_nonneg_right (fsKinCoeff_shift_le C ρ p) (sq_nonneg _)
  have hmono : (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ *
        (Work.OneBodyKin.profHat p) ^ 2)
      ≤ ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff (C - ‖ρ‖) ‖p‖ *
        (Work.OneBodyKin.profHat p) ^ 2 :=
    integral_mono (Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq C ρ)
      (integrable_fsKinCoeff_reduced C ρ) hpt
  have hA : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ *
          (Work.OneBodyKin.profHat p) ^ 2 := by
    rw [Work.OneBodyKin.symA]
    simp
  have hB : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (C - ‖ρ‖)) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff (C - ‖ρ‖) ‖p‖ *
          (Work.OneBodyKin.profHat p) ^ 2 := by
    rw [Work.OneBodyKin.symA]
    simp
  rw [hA, hB]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

end Work.BoseFixB1
