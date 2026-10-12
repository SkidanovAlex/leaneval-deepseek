import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.SecondOrder.fsKinCoeff_mul_abs_profHat_le_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small`

The cross symbol of the projected moving-box family form, at scale `ℓ = 1`, is

    `symD 1 F ρ = ∫_p F(‖p‖) · profHat p · profHat (ρ − p) dp`.

For the FS cut-off `F = fsKinCoeff C = [·−C]₊²` the symbol **tends to zero uniformly in the
momentum `ρ`** as the cut-off `C → ∞`:

    `∀ ε > 0, ∃ C₀ ≥ 0, ∀ C ≥ C₀, ∀ ρ, |symD 1 (fsKinCoeff C) ρ| ≤ ε.`

This is the "large cut-off kills the cross term" step of `lem:LocKinEn`.  The mechanism is a
one-step domination.  The cut-off factor `fsKinCoeff C ‖p‖` lives on the far region `‖p‖ ≥ C`, the
second profile factor decays (`ProfHatDecay`) while the *third* is merely bounded by the bump's
total mass `∫_z |χ z| dz` (`profHat_abs_le_mass`).  Hence

    `|symD 1 (fsKinCoeff C) ρ| ≤ (∫_z |χ z| dz) · ∫_p fsKinCoeff C ‖p‖ · |profHat p| dp`,

with the bound independent of `ρ`, and the `p`-integral tends to `0` as `C → ∞`
(`fsKinCoeff_mul_abs_profHat_le_all`).
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin.SecondOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- **The cross symbol `symD` at the FS cut-off vanishes uniformly in the momentum as the cut-off
grows.**  The `ρ`-independent bound is the bump mass `∫_z |χ z| dz` times the cut-off tail
`∫_p [‖p‖ − C]₊² |profHat p| dp`, which is made smaller than `ε / (∫|χ| + 1)` by taking `C`
large. -/
theorem symD_fsKinCoeff_small : ∀ ε : ℝ, 0 < ε → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C → ∀ ρ : EuclideanSpace ℝ (Fin 3), |Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ| ≤ ε := by
  intro ε hε
  set mass : ℝ := ∫ z : ℝ³, |Submission.BoseGases.chi z| with hmassdef
  have hmass_nn : 0 ≤ mass := by
    rw [hmassdef]
    exact integral_nonneg (fun z => abs_nonneg _)
  have hmass1 : 0 < mass + 1 := by linarith
  obtain ⟨C0, hC0pos, hC0⟩ :=
    fsKinCoeff_mul_abs_profHat_le_all (ε / (mass + 1)) (by positivity)
  refine ⟨C0, le_of_lt hC0pos, fun C hC ρ => ?_⟩
  have hI : MeasureTheory.Integrable
      (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|) :=
    Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat C
  have hsym : Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ
      = ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖p‖ * Work.OneBodyKin.profHat p
          * Work.OneBodyKin.profHat (ρ - p) := by
    rw [Work.OneBodyKin.symD]
    simp only [one_smul]
  rw [hsym]
  have hpt : ∀ p : ℝ³,
      |Submission.BoseGases.fsKinCoeff C ‖p‖ * Work.OneBodyKin.profHat p
          * Work.OneBodyKin.profHat (ρ - p)|
        ≤ Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| * mass := by
    intro p
    have hb : |Work.OneBodyKin.profHat (ρ - p)| ≤ mass := by
      rw [hmassdef]
      exact Work.OneBodyKin.profHat_abs_le_mass _
    rw [abs_mul, abs_mul, abs_of_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖)]
    exact mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖) (abs_nonneg _))
  calc |∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖p‖ * Work.OneBodyKin.profHat p
          * Work.OneBodyKin.profHat (ρ - p)|
      ≤ ∫ p : ℝ³, |Submission.BoseGases.fsKinCoeff C ‖p‖ * Work.OneBodyKin.profHat p
          * Work.OneBodyKin.profHat (ρ - p)| := abs_integral_le_integral_abs
    _ ≤ ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| * mass :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => abs_nonneg _))
          (hI.mul_const mass) (Filter.Eventually.of_forall hpt)
    _ = mass * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| := by
        rw [integral_mul_const, mul_comm]
    _ ≤ mass * (ε / (mass + 1)) := mul_le_mul_of_nonneg_left (hC0 C hC) hmass_nn
    _ = ε * (mass / (mass + 1)) := by ring
    _ ≤ ε * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hε.le
        rw [div_le_one hmass1]
        linarith
    _ = ε := by ring

end Work.OneBodyKin.SecondOrder
