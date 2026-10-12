import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat
import Submission.Work.OneBodyKin.symD_fsKinCoeff_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.symD_value_bound`

The cross symbol `symD 1 (fsKinCoeff C) ρ` at box size `1` and FS cut-off `fsKinCoeff C = [·−C]₊²`
is dominated by the product of the bump mass and the `|profHat|`-weighted mass:

    `|symD 1 (fsKinCoeff C) ρ| ≤ (∫_z |χ z|) · (∫_p [‖p‖−C]₊² · |profHat p|)`.

The mechanism is the elementary `L¹ → L^∞` bound `|profHat q| ≤ ∫_z |χ z|`
(`Work.OneBodyKin.profHat_abs_le_mass`) applied to the *second* factor, whose argument `ρ − p`
carries the momentum shift; the first factor's sign is dropped with `fsKinCoeff_nonneg`.  No decay
of `profHat` is needed (only the integrability of the weighted mass,
`Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat`).

This is the *value* (as opposed to second-order) estimate on the cross symbol: it is unchanged if
`symD` is shifted, and it is what makes the near-region decomposition of the two-regime symbol
bound uniform in `ρ`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Tprime

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 400000

theorem symD_value_bound (C : ℝ) (ρ : EuclideanSpace ℝ (Fin 3)) :
    |Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ|
      ≤ (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.chi z|)
        * (∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|) := by
  -- notation: the bump mass `M` and the weighted profile `g`
  set M : ℝ := ∫ z : ℝ³, |Submission.BoseGases.chi z| with hM
  set g : ℝ³ → ℝ := fun p => Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|
    with hg
  set I : ℝ³ → ℝ := fun p =>
    Submission.BoseGases.fsKinCoeff C ‖p‖ * Work.OneBodyKin.profHat p *
      Work.OneBodyKin.profHat (ρ - p) with hI
  have hM0 : 0 ≤ M := by
    rw [hM]; exact integral_nonneg (fun z => abs_nonneg _)
  have hgint : MeasureTheory.Integrable g := by
    rw [hg]; exact Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat C
  have hsym : Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ = ∫ p : ℝ³, I p := by
    rw [hI]
    simp only [Work.OneBodyKin.symD, one_smul]
  -- pointwise domination: the second profile factor is bounded by the bump mass
  have hdom : ∀ p : ℝ³, ‖I p‖ ≤ M * g p := by
    intro p
    have hfs : 0 ≤ Submission.BoseGases.fsKinCoeff C ‖p‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖
    have h1 : |Work.OneBodyKin.profHat (ρ - p)| ≤ M := by
      rw [hM]; exact Work.OneBodyKin.profHat_abs_le_mass (ρ - p)
    have hIv : I p = Submission.BoseGases.fsKinCoeff C ‖p‖ * Work.OneBodyKin.profHat p *
        Work.OneBodyKin.profHat (ρ - p) := by rw [hI]
    have hgv : g p = Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| := by
      rw [hg]
    rw [hIv, hgv, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hfs]
    calc Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| *
          |Work.OneBodyKin.profHat (ρ - p)|
        ≤ Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p| * M :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M * (Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|) := by
          ring
  calc |Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ|
      = ‖∫ p : ℝ³, I p‖ := by rw [hsym, Real.norm_eq_abs]
    _ ≤ ∫ p : ℝ³, ‖I p‖ := norm_integral_le_integral_norm (μ := volume) I
    _ ≤ ∫ p : ℝ³, M * g p :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => norm_nonneg _))
          (hgint.const_mul M) (Filter.Eventually.of_forall hdom)
    _ = M * ∫ p : ℝ³, g p := integral_const_mul M g
    _ = M * (∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|) := by
        rw [hg]

end Work.BoseKinLoc.Tprime
