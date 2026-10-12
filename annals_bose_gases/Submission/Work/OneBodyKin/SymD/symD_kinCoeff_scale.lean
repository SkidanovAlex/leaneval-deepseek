import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SymD.symD_kinCoeff_scale`

The dilation covariance of the cross symbol `Work.OneBodyKin.symD` with the FS cut-off
`fsKinCoeff c = [·−c]₊²`:

    `symD 1 (fsKinCoeff (c·ℓ)) (ℓ q) = ℓ⁵ · symD ℓ (fsKinCoeff c) q`   (`ℓ > 0`).

`symD ℓ F q = ∫_p F ‖p‖ · profHat (ℓ p) · profHat (ℓ (q − p)) dp`, so substituting
`p = ℓ s` (volume factor `ℓ³`) turns the integrand into
`F_{cℓ}(ℓ ‖s‖) · profHat (ℓ s) · profHat (ℓ (q − s))`, and the coefficient identity
`[ℓ r − c ℓ]₊² = ℓ² [r − c]₊²` supplies the remaining `ℓ²`.  The total power is `ℓ⁵`.
-/

namespace Work.OneBodyKin.SymD

theorem symD_kinCoeff_scale {ℓ c : ℝ} (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff (c * ℓ)) (ℓ • q)
      = ℓ ^ 5 * Work.OneBodyKin.symD ℓ (Submission.BoseGases.fsKinCoeff c) q := by
  -- the coefficient identity `[ℓ·r − c·ℓ]₊² = ℓ²·[r − c]₊²`
  have hfs : ∀ r : ℝ, Submission.BoseGases.fsKinCoeff (c * ℓ) (ℓ * r)
      = ℓ ^ 2 * Submission.BoseGases.fsKinCoeff c r := by
    intro r
    unfold Submission.BoseGases.fsKinCoeff
    rw [show ℓ * r - c * ℓ = ℓ * (r - c) from by ring]
    have hm : max (ℓ * (r - c)) 0 = ℓ * max (r - c) 0 := by
      rw [mul_max_of_nonneg (r - c) 0 hℓ.le, mul_zero]
    rw [hm]; ring
  unfold Work.OneBodyKin.symD
  -- the dilation substitution `p ↦ ℓ • s` (volume factor `ℓ³`)
  have hsub := Submission.BoseGases.integral_comp_smul_right
    (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff (c * ℓ) ‖p‖ * Work.OneBodyKin.profHat ((1:ℝ) • p) *
        Work.OneBodyKin.profHat ((1:ℝ) • (ℓ • q - p))) hℓ
  rw [hsub]
  -- the substituted integrand is `ℓ²` times the target integrand
  have hpoint : ∀ s : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff (c * ℓ) ‖ℓ • s‖ * Work.OneBodyKin.profHat ((1:ℝ) • (ℓ • s)) *
        Work.OneBodyKin.profHat ((1:ℝ) • (ℓ • q - ℓ • s))
      = ℓ ^ 2 * (Submission.BoseGases.fsKinCoeff c ‖s‖ * Work.OneBodyKin.profHat (ℓ • s) *
        Work.OneBodyKin.profHat (ℓ • (q - s))) := by
    intro s
    simp only [one_smul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, hfs ‖s‖, ← smul_sub]
    ring
  rw [show (∫ s : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff (c * ℓ) ‖ℓ • s‖ * Work.OneBodyKin.profHat ((1:ℝ) • (ℓ • s)) *
          Work.OneBodyKin.profHat ((1:ℝ) • (ℓ • q - ℓ • s)))
      = ∫ s : EuclideanSpace ℝ (Fin 3), ℓ ^ 2 * (Submission.BoseGases.fsKinCoeff c ‖s‖ *
          Work.OneBodyKin.profHat (ℓ • s) * Work.OneBodyKin.profHat (ℓ • (q - s)))
      from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_const_mul]
  ring

end Work.OneBodyKin.SymD
