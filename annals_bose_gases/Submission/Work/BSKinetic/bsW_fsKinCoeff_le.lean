import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BSKinetic.Decomp.bsDir_le_of_bounded_support
import Submission.Work.BSKinetic.Decomp.bsL2_le_of_bounded_support
import Submission.Work.BSKinetic.Decomp.bsW_le_L2_Dir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

/-- Box-supported a priori bound for the cutoff kinetic symbol: for a state `h` supported in the
centred box `acube ℓ` with sup bound `C` and coordinate-derivative bound `D`,
`(2π)⁻³·bsW (fsKinCoeff c) h ≤ 2c²(C²ℓ³) + 2(3 D²ℓ³)`.

Assembles the weighted Plancherel bound `bsW_le_L2_Dir` with the two box-supported a priori
estimates `bsL2_le_of_bounded_support` and `bsDir_le_of_bounded_support`. -/
theorem bsW_fsKinCoeff_le {ℓ c : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hh : ContDiff ℝ (⊤ : ENat) h) (hcs : HasCompactSupport h)
    (hzero : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube ℓ → h z = 0)
    {C D : ℝ} (hb : ∀ z : EuclideanSpace ℝ (Fin 3), |h z| ≤ C)
    (hb' : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 3)),
        |fderiv ℝ h z (Submission.BoseGases.kcStdBasis k)| ≤ D) :
    ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h
      ≤ 2 * c ^ 2 * (C ^ 2 * ℓ ^ 3) + 2 * (3 * (D ^ 2 * ℓ ^ 3)) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg (h 0)) (hb 0)
  have hD : 0 ≤ D := le_trans (abs_nonneg _) (hb' 0 0)
  have hplancherel := Work.BSKinetic.Decomp.bsW_le_L2_Dir (c := c) hh hcs
  have hL2 := Work.BSKinetic.Decomp.bsL2_le_of_bounded_support hℓ hC hb hzero
  have hDir := Work.BSKinetic.Decomp.bsDir_le_of_bounded_support hℓ hD hb' hzero
  exact le_trans hplancherel
    (add_le_add
      (mul_le_mul_of_nonneg_left hL2 (by positivity))
      (mul_le_mul_of_nonneg_left hDir (by norm_num)))

end Work.BSKinetic
