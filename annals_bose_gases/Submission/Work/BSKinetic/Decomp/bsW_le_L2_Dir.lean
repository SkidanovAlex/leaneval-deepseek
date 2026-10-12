import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BSKinetic.kinFT_energy_sum
import Submission.Work.BSKinetic.plancherel_pconv
import Submission.Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weighted Plancherel bound for the cutoff kinetic symbol

`(2π)⁻³⟨ψ, [√−Δ − c]₊² ψ⟩ ≤ 2c²‖ψ‖² + 2‖∇ψ‖²`.

The symbol bound `[r−c]₊² ≤ 2r² + 2c²` turns the `F`-weighted `p`-space norm² `bsW` into the
`L²` mass `bsL2` (unweighted Plancherel, `plancherel_pconv`) plus the Dirichlet word `bsDir`
(weighted Plancherel, `kinFT_energy_sum`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The elementary symbol bound `[r − c]₊² ≤ 2r² + 2c²`. -/
lemma fsKinCoeff_le_two_mul (c r : ℝ) :
    Submission.BoseGases.fsKinCoeff c r ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have h1 : max (r - c) 0 ≤ |r - c| := max_le (le_abs_self _) (abs_nonneg _)
  have h2 : (max (r - c) 0) ^ 2 ≤ (r - c) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (le_max_right _ 0)]
    exact h1
  have h3 : (r - c) ^ 2 ≤ 2 * r ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (r + c)]
  linarith

theorem bsW_le_L2_Dir {c : ℝ} {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hh : ContDiff ℝ (⊤ : ENat) h) (hcs : HasCompactSupport h) :
    ((2 * Real.pi) ^ 3)⁻¹
        * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h
      ≤ 2 * c ^ 2 * Work.BSKinetic.Decomp.bsL2 h
        + 2 * Work.BSKinetic.Decomp.bsDir h := by
  have hpre : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  have hKint : Integrable (fun p : ℝ³ =>
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq h hh hcs
  have hK2int : Integrable (fun p : ℝ³ =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt h hh hcs
  -- integrability of the dominating integrand
  have hGint : Integrable (fun p : ℝ³ =>
      (2 * ‖p‖ ^ 2 + 2 * c ^ 2)
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
    have h1 : Integrable (fun p : ℝ³ =>
        2 * (‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)) :=
      hK2int.const_mul 2
    have h2 : Integrable (fun p : ℝ³ =>
        (2 * c ^ 2) * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
      hKint.const_mul (2 * c ^ 2)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    ring
  -- the pointwise symbol bound passes to the integral
  have hmono : (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      ≤ ∫ p : ℝ³, (2 * ‖p‖ ^ 2 + 2 * c ^ 2)
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by
    refine integral_mono_of_nonneg ?_ hGint ?_
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)
    · exact Filter.Eventually.of_forall fun p =>
        mul_le_mul_of_nonneg_right (fsKinCoeff_le_two_mul c ‖p‖) (sq_nonneg _)
  -- linearity of the dominating integral
  have hsplit : (∫ p : ℝ³, (2 * ‖p‖ ^ 2 + 2 * c ^ 2)
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      = 2 * (∫ p : ℝ³, ‖p‖ ^ 2
            * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
        + 2 * c ^ 2 * (∫ p : ℝ³,
            ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
    have hpt : (fun p : ℝ³ => (2 * ‖p‖ ^ 2 + 2 * c ^ 2)
          * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
        = fun p : ℝ³ => 2 * (‖p‖ ^ 2
              * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
            + (2 * c ^ 2) * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by
      funext p
      ring
    rw [hpt, integral_add (hK2int.const_mul 2) (hKint.const_mul (2 * c ^ 2)),
      integral_const_mul, integral_const_mul]
  -- the two Plancherel identities
  have hdir := Work.BSKinetic.kinFT_energy_sum h hh hcs
  have hl2 := Work.BSKinetic.plancherel_pconv h hh hcs
  calc ((2 * Real.pi) ^ 3)⁻¹
        * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖
          * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := rfl
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, (2 * ‖p‖ ^ 2 + 2 * c ^ 2)
          * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hmono hpre
    _ = 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2
            * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
          + 2 * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
              ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
        rw [hsplit]; ring
    _ = 2 * Work.BSKinetic.Decomp.bsDir h + 2 * c ^ 2 * Work.BSKinetic.Decomp.bsL2 h := by
        rw [hdir, hl2]
        simp only [Work.BSKinetic.Decomp.bsDir, Work.BSKinetic.Decomp.bsL2]
    _ = 2 * c ^ 2 * Work.BSKinetic.Decomp.bsL2 h
          + 2 * Work.BSKinetic.Decomp.bsDir h := by ring

end Work.BSKinetic.Decomp
