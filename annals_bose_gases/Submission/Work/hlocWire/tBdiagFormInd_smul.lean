import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_eq_of_mem_farSet
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_farSet_le_tBwordB
import Submission.Work.UBBInputs8.A.exists_hlow_localised_of_bounded
import Submission.Work.UBBInputs8.A.qLHSwordB_integral_u_box
import Submission.Work.UBBInputs8.A.tBLocalisationInd_const
import Submission.Work.UBBInputs8.A.tBwordBInd_const_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.hlocWire

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The FS box projection `boxQInd` is linear in the state: unrolling the definitions,
`boxQInd volA A i (c • Φ)` differs from `c • boxQInd volA A i Φ` only by pulling the scalar
out of the slot-`i` Bochner integral (`MeasureTheory.integral_const_mul`). -/
private lemma boxQInd_smul_local {N : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (c : ℝ) :
    Work.UBBInputs8.boxQInd volA A i (c • Φ) = c • Work.UBBInputs8.boxQInd volA A i Φ := by
  funext x
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Pi.smul_apply, smul_eq_mul]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The windowed `p`-mode amplitude `tBamp` is `ℂ`-linear in the state: the scalar passes
through the defining Bochner integral of the slot-`i` fibre. -/
private lemma tBamp_smul_local (χ : ℝ³ → ℝ) (p : ℝ³) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) (x : Submission.BoseGases.X N) (c : ℝ) :
    Work.SmallBoxTBWord.tBamp χ p (c • Φ) i x
      = (c : ℂ) * Work.SmallBoxTBWord.tBamp χ p Φ i x := by
  unfold Work.SmallBoxTBWord.tBamp
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Quadratic homogeneity of the FS-faithful `p`-diagonal box form.**  `tBdiagFormInd a A volA χ F Ψ` is a sum over slots of `(2π)⁻³ ∫_p F‖p‖ · (a³)⁻¹ ∫_{x∈abox N a} ‖tBamp χ p (boxQInd volA A i Ψ) i x‖²`, hence homogeneous of degree two in the state: the projection `boxQInd` and the amplitude `tBamp` are linear and the norm squared is quadratic.  This is the analogue of `Submission.BoseGases.kinWord_smul` for the Fourier-side word, and it is what makes the `bigKin` energy word scale-invariant (its covariant closure rescales a state to `abox`-norm one).  No hypotheses on `F` or `Ψ` are needed: linearity of Bochner integrals plus `‖(c:ℂ)·z‖² = c²‖z‖²`. -/
theorem tBdiagFormInd_smul (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (F : ℝ → ℝ) {N : ℕ}
    (Ψ : Submission.BoseGases.X N → ℝ) (c : ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F (c • Ψ)
      = c ^ 2 * Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ := by
  unfold Work.UBBInputs8.tBdiagFormInd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hQ : Work.UBBInputs8.boxQInd volA A i (c • Ψ)
      = c • Work.UBBInputs8.boxQInd volA A i Ψ := boxQInd_smul_local volA A i Ψ c
  rw [hQ]
  have hpt : ∀ (p : ℝ³) (x : Submission.BoseGases.X N),
      ‖Work.SmallBoxTBWord.tBamp χ p (c • Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2
        = c ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2 := by
    intro p x
    rw [tBamp_smul_local χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x c]
    rw [norm_mul, mul_pow]
    rw [show ‖(c : ℂ)‖ = |c| from RCLike.norm_ofReal c, sq_abs]
  have hOuter : (∫ p : ℝ³, F ‖p‖ * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (c • Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2))
      = c ^ 2 * ∫ p : ℝ³, F ‖p‖ * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) := by
    rw [show (fun p : ℝ³ => F ‖p‖ * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ p (c • Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2))
        = (fun p : ℝ³ => c ^ 2 * (F ‖p‖ * ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2))) from ?_]
    · exact MeasureTheory.integral_const_mul _ _
    · funext p
      have h1 : (∫ x in Submission.BoseGases.abox N a,
            ‖Work.SmallBoxTBWord.tBamp χ p (c • Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
          = c ^ 2 * ∫ x in Submission.BoseGases.abox N a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2 := by
        rw [show (fun x => ‖Work.SmallBoxTBWord.tBamp χ p (c • Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)
              = (fun x => c ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) from funext (fun x => hpt p x)]
        exact MeasureTheory.integral_const_mul _ _
      rw [h1]; ring
  rw [hOuter]
  ring

end Work.hlocWire
