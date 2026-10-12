import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chi_sq_bounds
import Submission.Work.BoseFixR.FarKernelRowsB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sum_hatChiSq_sq_le` — the Parseval/Bessel bound `∑_k χ̂²(p_k)² ≤ 48/π`

For the corpus localization bump `χ = Submission.BoseGases.chi` (the smooth cubic bump,
`∫ χ² = 1`, supported in the ball of radius `1/2`) and the label cube
`Lab N = (ZMod (2N+1))³` with lattice momenta `p_k = vec (labVec N k) = 2π·(centred label)`,
the sum of the squared Fourier coefficients `χ̂²(p) = ∫ χ²(x) cos⟨p,x⟩` of `χ²` over the
labels is at most `48/π`.

## The argument

By the Bessel bound for the cosine system of the unit cell (`Work.BoseFixR.BesselUnitCell`,
the Hilbert-space core also used by `sum_hatChi_sq_le` with `g = χ`), applied to the
*nonnegative* function `g = χ²`:

    ∑_k χ̂²(p_k)² ≤ ∫_{cell} g² = ∫ χ⁴,

because `χ̂²(p) = ∫_{cell} χ² cos⟨p,·⟩` is the set-integral form of the full-space defining
integral (`Work.BoseFixR.unitCell_chiSq_cos`, `χ` vanishing off the cell).  The remaining
numeric input is the *supremum* bound `χ(x)² ≤ 48/π` (`chi_sq_bounds`, whose constant is
`1/chiNormSq ≤ 48/π`, the “sharp-χ” fact of the corpus normalisation): pointwise
`χ⁴ = χ²·χ² ≤ (48/π)·χ²`, and `∫_{cell} χ² = 1`
(`integral_unitCell_chi_sq`), so `∫ χ⁴ ≤ 48/π`.

This is the constant `Cn` of the Bessel conjunct of the honest §10 interface (`RViewFS`),
consumed by `Work.BoseBoxFock.bessel_honest` and `viewFS_of_gate`.
-/

namespace Work.BoseBoxFock

/-- **The numeric input.**  `∫_{cell} χ⁴ ≤ 48/π`, from the pointwise bound
`χ(x)² ≤ 48/π` (`chi_sq_bounds`) and the normalisation `∫_{cell} χ² = 1`. -/
theorem unitCell_chi_pow4_le_48 :
    (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4) ≤ 48 / Real.pi := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chi x) ^ 4
      ≤ (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 := by
    intro x
    have h : (Submission.BoseGases.chi x) ^ 2 ≤ 48 / Real.pi := chi_sq_bounds.2 x
    calc (Submission.BoseGases.chi x) ^ 4
        = (Submission.BoseGases.chi x) ^ 2 * (Submission.BoseGases.chi x) ^ 2 := by ring
      _ ≤ (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 :=
          mul_le_mul_of_nonneg_right h (sq_nonneg _)
  have hmono : (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4)
      ≤ ∫ x in Work.BoseB4.unitCell, (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 :=
    MeasureTheory.setIntegral_mono_ae
      ((Submission.BoseGases.chi_continuous.pow 4).continuousOn.integrableOn_compact
        Work.BoseB4.isCompact_unitCell)
      ((continuous_const.mul (Submission.BoseGases.chi_continuous.pow 2)).continuousOn.integrableOn_compact
        Work.BoseB4.isCompact_unitCell)
      (Filter.Eventually.of_forall hpt)
  calc (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4)
      ≤ ∫ x in Work.BoseB4.unitCell, (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 :=
        hmono
    _ = (48 / Real.pi) * ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2 :=
        MeasureTheory.integral_const_mul _ _
    _ = 48 / Real.pi := by rw [integral_unitCell_chi_sq]; ring

theorem sum_hatChiSq_sq_le (N : ℕ) :
    ∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (Work.BoseBoxFock.labVec N k))) ^ 2
      ≤ 48 / Real.pi := by
  -- the defining Fourier integral of `χ̂²` may be taken over the unit cell
  have hconv : (∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      = ∑ k : Work.BoseBoxFock.Lab N,
          (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Work.BoseFixR.unitCell_chiSq_cos]
  calc (∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      = ∑ k : Work.BoseBoxFock.Lab N,
          (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2 := hconv
    _ ≤ ∫ x in Work.BoseB4.unitCell, ((Submission.BoseGases.chi x) ^ 2) ^ 2 :=
        Work.BoseFixR.BesselUnitCell N (fun x => (Submission.BoseGases.chi x) ^ 2)
          (Submission.BoseGases.chi_continuous.pow 2)
    _ = ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4 := by
        apply MeasureTheory.setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
        intro x _
        ring
    _ ≤ 48 / Real.pi := unitCell_chi_pow4_le_48

end Work.BoseBoxFock
