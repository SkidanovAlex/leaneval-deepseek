import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- Scaling of a set integral of a product of two `t`-multiples: pulling the two scalars out of
the integrand.  (`MeasureTheory.integral_const_mul` applied after the pointwise identity
`(t·F)·(t·G)·W = t²·(F·G·W)`.) -/
private lemma setIntegral_sq_scale {N : ℕ} (t : ℝ) (s : Set (Submission.BoseGases.X N))
    (F G W : Submission.BoseGases.X N → ℝ) :
    (∫ x in s, (t * F x) * (t * G x) * W x) = t^2 * ∫ x in s, F x * G x * W x := by
  have h : (fun x => (t * F x) * (t * G x) * W x) = fun x => t^2 * (F x * G x * W x) := by
    funext x; ring
  rw [h, MeasureTheory.integral_const_mul]

/-- **`boxA2` is homogeneous of degree two.**  Each of the two box-projections `P` and each of the
two box-projections `Q` in the integrand of `Work.BoseFixB1.boxA2` is linear in the state
(`Work.hlocWire.boxPInd_smul`, `Work.hlocWire.boxQInd_smul`), so the integrand picks up `t·t` and
the sum over pairs and the integral — both linear — carry the factor out. -/
theorem boxA2ScaleB1 {N : ℕ} (ℓ volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.BoseFixB1.boxA2 ℓ volA A w1 (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1.boxA2 ℓ volA A w1 Φ := by
  have hfun : (fun x => t * Φ x) = t • Φ := by
    funext x; simp [Pi.smul_apply]
  rw [hfun]
  unfold Work.BoseFixB1.boxA2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 (t • Φ))
      = t • Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) by
    rw [Work.hlocWire.boxPInd_smul volA A p.2 Φ t,
      Work.hlocWire.boxPInd_smul volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) t]]
  rw [show Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 (t • Φ))
      = t • Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) by
    rw [Work.hlocWire.boxQInd_smul volA A p.1 Φ t,
      Work.hlocWire.boxQInd_smul volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) t]]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact setIntegral_sq_scale t (Submission.BoseGases.abox N ℓ) _ _ _

end Work.BoseFixB1S
