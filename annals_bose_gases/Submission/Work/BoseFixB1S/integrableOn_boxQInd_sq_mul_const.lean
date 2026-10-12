import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- The box-projection square is `IntegrableOn` the ambient box together with the constant
factor `K`: this is `Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn` (the `L∞` argument:
on `abox N ℓ` the state is bounded by `sup |Φ|`, and the box mean of a bounded state over
`A ⊆ acube ℓ` is bounded by the same constant) followed by `Integrable.mul_const` with `K`. -/
theorem integrableOn_boxQInd_sq_mul_const {N : ℕ} {ℓ volA K : ℝ} (hℓ : 0 < ℓ) (hvol : 0 ≤ volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * K)
      (Submission.BoseGases.abox N ℓ)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) := by
  -- the sup bound of the state on the ambient box, from continuity and compactness
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hC _ (Submission.BoseGases.zero_mem_abox hℓ.le))
  -- the square is integrable on the box
  have hbase : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn (M := N) (A := A) hA
      (a := ℓ) (volA := volA) hAc (by rw [MeasureTheory.Measure.real_def]; exact hvolA)
      hΦc.measurable hC0 (fun x hx => by simpa [Real.norm_eq_abs] using hC x hx) i
  simpa [MeasureTheory.IntegrableOn] using hbase.mul_const K

end Work.BoseFixB1S
