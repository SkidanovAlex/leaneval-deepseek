import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1

theorem boxFlatCountZeroAe {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = MeasureTheory.volume.real A) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hS : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ = 0) :
    ∀ i : Fin N,
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Φ x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
  -- `Φ` is bounded on the (compact) box.
  have hK : IsCompact (Submission.BoseGases.abox N ℓ) :=
    Submission.BoseGases.abox_compact N hℓ
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hK hΦc.continuousOn
  have hC' : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hC x hx
  intro i
  -- `PᵢΦ` is measurable and bounded on the box, hence `(PᵢΦ)²` is integrable there.
  have hmeas : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦc.measurable
  have hbd : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hC'
  have hint : IntegrableOn (fun x => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hmeas hbd
  -- The hypothesis is the vanishing of the sum of nonnegative summands.
  have hzero :
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
        = 0 := by
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg (f := fun j : Fin N =>
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)
      (s := Finset.univ) (fun j _ => integral_nonneg (fun x => sq_nonneg _))).mp (by
        simpa [Work.BoseFixB1S.boxFlatCount] using hS)
    exact hsum i (Finset.mem_univ i)
  -- Integrability upgrades `∫ (PᵢΦ)² = 0` to the a.e. statement, and the square comes off.
  have hae : (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      =ᵐ[volume.restrict (Submission.BoseGases.abox N ℓ)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (f := fun x => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      (fun _ => sq_nonneg _) hint).mp hzero
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp (by simpa using hx)

end Work.BoseFixB1

end
