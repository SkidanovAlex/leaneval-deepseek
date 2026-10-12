import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.Sector

open MeasureTheory

/-- **Self-adjointness of `Qᵢ = 1 − Pᵢ` over the centred box.**

Since `aQ ℓ i Φ = Φ − aP ℓ i Φ` and the box mean `aP ℓ i` is self-adjoint over
`abox N ℓ` (`Submission.BoseGases.aP_sym_box`), the complement is self-adjoint
as well.  This is the `aQ`-analogue of `aP_sym_box`, used to move the slot
operator `Qᵢ` from one factor of the box pairing to the other. -/
theorem aQ_sym_box {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) : (∫ x in Submission.BoseGases.abox N ℓ, Submission.BoseGases.aQ ℓ i Φ x * Ψ x) = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Submission.BoseGases.aQ ℓ i Ψ x := by
  have h1 : Integrable (fun x : Submission.BoseGases.X N => Φ x * Ψ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hΦ.mul hΨ)
  have h2 : Integrable
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i Φ x * Ψ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    (Submission.BoseGases.integrableOn_mul_aP hℓ i hΨ hΦ).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have h3 : Integrable
      (fun x : Submission.BoseGases.X N => Φ x * Submission.BoseGases.aP ℓ i Ψ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.integrableOn_mul_aP hℓ i hΦ hΨ
  calc
    (∫ x in Submission.BoseGases.abox N ℓ, Submission.BoseGases.aQ ℓ i Φ x * Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x * Ψ x - Submission.BoseGases.aP ℓ i Φ x * Ψ x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp only [Submission.BoseGases.aQ]
          ring
    _ = (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Ψ x)
          - (∫ x in Submission.BoseGases.abox N ℓ, Submission.BoseGases.aP ℓ i Φ x * Ψ x) :=
          MeasureTheory.integral_sub h1 h2
    _ = (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Ψ x)
          - (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Submission.BoseGases.aP ℓ i Ψ x) := by
          rw [Submission.BoseGases.aP_sym_box hℓ i hΦ hΨ]
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x * Ψ x - Φ x * Submission.BoseGases.aP ℓ i Ψ x) :=
          (MeasureTheory.integral_sub h1 h3).symm
    _ = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Submission.BoseGases.aQ ℓ i Ψ x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp only [Submission.BoseGases.aQ]
          ring

end Work.BoseFixB2.Sector
