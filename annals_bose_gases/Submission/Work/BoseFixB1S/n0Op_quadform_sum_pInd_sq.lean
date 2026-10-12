import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0SpectralDefs
import Submission.Work.BoseFixB1S.n0SumAqEqX
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem n0Op_quadform_sum_pInd_sq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ, Ψ x * Work.BoseFixB1S.n0Op volA A Ψ x)
      = ∑ j : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A j Ψ x) ^ 2 := by
  classical
  -- `PⱼΨ` is measurable and bounded on the box by `C` (`Ψ` is); hence `Ψ · PⱼΨ` is integrable.
  have hPm : ∀ j : Fin N, Measurable (Work.UBBInputs8.boxPInd volA A j Ψ) :=
    fun j => measurable_boxPInd volA A hA j hΨm
  have hPb : ∀ j : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A j Ψ x| ≤ C :=
    fun j => abs_boxPInd_le hℓ hvol hA hvolA hAc j hΨb
  have hint : ∀ j : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N => Ψ x * Work.UBBInputs8.boxPInd volA A j Ψ x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    fun j => integrableOn_mul_of_bound (N := N) (ℓ := ℓ) hℓ hΨm (hPm j) hΨb (hPb j)
  -- `n₀Ψ = Σⱼ PⱼΨ`, so the integrand distributes over the finite slot sum.
  have hpoint : (fun x : Submission.BoseGases.X N =>
        Ψ x * Work.BoseFixB1S.n0Op volA A Ψ x)
      = fun x : Submission.BoseGases.X N =>
          ∑ j : Fin N, Ψ x * Work.UBBInputs8.boxPInd volA A j Ψ x := by
    funext x
    simp only [Work.BoseFixB1S.n0Op, Finset.mul_sum]
  have hIntEq : (∫ x in Submission.BoseGases.abox N ℓ, Ψ x * Work.BoseFixB1S.n0Op volA A Ψ x)
      = ∑ j : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            Ψ x * Work.UBBInputs8.boxPInd volA A j Ψ x := by
    rw [hpoint, MeasureTheory.integral_finsetSum _ (fun j _ => hint j)]
  -- Each `Pⱼ` is an orthogonal projection of `L²(abox N ℓ)`: `∫ Ψ·PⱼΨ = ∫ (PⱼΨ)²`.
  rw [hIntEq]
  exact Finset.sum_congr rfl (fun j _ =>
    (n0Sum_pInd_sq_selfMul (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc j
      hΨm hΨb).symm)

end Work.BoseFixB1S
