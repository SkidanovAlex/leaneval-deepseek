import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxQCount_eq_sum_compT
import Submission.Work.BoseFixB1S.BoxFlatAux
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

theorem hopQIndDecomp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (i : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A i Φ x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  -- resolution of unity, pointwise on the analysis box
  have hsum : ∀ y ∈ abox N ℓ,
      Φ y = ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y :=
    fun y hy => (boxCompT_sum_eq hℓ hvol hA hvolA hAc hΦc y hy).symm
  -- `Qᵢ` only reads the box values of its argument
  have h1 : UBBInputs8.boxQInd volA A i Φ x
      = UBBInputs8.boxQInd volA A i
          (fun y => ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y) x :=
    agreeBox_boxQInd hA hAc i hsum x hx
  -- additivity of `Qᵢ` over the finite sum
  have h2 : UBBInputs8.boxQInd volA A i
        (fun y => ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y) x
      = ∑ p ∈ disjPairs N,
          UBBInputs8.boxQInd volA A i (boxCompT volA A p.1 p.2 Φ) x :=
    boxQInd_finset_sum_gen volA A i x (disjPairs N)
      (fun p => boxCompT volA A p.1 p.2 Φ)
      (fun p _ => slotInt_of_bound hℓ hA hAc i x hx (hG p).1 (hG p).2.choose_spec)
  -- the eigenvalue rule `Qᵢψ_p = [i ∈ p.2]·ψ_p`, turned into a filtered sum
  have h3 : (∑ p ∈ disjPairs N,
        UBBInputs8.boxQInd volA A i (boxCompT volA A p.1 p.2 Φ) x)
      = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.2),
          boxCompT volA A p.1 p.2 Φ x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p hp =>
      boxQInd_boxCompT hℓ hvol hA hvolA hAc (mem_disjPairs.mp hp) hΦc i x hx)
  rw [h1, h2, h3]

end Work.BoseFixB1S

end
