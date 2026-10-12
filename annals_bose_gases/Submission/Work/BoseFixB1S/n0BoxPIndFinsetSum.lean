import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.boxPInd_finset_sum_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0BoxPIndFinsetSum`

The box condensate projection `Pⱼ = UBBInputs8.boxPInd volA A j` (FS `eq:HBU`) is **additive
over a `Finset`-indexed family of `GoodState`s**: for a measurable family of states that is
bounded on the analysis box `abox N ℓ` and for a configuration `x` of the box,

    Pⱼ (Σ_{a∈s} Φ a) x = Σ_{a∈s} Pⱼ (Φ a) x .

This is the `GoodState`-hypothesis form of `Work.BoseFixB1S.boxPInd_finset_sum_gen`: the slot
integrability required by the general finite-sum linearity is supplied here by
`BoxPotOper.slotInt_of_bound`, which bounds the `j`-inserted state on `A ⊆ acube ℓ` by its box
bound (`GoodState`) and hence produces `IntegrableOn` over `A` (a finite-measure set).
-/

namespace Work.BoseFixB1S

set_option linter.unusedVariables false

theorem n0BoxPIndFinsetSum {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {ι : Type*} (s : Finset ι) (Φ : ι → Submission.BoseGases.X N → ℝ)
    (hΦ : ∀ a ∈ s, Work.BoseFixB1S.GoodState ℓ (Φ a)) (j : Fin N)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A j (∑ a ∈ s, Φ a) x
      = ∑ a ∈ s, Work.UBBInputs8.boxPInd volA A j (Φ a) x := by
  have hInt : ∀ a ∈ s,
      MeasureTheory.IntegrableOn (fun z => Φ a (Function.update x j z)) A MeasureTheory.volume :=
    fun a ha => slotInt_of_bound hℓ hA hAc j x hx (hΦ a ha).1 (hΦ a ha).2.choose_spec
  have hfun : (∑ a ∈ s, Φ a) = (fun y => ∑ a ∈ s, Φ a y) := by
    funext y
    rw [Finset.sum_apply]
  rw [hfun]
  exact boxPInd_finset_sum_gen volA A j x s Φ hInt

end Work.BoseFixB1S
