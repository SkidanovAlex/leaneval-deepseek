import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem n0ZeroOffPIndPresB1 {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x : Submission.BoseGases.X N, x i ∉ A → Ψ x = 0) :
    ∀ j : Fin N, ∀ x : Submission.BoseGases.X N, x i ∉ A →
      Work.UBBInputs8.boxPInd volA A j Ψ x = 0 := by
  intro j x hx
  rw [Work.UBBInputs8.boxPInd]
  by_cases hji : j = i
  · -- the box indicator in slot `j = i` vanishes at `x`
    have hxj : x j ∉ A := by rwa [hji]
    rw [Set.indicator_of_notMem hxj, mul_zero]
  · -- the integral kills the other factor: at every `z ∈ A` the configuration
    -- `update x j z` still has `i`-th coordinate `x i ∉ A`
    have hint : (∫ z in A, Ψ (Function.update x j z)) = 0 := by
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun z _ => ?_
      refine hΨ (Function.update x j z) ?_
      have hupd : (Function.update x j z) i = x i := by
        simp [Function.update, show i ≠ j from fun h => hji h.symm]
      rw [hupd]
      exact hx
    rw [hint]
    simp

end Work.BoseFixB1S
