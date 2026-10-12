import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPInd_self_idem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 800000

/-- **Linearity of the box projection over a finite sum.**  For a family `f j` of states whose
slot-`i` fibres `z ↦ f j (x|i↦z)` are integrable on `A` (`A` of finite measure, `x` arbitrary),

    Pᵢ(Σ_j f_j) x = Σ_j Pᵢ(f_j) x .

The proof unfolds `Pᵢ`, exchanges the finite sum with the slot integral
(`MeasureTheory.integral_finsetSum`, the hypotheses being exactly the fibre integrability), and
distributes the constants `|A|⁻¹` and the box indicator `1_A(x_i)` over the sum. -/
theorem boxPInd_sum {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin N)
    (x : Submission.BoseGases.X N) (f : Fin N → Submission.BoseGases.X N → ℝ)
    (h : ∀ j, IntegrableOn (fun z => f j (Function.update x i z)) A volume) :
    Work.UBBInputs8.boxPInd volA A i (fun y => ∑ j, f j y) x
      = ∑ j, Work.UBBInputs8.boxPInd volA A i (f j) x := by
  simp only [Work.UBBInputs8.boxPInd]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (f := fun j z => f j (Function.update x i z))
    (fun j _ => h j)]
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **Rung-`F` pointwise identity.**  For `A ⊆ acube ℓ` of measure `volA`, a continuous state `Φ`
and `x` in the analysis box,

    Pᵢ(Σ_j P_jΦ) x = Σ_j P_j(PᵢΦ) x .

Both sides are `Σ_j (P_j ∘ Pᵢ)Φ x`: `Pᵢ` is pulled through the finite sum by `boxPInd_sum`
(the slot fibres of `P_jΦ` are integrable because `Φ` is continuous, hence `P_jΦ` is bounded and
measurable on the compact box), and then `PᵢP_j = P_jPᵢ` termwise
(`Work.BoseFixB1S.boxPInd_comm` for `j ≠ i`; for `j = i` both terms are literally `Pᵢ(PᵢΦ) x`). -/
theorem boxPInd_rungF_pointwise {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i
          (fun y => ∑ j : Fin N, Work.UBBInputs8.boxPInd volA A j Φ y) x
        = ∑ j : Fin N,
            Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x := by
  intro x hx
  -- `Φ` is bounded on the compact box; consequently every `P_jΦ` is bounded and measurable there.
  obtain ⟨C, _hC0, hC⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hint : ∀ j : Fin N,
      IntegrableOn (fun z => Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i z))
        A volume :=
    fun j => Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
      (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦc.measurable)
      (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc j hC)
  -- pull `Pᵢ` through the finite sum
  rw [boxPInd_sum volA A i x (fun j => Work.UBBInputs8.boxPInd volA A j Φ) hint]
  -- termwise commutation `PᵢP_j = P_jPᵢ`
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hji : j = i
  · subst hji; rfl
  · exact Work.BoseFixB1S.boxPInd_comm hℓ hvol hA hvolA hAc (Ne.symm hji) hΦc x

end Work.BoseFixB1
