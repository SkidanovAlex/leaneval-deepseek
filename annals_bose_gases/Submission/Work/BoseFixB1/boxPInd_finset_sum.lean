import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPInd_finset_sum`

The FS-faithful box condensate projection `P_i = UBBInputs8.boxPInd V A i` is *linear*:

`P_i (∑_{k∈s} Ψ_k) = ∑_{k∈s} P_i Ψ_k`   pointwise on the analysis box `abox N ℓ`.

`P_i` is the mean over the box `A ⊆ acube ℓ` in the `i`-th slot followed by multiplication with the
box indicator `1_A(x_i)`.  The content of the lemma is therefore (a) the exchange of the
`z`-integral over `A` with the finite sum — legitimate because each `z ↦ Ψ_k (x_i ↦ z)` is
integrable on `A`, being measurable and bounded on the box (`Work.BoseFixB1S.slotInt_of_bound`) —
and (b) the distribution of the constant factor `(1/V)·1_A(x_i)` over the finite sum.

This is the `P`-half of the linearity of the FS box projections at the level of finite sums; the
`Q`-half is `Work.BoseFixB1.boxQInd_finset_sum`.
-/

namespace Work.BoseFixB1

theorem boxPInd_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ℝ)
    {A : Set Work.BoseFixB1.E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {i : Fin N} {ι : Type*} (s : Finset ι)
    {Ψ : ι → Submission.BoseGases.X N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hm : ∀ k ∈ s, Measurable (Ψ k))
    (hb : ∀ k ∈ s, ∀ y ∈ Submission.BoseGases.abox N ℓ, |Ψ k y| ≤ K)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.UBBInputs8.boxPInd V A i (fun y => ∑ k ∈ s, Ψ k y) x
      = ∑ k ∈ s, Work.UBBInputs8.boxPInd V A i (Ψ k) x := by
  -- Each slot composition `z ↦ Ψ k (x_i ↦ z)` is integrable on `A`: it is measurable and
  -- bounded by `K` on the analysis box, which absorbs `A` under the slot update.
  have hint : ∀ k ∈ s,
      MeasureTheory.IntegrableOn (fun z => Ψ k (Function.update x i z)) A MeasureTheory.volume :=
    fun k hk => Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx (hm k hk) (hb k hk)
  -- Exchange the finite sum with the slot integral, then distribute the constant factor.
  have hsum : (∫ z in A, ∑ k ∈ s, Ψ k (Function.update x i z))
      = ∑ k ∈ s, ∫ z in A, Ψ k (Function.update x i z) :=
    MeasureTheory.integral_finsetSum s (f := fun k z => Ψ k (Function.update x i z))
      (fun k hk => hint k hk)
  unfold Work.UBBInputs8.boxPInd
  rw [show (∫ z in A, (fun y => ∑ k ∈ s, Ψ k y) (Function.update x i z))
        = ∫ z in A, ∑ k ∈ s, Ψ k (Function.update x i z) from rfl,
    hsum, Finset.mul_sum, Finset.sum_mul]

end Work.BoseFixB1
