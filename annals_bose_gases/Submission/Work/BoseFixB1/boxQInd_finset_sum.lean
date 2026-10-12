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
# `Work.BoseFixB1.boxQInd_finset_sum`

The FS-faithful box (`mean-free`) projection

`Work.UBBInputs8.boxQInd volA A i Ψ = 1_A(xᵢ)·Ψ − P_{B,i}Ψ`,
`P_{B,i}Ψ = volA⁻¹ ∫_{z∈A} Ψ(x[i:=z]) · 1_A(xᵢ)`

is **linear** in the state `Ψ`, hence commutes with finite sums:

`Q_{B,i}(∑_{k∈s} Ψ k) = ∑_{k∈s} Q_{B,i}(Ψ k)`  pointwise.

The only care needed is the `IntegrableOn` side condition of additivity of the Bochner integral —
`∫ z in A, (f + g)(x[i:=z]) = ∫ z in A, f(x[i:=z]) + ∫ z in A, g(x[i:=z])` holds only when both
slot functions are integrable (for non-integrable functions the integral is conventionally `0`,
which is not additive on the nose).  The hypotheses of the statement supply exactly that: each
summand is `Measurable` and **uniformly** bounded by `K` on the analysis box `abox N ℓ`, and
`z ∈ A ⊆ acube ℓ`, `x ∈ abox N ℓ` keep `x[i:=z]` inside the box, so every slot function is
`IntegrableOn A volume` by `Work.BoseFixB1S.slotInt_of_bound`.

The result is proved by a general induction over the finset, stated with the uniform bound `K`
as a parameter (`boxQInd_finset_sum_aux`); the requested lemma (`hK : 0 ≤ K` unused) is its
instantiation.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `Q_{B,i}` kills the zero state (definitional unfolding: `∫ z in A, 0 = 0`). -/
private lemma boxQInd_finset_sum_zero {N : ℕ} (volA : ℝ) (A : Set Work.BoseFixB1.E3) (i : Fin N)
    (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd volA A i (0 : Submission.BoseGases.X N → ℝ) x = 0 := by
  simp [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]

/-- The inductive content of `boxQInd_finset_sum`: additivity of `Q_{B,i}` over an arbitrary
finset of summands that are measurable and uniformly bounded by `K` on the analysis box. -/
private lemma boxQInd_finset_sum_aux {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ℝ)
    {A : Set Work.BoseFixB1.E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {i : Fin N} {ι : Type*} (K : ℝ)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    ∀ (s : Finset ι) (Ψ : ι → Submission.BoseGases.X N → ℝ),
      (∀ k ∈ s, Measurable (Ψ k)) →
      (∀ k ∈ s, ∀ y ∈ Submission.BoseGases.abox N ℓ, |Ψ k y| ≤ K) →
      Work.UBBInputs8.boxQInd V A i (fun y => ∑ k ∈ s, Ψ k y) x
        = ∑ k ∈ s, Work.UBBInputs8.boxQInd V A i (Ψ k) x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro Ψ _ _
      have h0 : (fun y : Submission.BoseGases.X N => ∑ k ∈ (∅ : Finset ι), Ψ k y) = 0 := by
        funext y; simp
      rw [h0, Finset.sum_empty]
      exact boxQInd_finset_sum_zero V A i x
  | insert a s ha ih =>
      intro Ψ hm hb
      -- the new summand and the tail sum, with their box data
      have hma : Measurable (Ψ a) := hm a (Finset.mem_insert_self a s)
      have hba : ∀ y ∈ Submission.BoseGases.abox N ℓ, |Ψ a y| ≤ K :=
        hb a (Finset.mem_insert_self a s)
      have hm' : ∀ k ∈ s, Measurable (Ψ k) := fun k hk => hm k (Finset.mem_insert_of_mem hk)
      have hb' : ∀ k ∈ s, ∀ y ∈ Submission.BoseGases.abox N ℓ, |Ψ k y| ≤ K :=
        fun k hk => hb k (Finset.mem_insert_of_mem hk)
      -- the slot functions are integrable over `A ⊆ acube ℓ`
      have hint_a : IntegrableOn (fun z => Ψ a (Function.update x i z)) A volume :=
        Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hma hba
      have hint_s : IntegrableOn
          (fun z => (fun y : Submission.BoseGases.X N => ∑ k ∈ s, Ψ k y)
            (Function.update x i z)) A volume := by
        refine Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
          (Finset.measurable_sum s hm') (C := (s.card : ℝ) * K) ?_
        intro y hy
        calc |∑ k ∈ s, Ψ k y| ≤ ∑ k ∈ s, |Ψ k y| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ s, K := Finset.sum_le_sum (fun k hk => hb' k hk y hy)
          _ = (s.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
      -- split the inserted sum and apply additivity of `Q_{B,i}`
      have hstep : Work.UBBInputs8.boxQInd V A i (fun y => ∑ k ∈ insert a s, Ψ k y) x
          = Work.UBBInputs8.boxQInd V A i (Ψ a) x
            + Work.UBBInputs8.boxQInd V A i (fun y => ∑ k ∈ s, Ψ k y) x := by
        have hL : (fun y : Submission.BoseGases.X N => ∑ k ∈ insert a s, Ψ k y)
            = fun y => Ψ a y + ∑ k ∈ s, Ψ k y := by
          funext y
          rw [Finset.sum_insert ha]
        rw [hL]
        exact Work.BoseFixB1S.boxQInd_add V A i x hint_a hint_s
      rw [hstep, ih Ψ hm' hb', Finset.sum_insert ha]

/-- **Additivity of the FS-faithful box projection** `Q_{B,i} = 1_A(xᵢ)·Ψ − P_{B,i}Ψ` over a
finite sum of states that are measurable and uniformly bounded on the analysis box. -/
theorem boxQInd_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ℝ)
    {A : Set Work.BoseFixB1.E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {i : Fin N} {ι : Type*} (s : Finset ι)
    {Ψ : ι → Submission.BoseGases.X N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hm : ∀ k ∈ s, Measurable (Ψ k))
    (hb : ∀ k ∈ s, ∀ y ∈ Submission.BoseGases.abox N ℓ, |Ψ k y| ≤ K)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.UBBInputs8.boxQInd V A i (fun y => ∑ k ∈ s, Ψ k y) x
      = ∑ k ∈ s, Work.UBBInputs8.boxQInd V A i (Ψ k) x :=
  boxQInd_finset_sum_aux hℓ V hA hAc K hx s Ψ hm hb

end Work.BoseFixB1
