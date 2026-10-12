import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.HopDefs
import Submission.Work.BoseFixB1S.boxPInd_finset_sum_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.hopBracketDecomp`

The FS `eq:Q1n0` **bracket identity** at the box projections of the sliding box: with
`n₀Φ = rungF volA A Φ = Σ_j P_jΦ` (the state of FS `eq:Q1n0`) and `m = μ·volA`,

    Pᵢ(n₀Φ) − (1 + m)·PᵢΦ
      = Σ_{p ∈ hopPairSet i} (|p.1| − 1 − m)·ψ_p ,   ψ_p = boxCompT volA A p.1 p.2 Φ ,

where `hopPairSet i` is the set of disjoint pairs `(S,T)` with `i ∈ S` (`HopDefs`).

## Math

The two ingredients are the eigenvalue identities of the joint components `ψ_p` of the
commuting family `(Pᵢ, Qᵢ, Rᵢ)ᵢ`:

* **`n₀` is diagonal**: on the analysis box, `n₀Φ = Σ_{p ∈ disjPairs N} |p.1|·ψ_p`.  Indeed, by
  `boxPInd_eq_sum_boxCompT` (in the form `P_jΦ = Σ_{p : j ∈ p.1} ψ_p`) and the double-counting
  identity `sum_card_mul_eq_sum_j`, summing over the slots `j` counts the component `ψ_p`
  exactly `|p.1|` times.
* **The eigenrule** `Pᵢψ_p = [i ∈ p.1]·ψ_p` (`boxPInd_boxCompT`), together with linearity of
  `Pᵢ` over the finite sum (`boxPInd_finset_sum_gen`, the integrability side conditions coming
  from `GoodState` of the components and `slotInt_of_bound`) and scalar pull-out, gives

      Pᵢ(n₀Φ) = Σ_{p : i ∈ p.1} |p.1|·ψ_p ,     PᵢΦ = Σ_{p : i ∈ p.1} ψ_p .

Subtracting `(1+m)·PᵢΦ` and collecting the coefficient of `ψ_p`, which is
`|p.1| − 1 − m`, gives the claim.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1600000

theorem hopBracketDecomp {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (i : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1.rungF volA A Φ) x
        - (1 + μ * volA) * (Work.UBBInputs8.boxPInd volA A i Φ x)
      = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          ((p.1.card : ℝ) - 1 - μ * volA) * Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  classical
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  have hset : hopPairSet i = (disjPairs N).filter (fun p => i ∈ p.1) := rfl
  -- Scalar pull-out for the box projection.
  have hsmul : ∀ (c : ℝ) (Ψ : Submission.BoseGases.X N → ℝ),
      Work.UBBInputs8.boxPInd volA A i (fun y => c * Ψ y) x
        = c * Work.UBBInputs8.boxPInd volA A i Ψ x := by
    intro c Ψ
    simp only [Work.UBBInputs8.boxPInd]
    rw [MeasureTheory.integral_const_mul]
    ring
  -- The joint-component expansion of `n₀Φ = rungF volA A Φ`.
  have hdecomp : ∀ y ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1.rungF volA A Φ y
        = ∑ p ∈ disjPairs N, (p.1.card : ℝ) * boxCompT volA A p.1 p.2 Φ y := by
    intro y hy
    simp only [Work.BoseFixB1.rungF]
    rw [sum_card_mul_eq_sum_j (N := N) (fun p => boxCompT volA A p.1 p.2 Φ y)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine (boxPInd_eq_sum_boxCompT hℓ hvol hA hvolA hAc hΦc j y hy).trans ?_
    rw [Finset.sum_filter]
  -- (a) `PᵢΦ = Σ_{p ∋ i} ψ_p`.
  have hPi : Work.UBBInputs8.boxPInd volA A i Φ x
      = ∑ p ∈ hopPairSet i, boxCompT volA A p.1 p.2 Φ x := by
    rw [hset]
    exact boxPInd_eq_sum_boxCompT hℓ hvol hA hvolA hAc hΦc i x hx
  -- (b) `Pᵢ(n₀Φ) = Σ_{p ∋ i} |p.1|·ψ_p`.
  have hPeig : Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1.rungF volA A Φ) x
      = ∑ p ∈ hopPairSet i, (p.1.card : ℝ) * boxCompT volA A p.1 p.2 Φ x := by
    rw [hset]
    rw [agreeBox_boxPInd hA hAc i hdecomp x hx]
    have hInt : ∀ p ∈ disjPairs N,
        IntegrableOn (fun z => (p.1.card : ℝ) * boxCompT volA A p.1 p.2 Φ
          (Function.update x i z)) A volume := by
      intro p _
      obtain ⟨C, hC⟩ := (hG p).2
      exact slotInt_of_bound hℓ hA hAc i x hx
        (f := fun y => (p.1.card : ℝ) * boxCompT volA A p.1 p.2 Φ y)
        (measurable_const.mul (hG p).1)
        (fun y hy => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hC y hy) (abs_nonneg _))
    rw [boxPInd_finset_sum_gen volA A i x (disjPairs N)
      (fun p => fun y => (p.1.card : ℝ) * boxCompT volA A p.1 p.2 Φ y) hInt]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hsmul, boxPInd_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦc i x hx]
    by_cases hi : i ∈ p.1 <;> simp [hi]
  rw [hPeig, hPi, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

end Work.BoseFixB1S
