import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_eq_sum_boxCompT
import Submission.Work.BoseFixB1S.integral_sq_sum_of_orth
import Submission.Work.BoseFixB1S.sum_card_mul_eq_sum_j
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

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The single-slot spectral identity** `(★★)`: for a continuous state `Φ`, the box
condensate projection `PⱼΦ` has, on the box, the same `L²`-norm as the sum of the joint
components `ψ_{S,T}` with `j ∈ S`; the cross terms vanish by orthogonality. -/
theorem integral_sq_boxPInd_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (j : Fin N) :
    (∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A j Φ x) ^ 2)
      = ∑ p ∈ disjPairs N,
          (if j ∈ p.1 then ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 else 0) := by
  have hpoint := boxPInd_eq_sum_boxCompT (N := N) hℓ hvol hA hvolA hAc hΦc j
  have hΦg : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hprod : ∀ p ∈ (disjPairs N).filter (fun p => j ∈ p.1),
      ∀ q ∈ (disjPairs N).filter (fun p => j ∈ p.1),
      IntegrableOn (fun x => boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x)
        (abox N ℓ) volume := by
    intro p hp q hq
    exact integrableOn_mul_goodState hℓ
      (goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦg)
      (goodState_boxCompT hℓ hvol hA hvolA hAc q.1 q.2 hΦg)
  have horth : ∀ p ∈ (disjPairs N).filter (fun p => j ∈ p.1),
      ∀ q ∈ (disjPairs N).filter (fun p => j ∈ p.1), p ≠ q →
      (∫ x in abox N ℓ, boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x) = 0 := by
    intro p hp q hq hpq
    have hpd : Disjoint p.1 p.2 := mem_disjPairs.mp (Finset.mem_filter.mp hp).1
    have hqd : Disjoint q.1 q.2 := mem_disjPairs.mp (Finset.mem_filter.mp hq).1
    have hne : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
      rcases eq_or_ne p.1 q.1 with h1 | h1
      · rcases eq_or_ne p.2 q.2 with h2 | h2
        · exact absurd (Prod.ext h1 h2) hpq
        · exact Or.inr h2
      · exact Or.inl h1
    exact boxCompT_orth hℓ hvol hA hvolA hAc hpd hqd hne hΦc hΦc
  calc (∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A j Φ x) ^ 2)
      = ∫ x in abox N ℓ,
          (∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.1), boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
        apply setIntegral_congr_fun (abox_measurable N ℓ)
        intro x hx
        simp only [hpoint x hx]
    _ = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.1),
          ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
        integral_sq_sum_of_orth hprod horth
    _ = ∑ p ∈ disjPairs N,
          (if j ∈ p.1 then ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 else 0) :=
        Finset.sum_filter (s := disjPairs N) (p := fun p => j ∈ p.1) _

/-- **The localised flat count as a spectral sum over the three-way joint components**:
`Σᵢ∫(PᵢΦ)² = Σ_{(S,T), S⊥T} |S| · ∫(ψ_{S,T})²`. -/
theorem boxFlatCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
          (p.1.card : ℝ)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  let F : Finset (Fin N) × Finset (Fin N) → ℝ :=
    fun p => ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2
  have hB : ∀ j : Fin N,
      (∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A j Φ x) ^ 2)
        = ∑ p ∈ disjPairs N, (if j ∈ p.1 then F p else 0) :=
    fun j => integral_sq_boxPInd_eq hℓ hvol hA hvolA hAc hΦc j
  show boxFlatCount volA ℓ A Φ = ∑ p ∈ disjPairs N, (p.1.card : ℝ) * F p
  calc boxFlatCount volA ℓ A Φ
      = ∑ j : Fin N, ∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A j Φ x) ^ 2 := rfl
    _ = ∑ j : Fin N, ∑ p ∈ disjPairs N, (if j ∈ p.1 then F p else 0) :=
        Finset.sum_congr rfl (fun j _ => hB j)
    _ = ∑ p ∈ disjPairs N, (p.1.card : ℝ) * F p := (sum_card_mul_eq_sum_j F).symm

end Work.BoseFixB1S
