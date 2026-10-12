import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.SectorAux.GoodStateSpectralPieces
import Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-- Two distinct ordered pairs of slot sets differ in one of their two components. -/
theorem ne_fst_or_ne_snd_pair {N : ℕ} {p q : Finset (Fin N) × Finset (Fin N)} (h : p ≠ q) :
    p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
  by_contra hcon
  push Not at hcon
  exact h (Prod.ext hcon.1 hcon.2)

/-- **The single-slot spectral identity** for `GoodState` states: on the box, the condensate
projection `PⱼΦ` is the sum of the joint components whose `P`-slot set contains `j`, and the cross
terms of the squared sum integrate to `0` by orthogonality of the components. -/
theorem integral_sq_boxPInd_eq_goodState {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)
      = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          (if j ∈ p.1 then ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 else 0) := by
  have hpoint := boxPInd_eq_sum_boxCompT_goodState (N := N) hℓ hvol hA hvolA hAc hΦg j
  have hprod : ∀ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
      ∀ q ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
      IntegrableOn (fun x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
        (Submission.BoseGases.abox N ℓ) volume := by
    intro p hp q hq
    exact Work.BoseFixB1S.integrableOn_mul_goodState hℓ
      (Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦg)
      (Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc q.1 q.2 hΦg)
  have horth : ∀ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
      ∀ q ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1), p ≠ q →
      (∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x) = 0 := by
    intro p hp q hq hpq
    have hpd : Disjoint p.1 p.2 :=
      Work.BoseFixB1S.mem_disjPairs.mp (Finset.mem_filter.mp hp).1
    have hqd : Disjoint q.1 q.2 :=
      Work.BoseFixB1S.mem_disjPairs.mp (Finset.mem_filter.mp hq).1
    exact boxCompT_orth_good hℓ hvol hA hvolA hAc hpd hqd (ne_fst_or_ne_snd_pair hpq)
      hΦg hΦg
  calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
        apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        simp only [hpoint x hx]
    _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
        Work.BoseFixB1S.integral_sq_sum_of_orth hprod horth
    _ = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          (if j ∈ p.1 then ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 else 0) :=
        Finset.sum_filter (s := Work.BoseFixB1S.disjPairs N) (p := fun p => j ∈ p.1) _

theorem goodBoxFlatCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
          (p.1.card : ℝ)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  let F : Finset (Fin N) × Finset (Fin N) → ℝ :=
    fun p => ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2
  have hB : ∀ j : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)
        = ∑ p ∈ Work.BoseFixB1S.disjPairs N, (if j ∈ p.1 then F p else 0) :=
    fun j => integral_sq_boxPInd_eq_goodState hℓ hvol hA hvolA hAc hΦg j
  show Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      = ∑ p ∈ Work.BoseFixB1S.disjPairs N, (p.1.card : ℝ) * F p
  calc Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      = ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2 := rfl
    _ = ∑ j : Fin N, ∑ p ∈ Work.BoseFixB1S.disjPairs N, (if j ∈ p.1 then F p else 0) :=
        Finset.sum_congr rfl (fun j _ => hB j)
    _ = ∑ p ∈ Work.BoseFixB1S.disjPairs N, (p.1.card : ℝ) * F p :=
        (Work.BoseFixB1S.sum_card_mul_eq_sum_j F).symm

end Work.BoseFixB1.SectorAux
