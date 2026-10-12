import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxHopDefs
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

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem a0A2QJointCompTParseval {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ Work.BoseFixB1.disjPairs N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  have hΦg : Work.BoseFixB1S.GoodState ℓ Φ :=
    Work.BoseFixB1S.goodState_of_continuous hℓ hΦc
  have hpoint : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (∑ p ∈ Work.BoseFixB1.disjPairs N,
          Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) = Φ x :=
    Work.BoseFixB1S.boxCompT_sum_eq hℓ hV hA hVeq hAc hΦc
  have hprod : ∀ p ∈ Work.BoseFixB1.disjPairs N, ∀ q ∈ Work.BoseFixB1.disjPairs N,
      IntegrableOn (fun x => Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x)
        (Submission.BoseGases.abox N ℓ) volume := by
    intro p _ q _
    exact Work.BoseFixB1S.integrableOn_mul_goodState hℓ
      (Work.BoseFixB1S.goodState_boxCompT hℓ hV hA hVeq hAc p.1 p.2 hΦg)
      (Work.BoseFixB1S.goodState_boxCompT hℓ hV hA hVeq hAc q.1 q.2 hΦg)
  have horth : ∀ p ∈ Work.BoseFixB1.disjPairs N, ∀ q ∈ Work.BoseFixB1.disjPairs N, p ≠ q →
      (∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) = 0 := by
    intro p hp q hq hpq
    have hpd : Disjoint p.1 p.2 := Work.BoseFixB1.mem_disjPairs.mp hp
    have hqd : Disjoint q.1 q.2 := Work.BoseFixB1.mem_disjPairs.mp hq
    have hne : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
      rcases eq_or_ne p.1 q.1 with h1 | h1
      · rcases eq_or_ne p.2 q.2 with h2 | h2
        · exact absurd (Prod.ext h1 h2) hpq
        · exact Or.inr h2
      · exact Or.inl h1
    exact Work.BoseFixB1S.boxCompT_orth hℓ hV hA hVeq hAc hpd hqd hne hΦc hΦc
  rw [← Work.BoseFixB1S.integral_sq_sum_of_orth (s := Work.BoseFixB1.disjPairs N)
      (f := fun p x => Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) hprod horth]
  apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
  intro x hx
  simp only [hpoint x hx]

end Work.BoseFixB1S
