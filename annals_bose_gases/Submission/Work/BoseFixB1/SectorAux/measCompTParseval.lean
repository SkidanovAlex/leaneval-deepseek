import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.a0A2QJointCompTParseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Completeness (pointwise, for an arbitrary state)

The same proof as `Work.BoseFixB1S.boxCompT_sum_eq`, with its (unused) regularity hypotheses
dropped: the resolution of unity is pointwise algebra. -/

theorem boxCompT_sum_eq_gen {N : ℕ} (V : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X N → ℝ) :
    ∀ x : Submission.BoseGases.X N,
      (∑ p ∈ Work.BoseFixB1.disjPairs N,
          Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) = Φ x := by
  intro x
  have hsum : (∑ p ∈ Work.BoseFixB1.disjPairs N,
      Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ) = Φ := by
    calc (∑ p ∈ Work.BoseFixB1.disjPairs N,
            Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ)
        = ∑ p ∈ Work.BoseFixB1.disjPairs N,
            (List.finRange N).foldl (fun g i => Work.BoseFixB1S.boxPatOp V A i
              (if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2) g) Φ :=
          Finset.sum_congr rfl (fun p _ => Work.BoseFixB1S.boxCompT_eq_foldl V A p.1 p.2 Φ)
      _ = ∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i =>
            Work.BoseFixB1S.boxPatOp V A i (c i) g) Φ :=
          Work.BoseFixB1S.sumFilterDisjointFin3 (fun c => (List.finRange N).foldl (fun g i =>
            Work.BoseFixB1S.boxPatOp V A i (c i) g) Φ)
      _ = Φ := Work.BoseFixB1S.sumFoldFinRangeTriple (fun i b g => Work.BoseFixB1S.boxPatOp V A i b g)
          (fun i Ψ => Work.BoseFixB1S.boxPatOp_sum V A i Ψ) Φ
  simpa [Finset.sum_apply] using congr_fun hsum x

/-! ## 2. The eigenvalue rule `Pⱼψ_{S,T} = [j ∈ S]·ψ_{S,T}` for a `GoodState`

`Work.BoseFixB1S.boxPInd_boxCompT` is stated for continuous states but its proof only extracts
`GoodState ℓ Φ` (via `exists_abox_bound`) before calling `boxCompTAux_ind`, whose induction is
*already* stated at `GoodState`. -/

theorem boxPInd_boxCompT_good {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S T : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S T Φ) x
        = (if j ∈ S then Work.BoseFixB1S.boxCompT V A S T Φ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ :=
    Work.BoseFixB1S.boxCompTAux_ind hℓ hV hA hVeq hAc S T j (List.finRange N)
      (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦ x hx
  rw [Work.BoseFixB1S.boxCompT_eq_aux]
  exact hres

/-! ## 3. Orthogonality of the components for `GoodState`s -/

/-- If `j ∈ S` and `j ∉ S'` then the two components are orthogonal (measurable/bounded states). -/
theorem orth_of_mem_S_good {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {S T S' T' : Finset (Fin N)} {j : Fin N}
    (hjS : j ∈ S) (hjS' : j ∉ S')
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ)
    (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT V A S T Φ x
          * Work.BoseFixB1S.boxCompT V A S' T' Ψ x) = 0 := by
  obtain ⟨hXm, CX, hXb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hV hA hVeq hAc S T hΦ
  obtain ⟨hYm, CY, hYb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hV hA hVeq hAc S' T' hΨ
  have h1 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1S.boxCompT V A S T Φ x
        = Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S T Φ) x := by
    intro x hx
    rw [boxPInd_boxCompT_good hℓ hV hA hVeq hAc S T hΦ j x hx, if_pos hjS]
  have h2 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S' T' Ψ) x = 0 := by
    intro x hx
    rw [boxPInd_boxCompT_good hℓ hV hA hVeq hAc S' T' hΨ j x hx, if_neg hjS']
  have hAB : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S T Φ) x
          * Work.BoseFixB1S.boxCompT V A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT V A S T Φ x
            * Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S' T' Ψ) x :=
    Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hV hA hVeq hAc j hXm hXb hYm hYb
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT V A S T Φ x
          * Work.BoseFixB1S.boxCompT V A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S T Φ) x
            * Work.BoseFixB1S.boxCompT V A S' T' Ψ x := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        simp only [h1 x hx]
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT V A S T Φ x
            * Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S' T' Ψ) x := hAB
    _ = 0 := by
        have hz : (∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1S.boxCompT V A S T Φ x
                * Work.UBBInputs8.boxPInd V A j (Work.BoseFixB1S.boxCompT V A S' T' Ψ) x)
            = ∫ x in Submission.BoseGases.abox N ℓ, (0 : Submission.BoseGases.X N → ℝ) x := by
          apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          intro x hx
          simp only [h2 x hx, mul_zero, Pi.zero_apply]
        rw [hz]
        simp

/-- **Orthogonality of the three-way components** (`GoodState` version of
`Work.BoseFixB1S.boxCompT_orth`). -/
theorem boxCompT_orth_good {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hne : S ≠ S' ∨ T ≠ T')
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ)
    (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT V A S T Φ x
          * Work.BoseFixB1S.boxCompT V A S' T' Ψ x) = 0 := by
  have hex : ∃ j : Fin N, Work.BoseFixB1S.orthSlotType S T j
      ≠ Work.BoseFixB1S.orthSlotType S' T' j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := Work.BoseFixB1S.orth_eq_of_slotType_eq hST hST' hcon
    rcases hne with h | h
    · exact h h1
    · exact h h2
  obtain ⟨j, hjdif⟩ := hex
  have hswap : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT V A S T Φ x
          * Work.BoseFixB1S.boxCompT V A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT V A S' T' Ψ x
            * Work.BoseFixB1S.boxCompT V A S T Φ x := by
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    ring
  by_cases hS : j ∈ S
  · by_cases hS' : j ∈ S'
    · exact absurd (by unfold Work.BoseFixB1S.orthSlotType; rw [if_pos hS, if_pos hS']) hjdif
    · exact orth_of_mem_S_good hℓ hV hA hVeq hAc hS hS' hΦ hΨ
  · by_cases hS' : j ∈ S'
    · rw [hswap]
      exact orth_of_mem_S_good hℓ hV hA hVeq hAc hS' hS hΨ hΦ
    · by_cases hT : j ∈ T
      · have hT' : j ∉ T' := fun h =>
          hjdif (by unfold Work.BoseFixB1S.orthSlotType
                    rw [if_neg hS, if_pos hT, if_neg hS', if_pos h])
        have hnot : j ∉ S' ∪ T' := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS', hT'⟩
        exact Work.BoseFixB1S.integral_mul_eq_zero_of_vanish
          (Work.BoseFixB1S.boxComponent_vanish_off V A (Finset.mem_union_right S hT) Φ)
          (Work.BoseFixB1S.boxComponent_vanish_on V A hnot Ψ)
      · have hT' : j ∈ T' := by
          by_contra h
          exact hjdif (by unfold Work.BoseFixB1S.orthSlotType
                          rw [if_neg hS, if_neg hT, if_neg hS', if_neg h])
        have hnot : j ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS, hT⟩
        rw [hswap]
        exact Work.BoseFixB1S.integral_mul_eq_zero_of_vanish
          (Work.BoseFixB1S.boxComponent_vanish_off V A (Finset.mem_union_right S' hT') Ψ)
          (Work.BoseFixB1S.boxComponent_vanish_on V A hnot Φ)

/-! ## 4. The Parseval identity -/

theorem measCompTParseval {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) :
    (∑ p ∈ Work.BoseFixB1.disjPairs N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  have hΦg : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  have hpoint : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (∑ p ∈ Work.BoseFixB1.disjPairs N,
          Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) = Φ x :=
    fun x _ => boxCompT_sum_eq_gen V A Φ x
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
    exact boxCompT_orth_good hℓ hV hA hVeq hAc hpd hqd hne hΦg hΦg
  rw [← Work.BoseFixB1S.integral_sq_sum_of_orth (s := Work.BoseFixB1.disjPairs N)
      (f := fun p x => Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) hprod horth]
  apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
  intro x hx
  simp only [hpoint x hx]

end Work.BoseFixB1.SectorAux
