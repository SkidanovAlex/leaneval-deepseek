import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxPairQCount_eq_sum_compT
import Submission.Work.BoseFixB1S.boxPairQCount_swap
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
open Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The eigenvalue rules, at `GoodState` states -/

/-- Slot-`j` `P`-eigenvalue rule for the three-way joint components, for a state that is
measurable and bounded on the analysis box.  (`GoodState` form of
`Work.BoseFixB1S.boxPInd_boxCompT`; the proof is that of the original with
`goodState_of_continuous` replaced by the hypothesis.) -/
theorem boxPInd_boxCompTGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S T : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ S then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ :=
    Work.BoseFixB1S.boxCompTAux_ind hℓ hvol hA hvolA hAc S T j
      (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦ x hx
  rw [Work.BoseFixB1S.boxCompT_eq_aux]
  exact hres

/-- Slot-`j` `Q`-eigenvalue rule for the three-way joint components, at `GoodState` states.
(`GoodState` form of `Work.BoseFixB1S.boxQInd_boxCompT`.) -/
theorem boxQInd_boxCompTGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {S T : Finset (Fin N)} (hST : Disjoint S T)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ T then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ :=
    Work.BoseFixB1S.boxCompTAux_indQ hℓ hvol hA hvolA hAc S T hST j
      (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦ x hx
  rw [Work.BoseFixB1S.boxCompT_eq_aux]
  exact hres

/-! ## 2. The resolution of unity (no hypothesis on `Φ`) -/

/-- The three-way joint components resolve the identity on the analysis box:
`Σ_{(S,T), S ⊥ T} ψ_{S,T} = Φ`, pointwise.  No hypothesis on `Φ` at all (the continuity
hypothesis of `Work.BoseFixB1S.boxCompT_sum_eq` is unused in its proof). -/
theorem boxCompT_sum_eqGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ} :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (∑ p ∈ Work.BoseFixB1S.disjPairs N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = Φ x := by
  intro x hx
  have hsum : (∑ p ∈ Work.BoseFixB1S.disjPairs N,
      Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) = Φ := by
    calc (∑ p ∈ Work.BoseFixB1S.disjPairs N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
        = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            (List.finRange N).foldl (fun g i => boxPatOp volA A i
              (if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2) g) Φ :=
          Finset.sum_congr rfl (fun p _ => boxCompT_eq_foldl volA A p.1 p.2 Φ)
      _ = ∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i =>
            boxPatOp volA A i (c i) g) Φ :=
          sumFilterDisjointFin3 (fun c => (List.finRange N).foldl (fun g i =>
            boxPatOp volA A i (c i) g) Φ)
      _ = Φ := sumFoldFinRangeTriple (fun i b g => boxPatOp volA A i b g)
          (fun i Ψ => boxPatOp_sum volA A i Ψ) Φ
  simpa [Finset.sum_apply] using congr_fun hsum x

/-! ## 3. Orthogonality of the joint components, at `GoodState` states -/

/-- If `j ∈ S` and `j ∉ S'` then the two components are orthogonal on the box, for `GoodState`
states.  (`GoodState` form of `Work.BoseFixB1S.orth_of_mem_S`.) -/
theorem orth_of_mem_SGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {S T S' T' : Finset (Fin N)} {j : Fin N}
    (hjS : j ∈ S) (hjS' : j ∉ S')
    {Φ Ψ : X N → ℝ} (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) :
    (∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
        * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  obtain ⟨hXm, CX, hXb⟩ := goodState_boxCompT hℓ hvol hA hvolA hAc S T hΦ
  obtain ⟨hYm, CY, hYb⟩ := goodState_boxCompT hℓ hvol hA hvolA hAc S' T' hΨ
  have h1 : ∀ x ∈ abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
      = UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x := by
    intro x hx
    rw [boxPInd_boxCompTGood hℓ hvol hA hvolA hAc S T hΦ j x hx, if_pos hjS]
  have h2 : ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x = 0 := by
    intro x hx
    rw [boxPInd_boxCompTGood hℓ hvol hA hvolA hAc S' T' hΨ j x hx, if_neg hjS']
  have hAB : (∫ x in abox N ℓ,
        UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
          * UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x :=
    boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j hXm hXb hYm hYb
  calc (∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x := by
        apply MeasureTheory.setIntegral_congr_fun (abox_measurable N ℓ)
        intro x hx
        simp only [h1 x hx]
    _ = ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
          * UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x := hAB
    _ = 0 := by
        have hz : (∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
              * UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x)
            = ∫ x in abox N ℓ, (0 : X N → ℝ) x := by
          apply MeasureTheory.setIntegral_congr_fun (abox_measurable N ℓ)
          intro x hx
          simp only [h2 x hx, mul_zero, Pi.zero_apply]
        rw [hz]
        simp

/-- **Orthogonality of the three-way joint components** on the box, at `GoodState` states.
(`GoodState` form of `Work.BoseFixB1S.boxCompT_orth`.) -/
theorem boxCompT_orthGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hne : S ≠ S' ∨ T ≠ T')
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  have hex : ∃ j : Fin N, orthSlotType S T j ≠ orthSlotType S' T' j := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := orth_eq_of_slotType_eq hST hST' hcon
    rcases hne with h | h
    · exact h h1
    · exact h h2
  obtain ⟨j, hjdif⟩ := hex
  have hswap : (∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
        * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S' T' Ψ x
          * Work.BoseFixB1S.boxCompT volA A S T Φ x := by
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    ring
  by_cases hS : j ∈ S
  · by_cases hS' : j ∈ S'
    · exact absurd (by unfold orthSlotType; rw [if_pos hS, if_pos hS']) hjdif
    · exact orth_of_mem_SGood hℓ hvol hA hvolA hAc hS hS' hΦ hΨ
  · by_cases hS' : j ∈ S'
    · rw [hswap]
      exact orth_of_mem_SGood hℓ hvol hA hvolA hAc hS' hS hΨ hΦ
    · by_cases hT : j ∈ T
      · have hT' : j ∉ T' := fun h =>
          hjdif (by unfold orthSlotType; rw [if_neg hS, if_pos hT, if_neg hS', if_pos h])
        have hnot : j ∉ S' ∪ T' := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS', hT'⟩
        exact integral_mul_eq_zero_of_vanish
          (boxComponent_vanish_off volA A (Finset.mem_union_right S hT) Φ)
          (boxComponent_vanish_on volA A hnot Ψ)
      · have hT' : j ∈ T' := by
          by_contra h
          exact hjdif (by unfold orthSlotType; rw [if_neg hS, if_neg hT, if_neg hS', if_neg h])
        have hnot : j ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS, hT⟩
        rw [hswap]
        exact integral_mul_eq_zero_of_vanish
          (boxComponent_vanish_off volA A (Finset.mem_union_right S' hT') Ψ)
          (boxComponent_vanish_on volA A hnot Φ)

/-! ## 4. Parseval for the orthogonal components, at `GoodState` states -/

/-- **Parseval for the three-way components**, at `GoodState` states: for a family `s` of
disjoint pairs, the squared `L²`-norm of the sum of the components is the sum of the squared
norms.  (`GoodState` form of `Work.BoseFixB1S.integral_sum_compT_sq`.) -/
theorem integral_sum_compT_sqGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦ : GoodState ℓ Φ)
    (s : Finset (Finset (Fin N) × Finset (Fin N))) (hs : ∀ p ∈ s, Disjoint p.1 p.2) :
    (∫ x in abox N ℓ, (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∑ p ∈ s, ∫ x in abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦ
  -- the pairwise products of components are integrable on the box
  have hprod : ∀ p ∈ s, ∀ q ∈ s, IntegrableOn
      (fun x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x) (abox N ℓ) volume := by
    intro p _ q _
    obtain ⟨Cf, hCf⟩ := (hG p).2
    obtain ⟨Cg, hCg⟩ := (hG q).2
    exact integrableOn_mul_of_bound hℓ (hG p).1 (hG q).1 hCf hCg
  -- the pointwise expansion of the square into the double sum
  have hpt : ∀ x : X N,
      (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2
        = ∑ p ∈ s, ∑ q ∈ s,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x := by
    intro x
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
  calc (∫ x in abox N ℓ, (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x :=
        setIntegral_congr_fun (abox_measurable N ℓ) (fun x _ => hpt x)
    _ = ∑ p ∈ s, ∫ x in abox N ℓ, ∑ q ∈ s,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x :=
        MeasureTheory.integral_finsetSum s
          (f := fun p x => ∑ q ∈ s,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
          (fun p hp => integrable_finsetSum
            (μ := (volume : Measure (X N)).restrict (abox N ℓ)) s
            (f := fun q x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
            (fun q hq => hprod p hp q hq))
    _ = ∑ p ∈ s, ∑ q ∈ s,
          ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x := by
        apply Finset.sum_congr rfl
        intro p hp
        exact MeasureTheory.integral_finsetSum s
          (f := fun q x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
          (fun q hq => hprod p hp q hq)
    _ = ∑ p ∈ s, ∫ x in abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single_of_mem p hp (fun q hq hqp =>
          boxCompT_orthGood hℓ hvol hA hvolA hAc (hs p hp) (hs q hq)
            (ne_fst_or_ne_snd hqp.symm) hΦ hΦ)]
        apply integral_congr_ae
        filter_upwards with x
        ring

/-! ## 5. The `Q`-component decomposition and the per-pair spectral identity -/

/-- On the analysis box, `QⱼΦ` is the sum of the three-way joint components whose `Q`-slot set
contains `j`, at `GoodState` states.  (`GoodState` form of the private
`boxPairQCount_qdecomp`.) -/
theorem boxPairQCount_qdecompGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      UBBInputs8.boxQInd volA A j Φ x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦ
  have hsum : ∀ y ∈ abox N ℓ, Φ y = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
      Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y :=
    fun y hy => (boxCompT_sum_eqGood hℓ hvol hA hvolA hAc y hy).symm
  have h1 : UBBInputs8.boxQInd volA A j Φ x
      = UBBInputs8.boxQInd volA A j
          (fun y => ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x :=
    agreeBox_boxQInd hA hAc j hsum x hx
  have h2 : UBBInputs8.boxQInd volA A j
        (fun y => ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x
      = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          UBBInputs8.boxQInd volA A j (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x :=
    boxQInd_finset_sum_gen volA A j x (Work.BoseFixB1S.disjPairs N)
      (fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
      (fun p _ => slotInt_of_bound hℓ hA hAc j x hx (hG p).1 (hG p).2.choose_spec)
  have h3 : (∑ p ∈ Work.BoseFixB1S.disjPairs N,
        UBBInputs8.boxQInd volA A j (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x)
      = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.2),
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p hp =>
      boxQInd_boxCompTGood hℓ hvol hA hvolA hAc (Work.BoseFixB1S.mem_disjPairs.mp hp)
        hΦ j x hx)
  rw [h1, h2, h3]

/-- **The per-ordered-pair spectral identity**, at `GoodState` states: on the box,
`PᵢQⱼΦ = Σ_{p : i ∈ p.1, j ∈ p.2} ψ_p`, and the components of distinct disjoint pairs are
orthogonal there, so the box `L²`-norm of `PᵢQⱼΦ` is the sum of the squared norms of those
components.  (`GoodState` form of the private `boxPairQCount_pident`.) -/
theorem boxPairQCount_pidentGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : GoodState ℓ Φ) (i j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦ
  -- the pointwise component decomposition of `PᵢQⱼΦ` on the box
  have hpt : ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
    intro x hx
    have hQ := boxPairQCount_qdecompGood hℓ hvol hA hvolA hAc hΦ j
    calc UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
        = UBBInputs8.boxPInd volA A i
            (fun y => ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.2),
              Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x :=
            agreeBox_boxPInd hA hAc i hQ x hx
      _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.2),
            UBBInputs8.boxPInd volA A i (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x :=
            boxPInd_finset_sum_gen volA A i x
              ((Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.2))
              (fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
              (fun p _ => slotInt_of_bound hℓ hA hAc i x hx (hG p).1 (hG p).2.choose_spec)
      _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.2),
            (if i ∈ p.1 then Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x else 0) :=
            Finset.sum_congr rfl
              (fun p _ => boxPInd_boxCompTGood hℓ hvol hA hvolA hAc p.1 p.2 hΦ i x hx)
      _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
            conv_lhs => rw [Finset.sum_filter (s := Work.BoseFixB1S.disjPairs N)
              (p := fun p => j ∈ p.2)
              (f := fun p => if i ∈ p.1 then
                Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x else 0)]
            conv_rhs => rw [Finset.sum_filter (s := Work.BoseFixB1S.disjPairs N)
              (p := fun p => i ∈ p.1 ∧ j ∈ p.2)
              (f := fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)]
            apply Finset.sum_congr rfl
            intro p _
            by_cases hi : i ∈ p.1 <;> by_cases hj : j ∈ p.2 <;> simp [hi, hj]
  calc (∫ x in abox N ℓ,
          (UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∫ x in abox N ℓ,
          (∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by rw [hpt x hx])
    _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
          ∫ x in abox N ℓ, (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          integral_sum_compT_sqGood hℓ hvol hA hvolA hAc hΦ _
            (fun p hp => Work.BoseFixB1S.mem_disjPairs.mp (Finset.mem_filter.mp hp).1)

/-! ## 6. The pair-`PQ` count identity -/

/-- **The ordered pair-`PQ` count identity** at the FS-faithful box projections, for a state
that is merely measurable and bounded on the analysis box. -/
theorem boxPairQCountMeas {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) :
    (∑ p ∈ Work.BoseFixB1S.disjPairs N, (p.1.card : ℝ) * (p.2.card : ℝ) *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2 := by
  have hΦG : GoodState ℓ Φ :=
    ⟨hΦm, max Cb 0, fun x hx => le_trans (hΦb x hx) (le_max_left Cb 0)⟩
  have h1 : (∑ q ∈ pairSet N,
        ∫ x in abox N ℓ,
          (UBBInputs8.boxPInd volA A q.1 (UBBInputs8.boxQInd volA A q.2 Φ) x) ^ 2)
      = ∑ q ∈ pairSet N,
          ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.2),
            ∫ x in abox N ℓ, (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
    Finset.sum_congr rfl
      (fun q _ => boxPairQCount_pidentGood hℓ hvol hA hvolA hAc hΦG q.1 q.2)
  have h2 := boxPairQCount_swap
    (fun p => ∫ x in abox N ℓ, (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
  rw [← h2, ← h1]

end Work.BoseFixB1.SectorAux
