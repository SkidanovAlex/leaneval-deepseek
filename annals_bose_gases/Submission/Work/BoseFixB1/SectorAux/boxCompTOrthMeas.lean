import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxCompT_orth
import Submission.Work.BoseFixB1S.boxQInd_boxCompT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas`

Orthogonality of the three-way box components

    boxCompT volA A S T Φ = (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ) Φ

for **measurable, box-bounded** `Φ`, `Ψ` (rather than the continuous states for which
`Work.BoseFixB1S.boxCompT_orth` states it):

    ∫_{abox N ℓ} (boxCompT S T Φ)·(boxCompT S' T' Ψ) = 0      for (S,T) ≠ (S',T') .

## Math / formalisation

The proof of `Work.BoseFixB1S.boxCompT_orth` never uses continuity except to manufacture the
state class `GoodState ℓ Φ = Measurable Φ ∧ ∃ C, ∀ x ∈ abox N ℓ, |Φ x| ≤ C` via
`goodState_of_continuous`.  All the structural ingredients live at that level:

* the fold inductions `boxCompTAux_ind` (for `Pⱼ`) and `boxCompTAux_indQ` (for `Qⱼ`) are stated
  for `GoodState` inputs, and the final eigenvector rules `boxPInd_boxCompT` /
  `boxQInd_boxCompT` only need it in order to *produce* a `GoodState` from a continuous `Φ`;
* the self-adjointness `boxPIndSelfAdjoint` is already stated for measurable, box-bounded states;
* `goodState_boxCompT`, `boxComponent_vanish_off/on`, `integral_mul_eq_zero_of_vanish` carry no
  continuity hypothesis (`goodState_boxCompT` takes a `GoodState`).

So the whole file is the `boxCompT_orth` proof rerun with `GoodState` in place of `Continuous`;
the target theorem then closes by the one-line conversion `Measurable Φ, bound CΦ ⊢ GoodState ℓ Φ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The `P`-eigenvector rule for `GoodState` states -/

/-- `boxPInd_boxCompT` with the hypothesis weakened from `Continuous Φ` to `GoodState ℓ Φ`. -/
theorem boxPInd_boxCompT_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S T : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ S then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ :=
    Work.BoseFixB1S.boxCompTAux_ind hℓ hvol hA hvolA hAc S T j (List.finRange N)
      (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦ x hx
  rw [Work.BoseFixB1S.boxCompT_eq_aux]
  exact hres

/-! ## 2. The `P`-slot case -/

/-- `orth_of_mem_S` with the hypotheses weakened from continuity to `GoodState`. -/
theorem orth_of_mem_S_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {S T S' T' : Finset (Fin N)} {j : Fin N}
    (hjS : j ∈ S) (hjS' : j ∉ S')
    {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  obtain ⟨hXm, CX, hXb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc S T hΦ
  obtain ⟨hYm, CY, hYb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc S' T' hΨ
  have h1 : ∀ x ∈ abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
      = Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x := by
    intro x hx
    rw [boxPInd_boxCompT_good hℓ hvol hA hvolA hAc S T hΦ j x hx, if_pos hjS]
  have h2 : ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x = 0 := by
    intro x hx
    rw [boxPInd_boxCompT_good hℓ hvol hA hvolA hAc S' T' hΨ j x hx, if_neg hjS']
  have hAB : (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A j
          (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.UBBInputs8.boxPInd volA A j
              (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x :=
    Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j hXm hXb hYm hYb
  calc (∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A j
            (Work.BoseFixB1S.boxCompT volA A S T Φ) x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        simp only [h1 x hx]
    _ = ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.UBBInputs8.boxPInd volA A j
              (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x := hAB
    _ = 0 := by
        have hz : (∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A S T Φ x
              * Work.UBBInputs8.boxPInd volA A j
                  (Work.BoseFixB1S.boxCompT volA A S' T' Ψ) x)
            = ∫ x in abox N ℓ, (0 : Submission.BoseGases.X N → ℝ) x := by
          apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          intro x hx
          simp only [h2 x hx, mul_zero, Pi.zero_apply]
        rw [hz]
        simp

/-! ## 3. Orthogonality for `GoodState` states -/

/-- `boxCompT_orth` with the hypotheses weakened from continuity to `GoodState`. -/
theorem boxCompT_orth_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hne : S ≠ S' ∨ T ≠ T')
    {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  have hex : ∃ j : Fin N, Work.BoseFixB1S.orthSlotType S T j
      ≠ Work.BoseFixB1S.orthSlotType S' T' j := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := Work.BoseFixB1S.orth_eq_of_slotType_eq hST hST' hcon
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
    · exfalso
      exact hjdif (((Work.BoseFixB1S.orthSlotType_eq_zero_iff S T j).mpr hS).trans
        ((Work.BoseFixB1S.orthSlotType_eq_zero_iff S' T' j).mpr hS').symm)
    · exact orth_of_mem_S_good hℓ hvol hA hvolA hAc hS hS' hΦ hΨ
  · by_cases hS' : j ∈ S'
    · rw [hswap]
      exact orth_of_mem_S_good hℓ hvol hA hvolA hAc hS' hS hΨ hΦ
    · by_cases hT : j ∈ T
      · have hT' : j ∉ T' := by
          intro h
          exact hjdif (((Work.BoseFixB1S.orthSlotType_eq_one_iff hST j).mpr ⟨hS, hT⟩).trans
            ((Work.BoseFixB1S.orthSlotType_eq_one_iff hST' j).mpr ⟨hS', h⟩).symm)
        have hnot : j ∉ S' ∪ T' := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS', hT'⟩
        exact Work.BoseFixB1S.integral_mul_eq_zero_of_vanish
          (Work.BoseFixB1S.boxComponent_vanish_off volA A (Finset.mem_union_right S hT) Φ)
          (Work.BoseFixB1S.boxComponent_vanish_on volA A hnot Ψ)
      · have hT' : j ∈ T' := by
          by_contra h
          exact hjdif
            (((Work.BoseFixB1S.orthSlotType_eq_two_iff S T j).mpr ⟨hS, hT⟩).trans
              ((Work.BoseFixB1S.orthSlotType_eq_two_iff S' T' j).mpr ⟨hS', h⟩).symm)
        have hnot : j ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS, hT⟩
        rw [hswap]
        exact Work.BoseFixB1S.integral_mul_eq_zero_of_vanish
          (Work.BoseFixB1S.boxComponent_vanish_off volA A (Finset.mem_union_right S' hT') Ψ)
          (Work.BoseFixB1S.boxComponent_vanish_on volA A hnot Φ)

/-! ## 4. The requested theorem -/

theorem boxCompTOrthMeas {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hne : S ≠ S' ∨ T ≠ T')
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ)
    (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 :=
  boxCompT_orth_good hℓ hvol hA hvolA hAc hST hST' hne
    ⟨hΦm, CΦ, hΦb⟩ ⟨hΨm, CΨ, hΨb⟩

end Work.BoseFixB1.SectorAux
