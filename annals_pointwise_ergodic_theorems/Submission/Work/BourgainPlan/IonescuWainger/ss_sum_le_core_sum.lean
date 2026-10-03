import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.SunflowerSSDefs

namespace Work.BourgainPlan.IonescuWainger

open Finset
open scoped BigOperators

set_option autoImplicit false

theorem ss_sum_le_core_sum {α : Type*} [Fintype α] [DecidableEq α]
    (k r : ℕ) (hr : 2 ≤ r) (w : Finset α → NNReal) :
    (∑ X : Fin r → Finset α, if Work.BourgainPlan.IonescuWainger.IsSS k X then ∏ i, w (X i) else 0)
      ≤ ∑ A₀ : Finset α, if A₀.card ≤ k then
          ∑ A : Fin r → Finset α,
            (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                (∀ i j, i ≠ j → Disjoint (A i) (A j))
             then ∏ i, w (A₀ ∪ A i) else 0)
        else 0 := by
  classical
  have hr0 : 0 < r := by omega
  have hr1 : 1 < r := by omega
  let i0 : Fin r := ⟨0, hr0⟩
  let i1 : Fin r := ⟨1, hr1⟩
  have hi : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp only [i0, i1] at this
    exact absurd this (by norm_num)
  let F : (Fin r → Finset α) → Finset α × (Fin r → Finset α) :=
    fun X => (X i0 ∩ X i1, fun i => X i \ (X i0 ∩ X i1))
  let g : Finset α × (Fin r → Finset α) → NNReal :=
    fun p => ∏ i, w (p.1 ∪ p.2 i)
  let C : Finset α × (Fin r → Finset α) → Prop :=
    fun p => p.1.card ≤ k ∧ (∀ i, p.2 i ⊆ Finset.univ \ p.1) ∧
      (∀ i, (p.2 i).card = k - p.1.card) ∧ (∀ i j, i ≠ j → Disjoint (p.2 i) (p.2 j))
  have hsubA0 : ∀ X : Fin r → Finset α, IsSS k X → ∀ i, X i0 ∩ X i1 ⊆ X i := by
    intro X hX i
    obtain ⟨-, A₀c, hsubc, hint⟩ := hX
    rw [hint i0 i1 hi]
    exact hsubc i
  have hgeq : ∀ X : Fin r → Finset α, IsSS k X → g (F X) = ∏ i, w (X i) := by
    intro X hX
    dsimp only [F, g]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.union_sdiff_of_subset (hsubA0 X hX i)]
  have hinj : Set.InjOn F
      (↑(Finset.univ.filter (fun X : Fin r → Finset α => IsSS k X)) : Set (Fin r → Finset α)) := by
    intro X hXm Y hYm hXY
    rw [Finset.mem_coe, Finset.mem_filter] at hXm hYm
    have hX : IsSS k X := hXm.2
    have hY : IsSS k Y := hYm.2
    funext i
    have hx : X i = (F X).1 ∪ (F X).2 i := by
      dsimp only [F]
      rw [Finset.union_sdiff_of_subset (hsubA0 X hX i)]
    have hy : Y i = (F Y).1 ∪ (F Y).2 i := by
      dsimp only [F]
      rw [Finset.union_sdiff_of_subset (hsubA0 Y hY i)]
    rw [hx, hy, hXY]
  have himage : (Finset.univ.filter (fun X : Fin r → Finset α => IsSS k X)).image F ⊆
      Finset.univ.filter (fun p : Finset α × (Fin r → Finset α) => C p) := by
    intro p hp
    obtain ⟨X, hXm, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_filter] at hXm
    have hX : IsSS k X := hXm.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    dsimp only [C, F]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc (X i0 ∩ X i1).card ≤ (X i0).card := Finset.card_le_card Finset.inter_subset_left
        _ = k := hX.card_eq i0
    · intro i x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩
    · intro i
      rw [Finset.card_sdiff_of_subset (hsubA0 X hX i), hX.card_eq i]
    · intro i j hij
      obtain ⟨-, A₀c, hsubc, hint⟩ := hX
      have hA0 : X i0 ∩ X i1 = A₀c := hint i0 i1 hi
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_sdiff] at hx1 hx2
      obtain ⟨hxi, hxA⟩ := hx1
      obtain ⟨hxj, -⟩ := hx2
      refine hxA ?_
      rw [hA0, ← hint i j hij]
      exact Finset.mem_inter.mpr ⟨hxi, hxj⟩
  have hLHS_eq : (∑ X : Fin r → Finset α, if IsSS k X then ∏ i, w (X i) else 0)
      = ∑ X ∈ Finset.univ.filter (fun X : Fin r → Finset α => IsSS k X), g (F X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro X _
    by_cases hX : IsSS k X
    · rw [if_pos hX, if_pos hX]
      exact (hgeq X hX).symm
    · rw [if_neg hX, if_neg hX]
  have hRHS : (∑ A₀ : Finset α, if A₀.card ≤ k then
        ∑ A : Fin r → Finset α,
          (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (A i) (A j))
           then ∏ i, w (A₀ ∪ A i) else 0) else 0)
      = ∑ p : Finset α × (Fin r → Finset α), if C p then g p else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro A₀ _
    by_cases hc : A₀.card ≤ k
    · rw [if_pos hc]
      apply Finset.sum_congr rfl
      intro A _
      dsimp only [C, g]
      by_cases hv : (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (A i) (A j))
      · rw [if_pos hv, if_pos ⟨hc, hv⟩]
      · rw [if_neg hv, if_neg (fun h => hv h.2)]
    · rw [if_neg hc]
      symm
      apply Finset.sum_eq_zero
      intro A _
      dsimp only [C, g]
      rw [if_neg (fun h => hc h.1)]
  calc (∑ X : Fin r → Finset α, if IsSS k X then ∏ i, w (X i) else 0)
      = ∑ X ∈ Finset.univ.filter (fun X : Fin r → Finset α => IsSS k X), g (F X) := hLHS_eq
    _ = ∑ p ∈ (Finset.univ.filter (fun X : Fin r → Finset α => IsSS k X)).image F, g p :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Finset α × (Fin r → Finset α) => C p), g p :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (fun p _ _ => zero_le)
    _ = (∑ A₀ : Finset α, if A₀.card ≤ k then
          ∑ A : Fin r → Finset α,
            (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                (∀ i j, i ≠ j → Disjoint (A i) (A j))
             then ∏ i, w (A₀ ∪ A i) else 0) else 0) := by
        rw [Finset.sum_filter]
        exact hRHS.symm

end Work.BourgainPlan.IonescuWainger
