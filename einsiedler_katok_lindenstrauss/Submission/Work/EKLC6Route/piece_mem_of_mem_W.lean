import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

open MeasureTheory Set
open Work.EKLContract Work.EKLC6Core

/-- Unfolding of the never-returning set: `z` never comes back to `Ω` at any positive time. -/
private theorem mem_neverReturnSet_iff_aux {t : Fin 3 → ℝ} {Ω : Set X3} {z : X3} :
    z ∈ neverReturnSet t Ω ↔ z ∈ Ω ∧ ∀ j : ℕ, 1 ≤ j →
      ((fun y : X3 => aDiag t • y)^[j]) z ∉ Ω := by
  simp only [neverReturnSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_compl_iff, Set.mem_ofPred_eq]

/-- Unfolding of the `i`-th first-return set. -/
private theorem mem_firstReturnSet_iff_aux {t : Fin 3 → ℝ} {Ω : Set X3} {i : ℕ} {z : X3} :
    z ∈ firstReturnSet t Ω i ↔ z ∈ Ω ∧ ((fun y : X3 => aDiag t • y)^[i]) z ∈ Ω ∧
      ∀ j : ℕ, 1 ≤ j → j < i → ((fun y : X3 => aDiag t • y)^[j]) z ∉ Ω := by
  simp only [firstReturnSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
    Set.mem_compl_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun j hj hji => h3 j ⟨hj, by omega⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun j ⟨hj1, hj2⟩ => h3 j hj1 (by omega)⟩

/-- A point of `Ω` that is not in the never-returning set returns to `Ω` for the first time at
some positive time. -/
private theorem exists_firstReturnSet_of_mem_of_notMem {t : Fin 3 → ℝ} {Ω : Set X3} {z : X3}
    (hzΩ : z ∈ Ω) (hzN : z ∉ neverReturnSet t Ω) :
    ∃ i : ℕ, 1 ≤ i ∧ z ∈ firstReturnSet t Ω i := by
  classical
  have hne : ∃ i : ℕ, 1 ≤ i ∧ ((fun y : X3 => aDiag t • y)^[i]) z ∈ Ω := by
    by_contra h
    exact hzN (mem_neverReturnSet_iff_aux.2 ⟨hzΩ, fun j hj hmem => h ⟨j, hj, hmem⟩⟩)
  refine ⟨Nat.find hne, (Nat.find_spec hne).1, ?_⟩
  rw [mem_firstReturnSet_iff_aux]
  exact ⟨hzΩ, (Nat.find_spec hne).2, fun j hj hji hmem => Nat.find_min hne hji ⟨hj, hmem⟩⟩

/-- A point of `C 0` either lies in every `C i` or in some difference `C j \ C (j+1)`. -/
private theorem mem_iInter_or_mem_diff_aux {α : Type*} {C : ℕ → Set α} {y : α} (h0 : y ∈ C 0) :
    (∀ i, y ∈ C i) ∨ ∃ j, y ∈ C j ∧ y ∉ C (j + 1) := by
  classical
  by_cases h : ∃ j, y ∉ C (j + 1)
  · right
    refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
    cases hf : Nat.find h with
    | zero => exact h0
    | succ k =>
      have hk : k < Nat.find h := by rw [hf]; exact Nat.lt_succ_self k
      have hy : y ∈ C (k + 1) := by
        by_contra hy'
        exact Nat.find_min h hk hy'
      exact hy
  · left
    intro i
    cases i with
    | zero => exact h0
    | succ k =>
      by_contra hk
      exact h ⟨k, hk⟩

theorem piece_mem_of_mem_W {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) {z : Work.EKLContract.X3} (hzW : z ∈ w.W) (hzN : z ∉ w.N0) :
    ∃ (i : ℕ) (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ), 1 ≤ i ∧
      z ∈ Work.EKLC6Core.firstReturnSet t w.W i ∧ z ∈ w.Jset J ∧
      Work.EKLC6Route.gridIdx w.ρ (Work.EKLC6Route.gridLev t i) (w.θ z) = c ∧
      z ∈ w.piece (some (some (i, J, c))) := by
  classical
  -- `z` is not in the never-returning set, so it first returns at some positive time `i`
  have hzN' : z ∉ neverReturnSet t w.W := fun h => hzN (Or.inl h)
  obtain ⟨i, hi1, hzi⟩ := exists_firstReturnSet_of_mem_of_notMem hzW hzN'
  -- `θ z ∈ C 0`, so `z` lies in one of the sets `Jset J`
  have hθC0 : w.θ z ∈ w.C 0 := by rw [w.hC0]; exact hzW.2.1
  have hJ : ∃ J : Option ℕ, z ∈ w.Jset J := by
    rcases mem_iInter_or_mem_diff_aux hθC0 with hall | ⟨j, hj, hjn⟩
    · exact ⟨none, hzW, Set.mem_iInter.2 hall⟩
    · exact ⟨some j, hzW, hj, hjn⟩
  obtain ⟨J, hzJ⟩ := hJ
  refine ⟨i, J, gridIdx w.ρ (gridLev t i) (w.θ z), hi1, hzi, hzJ, rfl, ?_⟩
  -- membership in the piece `D i J c`, the grid label `c` being the one of `z`
  show z ∈ w.D i J (gridIdx w.ρ (gridLev t i) (w.θ z))
  rw [Window.D, if_neg (Nat.one_le_iff_ne_zero.mp hi1)]
  exact ⟨⟨⟨hzi, hzJ⟩, rfl⟩, hzN⟩

end Work.EKLC6Route
