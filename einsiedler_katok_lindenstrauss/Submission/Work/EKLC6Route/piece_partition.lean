import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.firstReturn_partition

namespace Work.EKLC6Route

open MeasureTheory Set
open Work.EKLContract Work.EKLC6Core

/-- For a point of `C 0` under a sequence of sets, either the point lies in every `C i` or it lies
in some difference `C j \ C (j+1)`. -/
theorem mem_iInter_or_mem_diff {α : Type*} {C : ℕ → Set α} {y : α} (h0 : y ∈ C 0) :
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

namespace Window

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ} (w : Window μ t)

lemma Jset_subset_W (J : Option ℕ) : w.Jset J ⊆ w.W := by
  rcases J with _ | j
  · intro x hx; exact hx.1
  · intro x hx; exact hx.1

lemma Jset_disjoint (J J' : Option ℕ) (hne : J ≠ J') : Disjoint (w.Jset J) (w.Jset J') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases J with _ | j
  · rcases J' with _ | j'
    · exact absurd rfl hne
    · exact hx'.2.2 (Set.mem_iInter.1 hx.2 (j' + 1))
  · rcases J' with _ | j'
    · exact hx.2.2 (Set.mem_iInter.1 hx'.2 (j + 1))
    · have hjj' : j ≠ j' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hjj' with h | h
      · exact hx.2.2 (w.hCanti (by omega : j + 1 ≤ j') hx'.2.1)
      · exact hx'.2.2 (w.hCanti (by omega : j' + 1 ≤ j) hx.2.1)

lemma Jset_union : (⋃ J : Option ℕ, w.Jset J) = w.W := by
  apply Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨J, hJ⟩ := hx
    exact w.Jset_subset_W J hJ
  · intro x hx
    rw [Set.mem_iUnion]
    have hθC0 : w.θ x ∈ w.C 0 := by rw [w.hC0]; exact hx.2.1
    rcases mem_iInter_or_mem_diff hθC0 with hall | ⟨j, hj, hjn⟩
    · exact ⟨none, hx, Set.mem_iInter.2 hall⟩
    · exact ⟨some j, hx, hj, hjn⟩

lemma mem_D {i : ℕ} {J : Option ℕ} {c : Fin 3 → Fin 3 → ℤ} {x : X3} :
    x ∈ w.D i J c ↔ i ≠ 0 ∧ x ∈ firstReturnSet t w.W i ∧ x ∈ w.Jset J ∧
      gridIdx w.ρ (gridLev t i) (w.θ x) = c ∧ x ∉ w.N0 := by
  classical
  simp only [Window.D]
  by_cases hi : i = 0
  · rw [if_pos hi]; simp [hi]
  · rw [if_neg hi]
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨hA, hB⟩, hc⟩, hN⟩
      exact ⟨hi, hA, hB, hc, hN⟩
    · rintro ⟨-, hA, hB, hc, hN⟩
      exact ⟨⟨⟨hA, hB⟩, hc⟩, hN⟩

lemma piece_some_subset (q : Option (ℕ × Option ℕ × (Fin 3 → Fin 3 → ℤ))) :
    w.piece (some q) ⊆ w.W ∪ w.N0 := by
  rcases q with _ | ⟨i, J, c⟩
  · intro y hy; exact Or.inr hy
  · intro y hy
    exact Or.inl ((w.mem_D).1 hy).2.1.1.1

lemma N0_disjoint_D (i : ℕ) (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ) :
    Disjoint w.N0 (w.D i J c) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  exact ((w.mem_D).1 hy').2.2.2.2 hy

lemma D_disjoint (hW : MeasurableSet w.W) {i i' : ℕ} {J J' : Option ℕ}
    {c c' : Fin 3 → Fin 3 → ℤ} (h : (i, J, c) ≠ (i', J', c')) :
    Disjoint (w.D i J c) (w.D i' J' c') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨hi0, hyi, hyJ, hyg, -⟩ := (w.mem_D).1 hy
  obtain ⟨hi0', hyi', hyJ', hyg', -⟩ := (w.mem_D).1 hy'
  by_cases hii : i = i'
  · subst hii
    by_cases hJJ : J = J'
    · subst hJJ
      have hcc : c ≠ c' := fun hcc => h (by rw [hcc])
      exact hcc (hyg.symm.trans hyg')
    · exact (Set.disjoint_left.1 (w.Jset_disjoint J J' hJJ)) hyJ hyJ'
  · have h1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 hi0
    have h1' : 1 ≤ i' := Nat.one_le_iff_ne_zero.2 hi0'
    have hdisj :=
      (Work.EKLC6Core.firstReturn_partition (t := t) (Ω := w.W) hW).2.2.1 i i' h1 h1' hii
    exact (Set.disjoint_left.1 hdisj) hyi hyi'

end Window

/-- The family `piece` of the window is a partition of `X₃`: its members are pairwise disjoint and
their union is everything.  The members are `(W ∪ N0)ᶜ`, `N0`, and the `D i J c`; the content is
(a) the `firstReturnSet t W i` (`i ≥ 1`) together with `neverReturnSet t W` partition `W`
(`Work.EKLC6Core.firstReturn_partition hW`), (b) the `Jset J` partition `W` (using `hC0 : C 0 = VtSet t ∩ V ρ`
— every `x ∈ W` has `θ x ∈ C 0` — and `Antitone C`), (c) the grid classes
`{x | gridIdx ρ (gridLev t i) (θ x) = c}` partition by values of a function, and (d) `D i J c = ∅`
for `i = 0` and `D i J c ∩ N0 = ∅`.  The hypothesis `hW : MeasurableSet w.W` is only used to
invoke `firstReturn_partition`. -/
theorem piece_partition {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    (hW : MeasurableSet w.W) :
    (∀ p q : Work.EKLC6Route.Window.PIdx, p ≠ q → Disjoint (w.piece p) (w.piece q)) ∧
    (⋃ p : Work.EKLC6Route.Window.PIdx, w.piece p) = Set.univ := by
  classical
  have hfr := Work.EKLC6Core.firstReturn_partition (t := t) (Ω := w.W) hW
  constructor
  · intro p q hpq
    rcases p with _ | p
    · rcases q with _ | q
      · exact (hpq rfl).elim
      · rw [Set.disjoint_left]
        intro y hy hy'
        exact hy (w.piece_some_subset q hy')
    · rcases q with _ | q
      · rw [Set.disjoint_left]
        intro y hy hy'
        exact hy' (w.piece_some_subset p hy)
      · rcases p with _ | p
        · rcases q with _ | q
          · exact (hpq rfl).elim
          · rcases q with ⟨i, J, c⟩
            exact w.N0_disjoint_D i J c
        · rcases q with _ | q
          · rcases p with ⟨i, J, c⟩
            exact (w.N0_disjoint_D i J c).symm
          · rcases p with ⟨i, J, c⟩
            rcases q with ⟨i', J', c'⟩
            have hne : (i, J, c) ≠ (i', J', c') := fun hc => hpq (by rw [hc])
            exact w.D_disjoint hW hne
  · rw [Set.iUnion_eq_univ_iff]
    intro x
    by_cases hxN : x ∈ w.N0
    · exact ⟨some none, hxN⟩
    · by_cases hxW : x ∈ w.W
      · have hx' : x ∈ (⋃ i ∈ {i : ℕ | 1 ≤ i}, firstReturnSet t w.W i) ∪
            neverReturnSet t w.W := by
          rw [← hfr.2.2.2.1]; exact hxW
        have hxJW : x ∈ ⋃ J : Option ℕ, w.Jset J := by rw [w.Jset_union]; exact hxW
        rw [Set.mem_iUnion] at hxJW
        obtain ⟨J, hxJ⟩ := hxJW
        rcases hx' with h | h
        · rw [Set.mem_iUnion₂] at h
          obtain ⟨i, hi, hxi⟩ := h
          refine ⟨some (some (i, J, gridIdx w.ρ (gridLev t i) (w.θ x))), ?_⟩
          show x ∈ w.D i J (gridIdx w.ρ (gridLev t i) (w.θ x))
          rw [w.mem_D]
          exact ⟨Nat.one_le_iff_ne_zero.1 hi, hxi, hxJ, rfl, hxN⟩
        · exact absurd (Or.inl h) hxN
      · exact ⟨none, fun h => h.elim hxW hxN⟩

end Work.EKLC6Route
