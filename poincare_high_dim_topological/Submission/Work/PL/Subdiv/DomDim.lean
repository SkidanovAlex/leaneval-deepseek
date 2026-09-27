import Submission.Work.PL.Subdiv.Defs

/-!
# The DomDim API (Newman's "dimension ≤ d", blueprint D7)

`PL.DomDim A d` means: `A` is covered by finitely many simplices each having at most `d + 1`
vertices.  This file collects the basic calculus; preservation under injective affine maps
(`domDim_affine_image`) lives in `Submission.Work.PL.Subdiv.DomDim.domDim_affine_image`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

theorem domDim_mono {m : ℕ} {A B : Set (E m)} {d : ℤ} (h : DomDim A d) (hAB : B ⊆ A) :
    DomDim B d := by
  obtain ⟨S, hS, hsub⟩ := h
  exact ⟨S, hS, hAB.trans hsub⟩

theorem domDim_empty {m : ℕ} (d : ℤ) : DomDim (∅ : Set (E m)) d :=
  ⟨∅, by simp, by simp⟩

theorem domDim_simp {m : ℕ} (s : Finset (E m)) : DomDim (simp s) ((s.card : ℤ) - 1) := by
  refine ⟨{s}, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    rw [ht]
    omega
  · intro x hx
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_singleton_self s, hx⟩

theorem domDim_union {m : ℕ} {A B : Set (E m)} {d : ℤ} (hA : DomDim A d) (hB : DomDim B d) :
    DomDim (A ∪ B) d := by
  obtain ⟨S, hS, hsub⟩ := hA
  obtain ⟨T, hT, hsub'⟩ := hB
  refine ⟨S ∪ T, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact hS s h
    · exact hT s h
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hsub hx)
      exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_union_left T hs, hxs⟩
    · obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hsub' hx)
      exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_union_right S hs, hxs⟩

theorem domDim_finite_biUnion {m : ℕ} {ι : Type*} (t : Finset ι) (A : ι → Set (E m)) (d : ℤ)
    (h : ∀ i ∈ t, DomDim (A i) d) : DomDim (⋃ i ∈ t, A i) d := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using domDim_empty (m := m) d
  | insert a t ha ih =>
    have hsplit : (⋃ i ∈ insert a t, A i) = A a ∪ ⋃ i ∈ t, A i := by
      ext x
      simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi | hi, hx⟩
        · exact Or.inl (hi ▸ hx)
        · exact Or.inr ⟨i, hi, hx⟩
      · rintro (hx | ⟨i, hi, hx⟩)
        · exact ⟨a, Or.inl rfl, hx⟩
        · exact ⟨i, Or.inr hi, hx⟩
    rw [hsplit]
    exact domDim_union (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isClosed_biUnion_simp {m : ℕ} (S : Finset (Finset (E m))) :
    IsClosed (⋃ s ∈ S, simp s) := by
  refine isClosed_biUnion_finset ?_
  intro s _
  exact Set.Finite.isClosed_convexHull (𝕜 := ℝ) (Finset.finite_toSet s)

theorem eq_empty_of_domDim_neg {m : ℕ} {A : Set (E m)} {d : ℤ} (hd : d < 0) (h : DomDim A d) :
    A = ∅ := by
  obtain ⟨S, hS, hsub⟩ := h
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hsub hx)
  have hle : (s.card : ℤ) ≤ 0 := by have := hS s hs; omega
  have hcard : s.card = 0 := by omega
  rw [Finset.card_eq_zero.mp hcard] at hxs
  simp [PL.simp] at hxs

theorem domDim_singleton {m : ℕ} (x : E m) {d : ℤ} (hd : 0 ≤ d) :
    DomDim ({x} : Set (E m)) d := by
  refine ⟨{({x} : Finset (E m))}, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    rw [ht]
    simp only [Finset.card_singleton, Nat.cast_one]
    omega
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Set.mem_iUnion₂.mpr ⟨({x} : Finset (E m)), Finset.mem_singleton_self _,
      subset_convexHull ℝ _ (Finset.mem_singleton_self x)⟩

end Work.PL.Subdiv
