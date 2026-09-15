import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Combinatorics.Transference

theorem sum_biUnion_small_atoms {X : Type*} [Fintype X] [DecidableEq X] (part : X → Finset X)
    (hmem : ∀ x, x ∈ part x) (heq : ∀ x y : X, y ∈ part x → part y = part x) (ν : X → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {η : ℝ} (hη : 0 ≤ η) :
    ∑ x ∈ ((Finset.univ.image part).filter (fun A => ∑ y ∈ A, (ν y + 1) ≤ η)).biUnion
        (fun A => A), (ν x + 1)
      ≤ η * ((Finset.univ.image part).card : ℝ) := by
  set P : Finset (Finset X) := Finset.univ.image part with hP
  set S : Finset (Finset X) := P.filter (fun A => ∑ y ∈ A, (ν y + 1) ≤ η) with hS
  -- The atoms appearing in `S` are pairwise disjoint.
  have hdisj : (S : Set (Finset X)).PairwiseDisjoint (fun A : Finset X => A) := by
    intro A hA B hB hne
    change Disjoint A B
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hA' : A ∈ P := (Finset.mem_filter.mp (Finset.mem_coe.mp hA)).1
    have hB' : B ∈ P := (Finset.mem_filter.mp (Finset.mem_coe.mp hB)).1
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (show A ∈ Finset.univ.image part from hP ▸ hA')
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp (show B ∈ Finset.univ.image part from hP ▸ hB')
    -- ha : part a = A, hb : part b = B
    have hza : z ∈ part a := ha ▸ hzA
    have hzb : z ∈ part b := hb ▸ hzB
    have hpa : part z = part a := heq a z hza
    have hpb : part z = part b := heq b z hzb
    apply hne
    rw [← ha, ← hb, ← hpb, hpa]
  rw [Finset.sum_biUnion hdisj]
  calc ∑ A ∈ S, ∑ y ∈ A, (ν y + 1)
      ≤ ∑ A ∈ S, η := by
        apply Finset.sum_le_sum
        intro A hA
        exact (Finset.mem_filter.mp hA).2
    _ = S.card • η := Finset.sum_const η
    _ = (S.card : ℝ) * η := by rw [nsmul_eq_mul]
    _ ≤ (P.card : ℝ) * η := by
        apply mul_le_mul_of_nonneg_right _ hη
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = η * (P.card : ℝ) := by ring

end Commons.Combinatorics.Transference