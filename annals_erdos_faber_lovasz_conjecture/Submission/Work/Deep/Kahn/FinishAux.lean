import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.FinishSetup

/-!
# The finishing step of Kahn's theorem: the neighbourhood estimates

This module contains the `Finset` bookkeeping of the LLL application in
`Work.Deep.Kahn.finishing_step`: the neighbourhood sums of the bad events
attached to the pairs of meeting edges.

The key point is that the neighbours of the index `i = {e, f}` are the indices
sharing one of the two edges, and the sum of the potentials `badX` over them is
at most `1/2`: each such index is covered by one of the two families
`{j : j.1.1 = g}` (`g` running over the two edges of `i`), and each of those
families has potential-sum at most `1/4` because the map `j ↦ j.1.2` is
injective on it and its image lies in the edges meeting `g`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ}

/-- **Union bound for sums of nonnegative terms.** -/
lemma sum_union_le' {α : Type*} [DecidableEq α] (s t : Finset α) (g : α → ℝ)
    (h : ∀ y, 0 ≤ g y) : ∑ y ∈ s ∪ t, g y ≤ ∑ y ∈ s, g y + ∑ y ∈ t, g y := by
  have hEq : s ∪ t = s ∪ (t \ s) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hEq, Finset.sum_union Finset.disjoint_sdiff]
  have hle : ∑ y ∈ t \ s, g y ≤ ∑ y ∈ t, g y :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun y _ _ => h y)
  linarith

/-- No edge of an index `j` that is not a neighbour of `i` is an edge of `i`. -/
lemma coords_of_not_mem_Dep {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    {i j : BadIdx 𝓗} (hji : j ≠ i) (hj : j ∉ Dep 𝓗 i) :
    j.1.1 ∉ ({i.1.1, i.1.2} : Finset 𝓗) ∧ j.1.2 ∉ ({i.1.1, i.1.2} : Finset 𝓗) := by
  classical
  constructor
  · intro hmem
    exact hj (mem_Dep_iff.mpr ⟨hji, Or.inl hmem⟩)
  · intro hmem
    exact hj (mem_Dep_iff.mpr ⟨hji, Or.inr hmem⟩)

/-- **The potential summed over the pairs through a fixed edge is at most `1/8`.**
The index set is that of `BadIdx` (canonically ordered pairs of distinct meeting
edges) and the potential of an index is `badWeight`. -/
lemma sum_badWeight_through_le (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    [Fintype 𝓗] (L : 𝓗 → Finset (Fin c)) (hs : ∀ e : 𝓗,
      ∑ f ∈ (Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
          (verts (f : Set (Fin n)) ∩ verts (e : Set (Fin n))).Nonempty)),
        (((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ))) ≤ 1 / 8) (g : 𝓗) :
    ∑ j ∈ (Finset.univ.filter (fun j : BadIdx 𝓗 => g ∈ ({j.1.1, j.1.2} : Finset 𝓗))),
      badWeight L j ≤ 1 / 8 := by
  classical
  set T : Finset 𝓗 := Finset.univ.filter (fun f : 𝓗 => f ≠ g ∧
      (verts (f : Set (Fin n)) ∩ verts (g : Set (Fin n))).Nonempty) with hT
  set pf : 𝓗 → ℝ := fun f =>
    (((L g ∩ L f).card : ℝ) / (((L g).card : ℝ) * ((L f).card : ℝ))) with hpf
  set A : Finset (BadIdx 𝓗) :=
    Finset.univ.filter (fun j : BadIdx 𝓗 => j.1.1 = g) with hA
  set B : Finset (BadIdx 𝓗) :=
    Finset.univ.filter (fun j : BadIdx 𝓗 => j.1.2 = g) with hB
  have hSAB : (Finset.univ.filter (fun j : BadIdx 𝓗 => g ∈ ({j.1.1, j.1.2} : Finset 𝓗)))
      = A ∪ B := by
    ext j
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [hSAB]
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    exact j.2.1 (hjA.trans hjB.symm)
  have hinjA : ∀ x ∈ A, ∀ y ∈ A, x.1.2 = y.1.2 → x = y := by
    intro x hxA y hyA hxy
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hxA hyA
    exact Subtype.ext (Prod.ext (hxA.trans hyA.symm) hxy)
  have hinjB : ∀ x ∈ B, ∀ y ∈ B, x.1.1 = y.1.1 → x = y := by
    intro x hxB y hyB hxy
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hxB hyB
    exact Subtype.ext (Prod.ext hxy (hxB.trans hyB.symm))
  have hAeq : ∑ j ∈ A, badWeight L j = ∑ h ∈ A.image (fun j : BadIdx 𝓗 => j.1.2), pf h := by
    have h1 : ∑ j ∈ A, badWeight L j = ∑ j ∈ A, pf j.1.2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [hpf, badWeight, hj]
    rw [h1, ← Finset.sum_image hinjA]
  have hBeq : ∑ j ∈ B, badWeight L j = ∑ h ∈ B.image (fun j : BadIdx 𝓗 => j.1.1), pf h := by
    have h1 : ∑ j ∈ B, badWeight L j = ∑ j ∈ B, pf j.1.1 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have h2 : badWeight L j =
          ((L j.1.1 ∩ L g).card : ℝ) / (((L j.1.1).card : ℝ) * ((L g).card : ℝ)) := by
        unfold badWeight
        rw [hj]
      rw [h2]
      simp only [hpf]
      rw [Finset.inter_comm (L j.1.1) (L g),
        mul_comm ((L j.1.1).card : ℝ) ((L g).card : ℝ)]
    rw [h1, ← Finset.sum_image hinjB]
  have hdisjρ : Disjoint (A.image (fun j : BadIdx 𝓗 => j.1.2))
      (B.image (fun j : BadIdx 𝓗 => j.1.1)) := by
    rw [Finset.disjoint_left]
    intro h hhA hhB
    rw [Finset.mem_image] at hhA hhB
    obtain ⟨j, hjA, hjv⟩ := hhA
    obtain ⟨j', hjB, hj'v⟩ := hhB
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    have h1 : edgeRank 𝓗 g < edgeRank 𝓗 h := by
      have hh := j.2.2.2
      rw [hjA, hjv] at hh
      exact hh
    have h2 : edgeRank 𝓗 h < edgeRank 𝓗 g := by
      have hh := j'.2.2.2
      rw [hj'v, hjB] at hh
      exact hh
    exact absurd (h1.trans h2) (lt_irrefl _)
  have hρsub : (A.image (fun j : BadIdx 𝓗 => j.1.2))
      ∪ (B.image (fun j : BadIdx 𝓗 => j.1.1)) ⊆ T := by
    intro h hh
    rw [Finset.mem_union] at hh
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ h, ?_, ?_⟩
    · rcases hh with hh | hh
      · rw [Finset.mem_image] at hh
        obtain ⟨j, hjA, hjv⟩ := hh
        simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
        rw [← hjv]
        exact fun hcon => j.2.1 (hjA.trans hcon.symm)
      · rw [Finset.mem_image] at hh
        obtain ⟨j, hjB, hjv⟩ := hh
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
        rw [← hjv]
        exact fun hcon => j.2.1 (hcon.trans hjB.symm)
    · rcases hh with hh | hh
      · rw [Finset.mem_image] at hh
        obtain ⟨j, hjA, hjv⟩ := hh
        simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
        have hmem := j.2.2.1
        rw [hjA, hjv] at hmem
        rwa [Finset.inter_comm]
      · rw [Finset.mem_image] at hh
        obtain ⟨j, hjB, hjv⟩ := hh
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
        have hmem := j.2.2.1
        rw [hjv, hjB] at hmem
        exact hmem
  calc ∑ j ∈ A ∪ B, badWeight L j
      = (∑ j ∈ A, badWeight L j) + (∑ j ∈ B, badWeight L j) := Finset.sum_union hdisjAB
    _ = (∑ h ∈ A.image (fun j : BadIdx 𝓗 => j.1.2), pf h)
          + (∑ h ∈ B.image (fun j : BadIdx 𝓗 => j.1.1), pf h) := by rw [hAeq, hBeq]
    _ = ∑ h ∈ (A.image (fun j : BadIdx 𝓗 => j.1.2))
            ∪ (B.image (fun j : BadIdx 𝓗 => j.1.1)), pf h := (Finset.sum_union hdisjρ).symm
    _ ≤ ∑ h ∈ T, pf h :=
        Finset.sum_le_sum_of_subset_of_nonneg hρsub (fun h _ _ => by positivity)
    _ ≤ 1 / 8 := by
        rw [hT, hpf]
        exact hs g

/-- **The potential summed over the neighbours of an index is at most `1/2`.** -/
lemma sum_badX_Dep_le (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    [Fintype 𝓗] (L : 𝓗 → Finset (Fin c)) (hs : ∀ e : 𝓗,
      ∑ f ∈ (Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
          (verts (f : Set (Fin n)) ∩ verts (e : Set (Fin n))).Nonempty)),
        (((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ))) ≤ 1 / 8) (i : BadIdx 𝓗) :
    ∑ j ∈ Dep 𝓗 i, badX L j ≤ 1 / 2 := by
  classical
  have h2 : ∑ j ∈ Dep 𝓗 i, badX L j = 2 * ∑ j ∈ Dep 𝓗 i, badWeight L j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => badX_eq L j
  rw [h2]
  have hcover : ∑ j ∈ Dep 𝓗 i, badWeight L j ≤
      ∑ g ∈ ({i.1.1, i.1.2} : Finset 𝓗),
        ∑ j ∈ (Dep 𝓗 i).filter (fun j => g ∈ ({j.1.1, j.1.2} : Finset 𝓗)),
          badWeight L j := by
    calc ∑ j ∈ Dep 𝓗 i, badWeight L j
        ≤ ∑ j ∈ Dep 𝓗 i, ∑ g ∈ ({i.1.1, i.1.2} : Finset 𝓗),
            (if g ∈ ({j.1.1, j.1.2} : Finset 𝓗) then badWeight L j else 0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := mem_Dep_iff.mp hj
          have hmem : ∃ g ∈ ({i.1.1, i.1.2} : Finset 𝓗),
              g ∈ ({j.1.1, j.1.2} : Finset 𝓗) := by
            rcases hj'.2 with h | h
            · exact ⟨j.1.1, h, by simp⟩
            · exact ⟨j.1.2, h, by simp⟩
          obtain ⟨g, hg1, hg2⟩ := hmem
          refine le_trans (le_of_eq ?_)
            (Finset.single_le_sum (fun g' _ => ?_) hg1)
          · simp only [if_pos hg2]
          · by_cases h : g' ∈ ({j.1.1, j.1.2} : Finset 𝓗)
            · simp only [if_pos h]
              exact badWeight_nonneg L j
            · simp only [if_neg h]
              norm_num
      _ = ∑ g ∈ ({i.1.1, i.1.2} : Finset 𝓗), ∑ j ∈ Dep 𝓗 i,
            (if g ∈ ({j.1.1, j.1.2} : Finset 𝓗) then badWeight L j else 0) :=
          Finset.sum_comm
      _ = ∑ g ∈ ({i.1.1, i.1.2} : Finset 𝓗),
            ∑ j ∈ (Dep 𝓗 i).filter (fun j => g ∈ ({j.1.1, j.1.2} : Finset 𝓗)),
              badWeight L j := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_filter]
  have hinner : ∀ g ∈ ({i.1.1, i.1.2} : Finset 𝓗),
      ∑ j ∈ (Dep 𝓗 i).filter (fun j => g ∈ ({j.1.1, j.1.2} : Finset 𝓗)),
        badWeight L j ≤ 1 / 8 := by
    intro g _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun j _ _ => badWeight_nonneg L j)) (sum_badWeight_through_le 𝓗 L hs g)
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ j, hj.2⟩
  calc 2 * ∑ j ∈ Dep 𝓗 i, badWeight L j
      ≤ 2 * ∑ g ∈ ({i.1.1, i.1.2} : Finset 𝓗),
          ∑ j ∈ (Dep 𝓗 i).filter (fun j => g ∈ ({j.1.1, j.1.2} : Finset 𝓗)),
            badWeight L j := mul_le_mul_of_nonneg_left hcover (by norm_num)
    _ ≤ 2 * ∑ g ∈ ({i.1.1, i.1.2} : Finset 𝓗), (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by norm_num)
    _ = 2 * ((({i.1.1, i.1.2} : Finset 𝓗).card : ℝ) * (1 / 8)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 / 2 := by
        have hcard : (({i.1.1, i.1.2} : Finset 𝓗).card : ℝ) ≤ 2 := by
          rw [Finset.card_pair i.2.1]
          norm_num
        nlinarith

end

end Work.Deep.Kahn
