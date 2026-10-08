import Mathlib
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coherence

/-- **Combinatorial core.**  Four elements of an arbitrary type with `x1 ≠ y1` whose four
indicator values satisfy the numerical relation forced by the hypothesis
`cfInner (ψ i - ψ' i) (ψ j - ψ' j) = 1`.

Here `[x1 = x2] - [y1 = x2] - ([x1 = y2] - [y1 = y2]) = 1` (with `[·]` the `{0,1}`-valued
indicator), which is exactly the expansion of `⟨x1 - y1, x2 - y2⟩ = 1` when the four elements
are pairwise orthonormal.  The conclusion is that exactly one of `x1 = x2`, `y1 = y2` holds. -/
private lemma ite_inner_key {α : Type*} [DecidableEq α] {x1 x2 y1 y2 : α}
    (h1 : x1 ≠ y1)
    (h : ((if x1 = x2 then (1:ℂ) else 0) - (if y1 = x2 then (1:ℂ) else 0))
       - ((if x1 = y2 then (1:ℂ) else 0) - (if y1 = y2 then (1:ℂ) else 0)) = 1) :
    (x1 = x2 ∨ y1 = y2) ∧ ¬(x1 = x2 ∧ y1 = y2) := by
  constructor
  · by_contra hc
    rw [not_or] at hc
    obtain ⟨hA, hD⟩ := hc
    rw [ite_eq_right hA, ite_eq_right hD] at h
    by_cases hB : x1 = y2
    · rw [ite_eq_left hB] at h
      by_cases hC : y1 = x2
      · rw [ite_eq_left hC] at h; norm_num at h
      · rw [ite_eq_right hC] at h; norm_num at h
    · rw [ite_eq_right hB] at h
      by_cases hC : y1 = x2
      · rw [ite_eq_left hC] at h; norm_num at h
      · rw [ite_eq_right hC] at h; norm_num at h
  · rintro ⟨hA, hD⟩
    rw [ite_eq_left hA, ite_eq_left hD] at h
    by_cases hB : x1 = y2
    · rw [ite_eq_left hB] at h
      by_cases hC : y1 = x2
      · rw [ite_eq_left hC] at h; norm_num at h
      · exact absurd (hB.trans hD.symm) h1
    · rw [ite_eq_right hB] at h
      by_cases hC : y1 = x2
      · exact absurd (hA.trans hC.symm) h1
      · rw [ite_eq_right hC] at h; norm_num at h

/-- If `T` is an orthonormal set of functions on a finite group, and for every index `i` we have
`ψ i, ψ' i ∈ T` with `ψ i ≠ ψ' i`, and `cfInner (ψ i - ψ' i) (ψ j - ψ' j) = 1` for all `i ≠ j`,
then one of the two families is constant with the same value in `T` — provided there are at least
three indices.

Indeed `⟨ψ i - ψ' i, ψ j - ψ' j⟩ = [ψ i = ψ j] - [ψ' i = ψ j] - ([ψ i = ψ' j] - [ψ' i = ψ' j])`,
so for `i ≠ j` exactly one of `ψ i = ψ j`, `ψ' i = ψ' j` holds.  Transitivity of equality then
shows that if some pair `ψ i = ψ j` (`i ≠ j`) exists, all the `ψ i` coincide, and otherwise all
the `ψ' i` coincide. -/
theorem exists_common_of_pairwise_inner_one {G : Type*} [Group G] [Fintype G]
    {T : Finset (G → ℂ)} (hT : Orthonormal T) {ι : Type*} [Fintype ι] (ψ ψ' : ι → G → ℂ)
    (hψ : ∀ i, ψ i ∈ T) (hψ' : ∀ i, ψ' i ∈ T)
    (hne : ∀ i, ψ i ≠ ψ' i)
    (horth : ∀ i j, i ≠ j → cfInner (ψ i - ψ' i) (ψ j - ψ' j) = 1)
    (hι : 3 ≤ Fintype.card ι) :
    ∃ Ψ ∈ T, (∀ i, ψ i = Ψ) ∨ (∀ i, ψ' i = Ψ) := by
  classical
  -- For `i ≠ j` exactly one of `ψ i = ψ j` and `ψ' i = ψ' j` holds.
  have hpair : ∀ i j, i ≠ j → (ψ i = ψ j ∨ ψ' i = ψ' j) ∧
      ¬(ψ i = ψ j ∧ ψ' i = ψ' j) := by
    intro i j hij
    have h := horth i j hij
    rw [cfInner_sub_right, cfInner_sub_left, cfInner_sub_left,
        hT (ψ i) (hψ i) (ψ j) (hψ j), hT (ψ i) (hψ i) (ψ' j) (hψ' j),
        hT (ψ' i) (hψ' i) (ψ j) (hψ j), hT (ψ' i) (hψ' i) (ψ' j) (hψ' j)] at h
    exact ite_inner_key (hne i) h
  by_cases hex : ∃ i j, i ≠ j ∧ ψ i = ψ j
  · -- some pair `ψ i = ψ j` exists: then all the `ψ i` coincide
    obtain ⟨i, j, hij, hijeq⟩ := hex
    refine ⟨ψ i, hψ i, Or.inl ?_⟩
    intro k
    by_cases hk : k = i
    · simp [hk]
    by_cases hk' : k = j
    · rw [hk']; exact hijeq.symm
    -- `k` is distinct from both `i` and `j`; use the two pairs `{i,k}` and `{j,k}`
    have hik : i ≠ k := fun h => hk h.symm
    have hjk : j ≠ k := fun h => hk' h.symm
    rcases (hpair i k hik).1 with h | h
    · exact h.symm
    rcases (hpair j k hjk).1 with h2 | h2
    · exact (hijeq.trans h2).symm
    · exact absurd ⟨hijeq, h.trans h2.symm⟩ (hpair i j hij).2
  · -- no pair `ψ i = ψ j` with `i ≠ j`: then all the `ψ' i` coincide
    have hex' : ∀ i j, i ≠ j → ψ i ≠ ψ j := fun i j hij h => hex ⟨i, j, hij, h⟩
    have hone : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i0⟩ := hone
    refine ⟨ψ' i0, hψ' i0, Or.inr ?_⟩
    intro k
    by_cases hk : k = i0
    · simp [hk]
    · have hk' : i0 ≠ k := fun h => hk h.symm
      rcases (hpair i0 k hk').1 with h | h
      · exact absurd h (hex' i0 k hk')
      · exact h.symm

end Work.Coherence
