import Mathlib
import Submission.Work.Whitney.insert_double_point_oriented
import Submission.Work.Whitney.clean_region_of_arcs

/-!
# Auxiliary lemmas for the endgame: simplicity, set algebra, cardinality

After the insertion move of `Work.Whitney.exists_addDoublePoint_oriented` one cancels the new double
point against a pre-existing one.  The cancellation needs the two double points to be *simple* (no
third preimage of their values) and, at the end, the bookkeeping of the double point sets.

* `Work.Whitney.simple_of_inserted` -- a double point created inside the `R`-ball by the gluing move
  is simple: `f (c.symm ·)` is injective there, so the only preimages of its value are the two
  preimages of the inserted pair.
* `Work.Whitney.simple_transported` -- a double point of `f` outside the insertion ball stays simple
  for the modified map `f'` (its value's preimages cannot be the inserted points).
* `Work.Whitney.eventually_norm_lt_of_mem_source` -- the two eventual radius conditions required by
  the insertion lemma hold automatically at a point of the chart's source whose value has norm `> R`.
* `Work.Whitney.doubleSet_cancel_inserted`, `Work.Whitney.ncard_doubleSet_drop_one` -- the composed
  double point set and the drop of the cardinality by two.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

/-- **The double point inserted in the `R`-ball is simple.** -/
theorem simple_of_inserted {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f f' : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (R : ℝ) (p' q' : M) (hp'q' : p' ≠ q')
    (hp' : ‖c p'‖ < R) (hq' : ‖c q'‖ < R)
    (hout : ∀ y : M, R ≤ ‖c y‖ → f' y = f y)
    (hclean : ∀ y : M, ‖c y‖ < R → ∀ z : M, f y = f z → z = y)
    (hds : Work.Whitney.doubleSet f' =
      Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')}) :
    (∀ z : M, f' z = f' p' → z = p' ∨ z = q') ∧
      (∀ z : M, f' z = f' q' → z = q' ∨ z = p') := by
  have key : ∀ a b : M, (a, b) ∈ Work.Whitney.doubleSet f' →
      (a, b) ∈ Work.Whitney.doubleSet f ∨ (a = p' ∧ b = q') ∨ (a = q' ∧ b = p') := by
    intro a b hab
    rw [hds] at hab
    rcases hab with h | h
    · exact Or.inl h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  constructor
  · intro z hz
    by_cases hzp : z = p'
    · exact Or.inl hzp
    · rcases key z p' (by rw [Work.Whitney.mem_doubleSet]; exact ⟨hzp, hz⟩) with h | h | h
      · exact absurd (hclean p' hp' z h.2.symm) hzp
      · exact absurd h.2 hp'q'
      · exact Or.inr h.1
  · intro z hz
    by_cases hzq : z = q'
    · exact Or.inl hzq
    · rcases key z q' (by rw [Work.Whitney.mem_doubleSet]; exact ⟨hzq, hz⟩) with h | h | h
      · exact absurd (hclean q' hq' z h.2.symm) hzq
      · exact Or.inr h.1
      · exact absurd h.1 hzq

/-- **A pre-existing simple double point stays simple after the insertion.** -/
theorem simple_transported {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f f' : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (R : ℝ) (p₁ p₂ p' q' : M)
    (hR : 0 < R) (hp' : ‖c p'‖ < R) (hq' : ‖c q'‖ < R)
    (hR₁ : R < ‖c p₁‖) (hR₂ : R < ‖c p₂‖)
    (hpre : ∀ z : M, f z = f p₁ → z = p₁ ∨ z = p₂)
    (hfp : f p₁ = f p₂)
    (hds : Work.Whitney.doubleSet f' =
      Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')}) :
    ∀ z : M, f' z = f' p₁ → z = p₁ ∨ z = p₂ := by
  intro z hz
  by_cases hzp : z = p₁
  · exact Or.inl hzp
  · have hmem : (z, p₁) ∈ Work.Whitney.doubleSet f' := by
      rw [Work.Whitney.mem_doubleSet]; exact ⟨hzp, hz⟩
    rw [hds] at hmem
    rcases hmem with h | h
    · exact hpre z h.2
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · exact absurd (h2 ▸ hR₁ : R < ‖c q'‖) (not_lt.mpr (le_of_lt hq'))
      · exact absurd (h2 ▸ hR₁ : R < ‖c p'‖) (not_lt.mpr (le_of_lt hp'))

/-- The eventual radius condition of the insertion lemma, from continuity in the chart source. -/
theorem eventually_norm_lt_of_mem_source {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (p : M) (hp : p ∈ c.source) (R : ℝ) (hRp : R < ‖c p‖) :
    ∀ᶠ y in 𝓝 p, R < ‖c y‖ := by
  have hcont : ContinuousAt (c : M → EuclideanSpace ℝ (Fin n)) p :=
    c.continuousOn_toFun.continuousAt (c.open_source.mem_nhds hp)
  exact hcont.preimage_mem_nhds ((isOpen_lt continuous_const continuous_norm).mem_nhds hRp)

/-- **The cardinality of the double point set after an insertion.** -/
theorem ncard_doubleSet_insert {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M)
    (hp'q' : p' ≠ q')
    (hnew : (p', q') ∉ Work.Whitney.doubleSet f)
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (h : Work.Whitney.doubleSet f' =
      Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')}) :
    (Work.Whitney.doubleSet f').ncard = (Work.Whitney.doubleSet f).ncard + 2 := by
  rw [h]
  have hS2 : ({(p', q'), (q', p')} : Set (M × M)).ncard = 2 := by
    simp [Set.ncard_insert_of_notMem, Set.ncard_singleton, Prod.mk.injEq, hp'q']
  have hSfin : ({(p', q'), (q', p')} : Set (M × M)).Finite :=
    (Set.finite_singleton (q', p')).insert (p', q')
  have hdisj : Disjoint (Work.Whitney.doubleSet f) ({(p', q'), (q', p')} : Set (M × M)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl
    · exact hnew hx
    · exact hnew ⟨hx.1.symm, hx.2.symm⟩
  rw [Set.ncard_union_eq hdisj hfin hSfin, hS2]

/-- **The cardinality of the double point set drops by two per cancellation.** -/
theorem ncard_doubleSet_drop_one {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ : M)
    (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂)
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (h : Work.Whitney.doubleSet f' = Work.Whitney.doubleSet f \ {(p₁, p₂), (p₂, p₁)}) :
    (Work.Whitney.doubleSet f').ncard + 2 = (Work.Whitney.doubleSet f).ncard := by
  rw [h]
  have hS2 : ({(p₁, p₂), (p₂, p₁)} : Set (M × M)).ncard = 2 := by
    simp [Set.ncard_insert_of_notMem, Set.ncard_singleton, Prod.mk.injEq, hp₁p₂]
  have hSsub : ({(p₁, p₂), (p₂, p₁)} : Set (M × M)) ⊆ Work.Whitney.doubleSet f := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [Work.Whitney.mem_doubleSet]
    rcases hx with rfl | rfl
    · exact ⟨hp₁p₂, hfp⟩
    · exact ⟨hp₁p₂.symm, hfp.symm⟩
  have hSfin : ({(p₁, p₂), (p₂, p₁)} : Set (M × M)).Finite := hfin.subset hSsub
  rw [Set.ncard_sdiff hSsub hSfin, hS2]
  have h2 : 2 ≤ (Work.Whitney.doubleSet f).ncard := by
    have := Set.ncard_le_ncard hSsub hfin
    omega
  omega

end Work.Whitney
