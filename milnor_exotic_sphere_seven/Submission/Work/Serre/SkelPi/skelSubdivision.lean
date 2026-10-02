import Mathlib
import Submission.Work.Serre.SkelPi.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Subdividing a loop in the `1`-skeleton according to the cell decomposition

`Skel X pt` is the wedge of one circle per based loop of `X`; every point of it is either the base
point, or lies in the open cell `openCell X pt w` of exactly one index `w`.  The spider
`spider X pt = {base} ∪ shell` is an open neighbourhood of the base point.

Given any loop `γ` in the skeleton, this file produces a finite subdivision of `[0,1]` such that on
each subinterval the loop stays inside a single open cell, or else entirely inside the spider.

The proof is the Lebesgue number argument: the family
`{γ⁻¹ spider} ∪ {γ⁻¹ openCell w}_w` is an open cover of the compact interval `[0,1]`
(`self_subset_spider_or_openCell`), so it has a Lebesgue number `δ > 0`
(`exists_monotone_Icc_subset_open_cover_unitInterval`, which is
`lebesgue_number_lemma_of_metric` for the unit interval); a partition of mesh `< δ` then has the
required property.
-/

open scoped Topology

namespace Work.Serre.SkelPi

theorem skelSubdivision (X : Type) [TopologicalSpace X] (pt : X)
    (γ : Path (base X pt) (base X pt)) :
    ∃ (M : ℕ) (_ : 0 < M) (t : Fin (M + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last M) = 1 ∧
      (∀ i j : Fin (M + 1), i ≤ j → t i ≤ t j) ∧
      (∀ k : Fin M, (∃ w : Idx X pt, ∀ s ∈ Set.Icc (t k.castSucc) (t k.succ),
          γ s ∈ openCell X pt w) ∨
        (∀ s ∈ Set.Icc (t k.castSucc) (t k.succ), γ s ∈ spider X pt)) := by
  classical
  -- The open cover of `[0,1]` given by the pulling back the spider and the open cells.
  let c : Option (Idx X pt) → Set unitInterval := fun i =>
    match i with
    | none => γ ⁻¹' spider X pt
    | some w => γ ⁻¹' openCell X pt w
  have hc₁ : ∀ i, IsOpen (c i) := by
    rintro (_ | w)
    · exact (isOpen_spider X pt).preimage γ.continuous
    · exact (isOpen_openCell X pt w).preimage γ.continuous
  have hc₂ : (Set.univ : Set unitInterval) ⊆ ⋃ i, c i := by
    intro s _
    rcases self_subset_spider_or_openCell X pt (γ s) with h | ⟨w, hw⟩
    · exact Set.mem_iUnion.mpr ⟨none, h⟩
    · exact Set.mem_iUnion.mpr ⟨some w, hw⟩
  -- Lebesgue number: a partition of sufficiently small mesh is subordinate to the cover.
  obtain ⟨t, ht0, htmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  refine ⟨n + 1, Nat.succ_pos n, fun i => t i, ?_, ?_, ?_, ?_⟩
  · simpa using ht0
  · simpa using hn (n + 1) (Nat.le_succ n)
  · intro i j hij
    exact htmono hij
  · intro k
    obtain ⟨i, hi⟩ := hsub (k : ℕ)
    rcases i with - | w
    · right
      intro s hs
      exact hi hs
    · left
      exact ⟨w, fun s hs => hi hs⟩

end Work.Serre.SkelPi
