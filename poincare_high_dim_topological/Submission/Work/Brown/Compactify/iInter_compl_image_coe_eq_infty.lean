import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Compactify

open Set

theorem iInter_compl_image_coe_eq_infty {X : Type*} [TopologicalSpace X] {U : ℕ → Set X} (hmono : Monotone U) (hcover : (⋃ k, U k) = Set.univ) : (⋂ k, (((↑) '' U k : Set (OnePoint X))ᶜ)) = {OnePoint.infty} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_singleton_iff]
    by_contra h
    obtain ⟨a, rfl⟩ : ∃ a : X, (↑a : OnePoint X) = x := by
      cases x using OnePoint.rec with
      | infty => exact absurd rfl h
      | coe a => exact ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ a)
    exact (Set.mem_iInter.mp hx k) ⟨a, hk, rfl⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine Set.mem_iInter.mpr (fun k => ?_)
    rw [Set.mem_compl_iff, Set.mem_image]
    rintro ⟨a, -, ha⟩
    exact OnePoint.coe_ne_infty a ha

end Work.Brown.Compactify
