import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- A preconnected set contained in the union of two disjoint closed sets is contained
in one of them. -/
theorem preconnected_subset_or_subset {α : Type*} [TopologicalSpace α] {s u v : Set α} (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v) (hd : Disjoint u v) (hsub : s ⊆ u ∪ v) : s ⊆ u ∨ s ⊆ v := by
  by_cases hsu : (s ∩ u).Nonempty
  · left
    intro x hxs
    by_contra hxu
    have hxv : x ∈ v := (hsub hxs).resolve_left hxu
    obtain ⟨z, hzs, hzu, hzv⟩ :=
      isPreconnected_closed_iff.1 hs u v hu hv hsub hsu ⟨x, hxs, hxv⟩
    exact (Set.disjoint_left.1 hd hzu) hzv
  · right
    intro x hxs
    rcases hsub hxs with h | h
    · exact absurd ⟨x, hxs, h⟩ hsu
    · exact h

end Work.SeedCertRay
