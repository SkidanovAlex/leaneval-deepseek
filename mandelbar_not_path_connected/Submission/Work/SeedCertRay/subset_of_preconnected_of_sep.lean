import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- A preconnected set contained in the union of two disjoint closed sets lies in one of them,
and the witness `w` (disjoint from `v`, meeting `s`) tells us *which* one: it forces `s ∩ u`
to be nonempty, so `s` cannot be the `v`-side. -/
theorem subset_of_preconnected_of_sep {α : Type*} [TopologicalSpace α] {s u v w : Set α} (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v) (hd : Disjoint u v) (hsub : s ⊆ u ∪ v) (hwv : Disjoint w v) (hws : (s ∩ w).Nonempty) : s ⊆ u := by
  -- The witness `y ∈ s ∩ w` lies in `u`: it is in `u ∪ v`, and `w` misses `v`.
  obtain ⟨y, hys, hyw⟩ := hws
  have hyu : y ∈ u := by
    rcases hsub hys with h | h
    · exact h
    · exact absurd (hwv.le_bot ⟨hyw, h⟩) (by simp)
  -- Hence `s` meets `u`. If it also met `v`, preconnectedness (closed formulation) would put a
  -- point of `s` in `u ∩ v`, contradicting disjointness.
  rintro x hx
  by_contra hxu
  have hxv : x ∈ v := by
    rcases hsub hx with h | h
    · exact absurd h hxu
    · exact h
  obtain ⟨z, -, hzu, hzv⟩ :=
    isPreconnected_closed_iff.1 hs u v hu hv hsub ⟨y, hys, hyu⟩ ⟨x, hx, hxv⟩
  exact absurd (hd.le_bot ⟨hzu, hzv⟩) (by simp)

end Work.SeedCertRay
