import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.closure_paramRay_inter_compl

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The potential attains its maximum on the part of a parameter ray lying in a segment

Let `S = segment ℝ x y ∩ paramRay hN β` be the set of points of a parameter ray which lie on a
segment.  We show that the potential `potential Mb Φ` attains a maximum on `S` (whenever `S` is
nonempty).

The point is that a parameter ray is *closed in the complement of `Mb`*: off the connectedness
locus it equals the intersection of its closure with `Mbᶜ`
(`Work.Top.closure_paramRay_inter_compl`).  Hence the truncated set

`K = S ∩ {c | potential Mb Φ e ≤ potential Mb Φ c}`

is closed: `{potential Mb Φ e ≤ potential Mb Φ ·}` avoids `Mb` entirely because `potential Mb Φ e > 0`
on the ray and the potential vanishes on `Mb`.  And `K` is contained in the compact segment, so it
is compact; the potential being continuous, it attains a maximum on `K`, and that maximum is the
maximum on all of `S` because every point of `S` below the truncation level already lies below `e`
(which belongs to `K`).
-/

open Classical Filter Set
open scoped Topology

namespace Work.Top

theorem exists_max_potential_on_segment_in_ray {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    (x y : ℂ) (β : ℝ) {e : ℂ} (he : e ∈ segment ℝ x y ∧ e ∈ Work.Top.NakaneData.paramRay hN β) :
    ∃ e' ∈ segment ℝ x y ∩ Work.Top.NakaneData.paramRay hN β,
      ∀ c ∈ segment ℝ x y ∩ Work.Top.NakaneData.paramRay hN β,
        Work.Top.potential Mb Φ c ≤ Work.Top.potential Mb Φ e' := by
  obtain ⟨hse, hpe⟩ := he
  -- `e` lies off `Mb`, so its potential is positive
  have he_notMb : e ∉ Mb := (NakaneData.mem_paramRay_iff hN).mp hpe |>.1
  have hp_pos : 0 < potential Mb Φ e := (hN.potential_pos_iff e).mpr he_notMb
  -- the segment is closed and compact
  have hseg_closed : IsClosed (segment ℝ x y) := by
    rw [← convexHull_pair (𝕜 := ℝ) x y]
    exact (Set.finite_singleton y).insert x |>.isClosed_convexHull ℝ
  have hseg_cpt : IsCompact (segment ℝ x y) := by
    rw [← convexHull_pair (𝕜 := ℝ) x y]
    exact (Set.finite_singleton y).insert x |>.isCompact_convexHull ℝ
  -- the truncated part of `S` is closed
  have hKeq : segment ℝ x y ∩ NakaneData.paramRay hN β ∩ {c : ℂ | potential Mb Φ e ≤ potential Mb Φ c} =
      segment ℝ x y ∩ closure (NakaneData.paramRay hN β) ∩ {c : ℂ | potential Mb Φ e ≤ potential Mb Φ c} := by
    ext c
    constructor
    · rintro ⟨⟨hcs, hcp⟩, hcb⟩
      exact ⟨⟨hcs, subset_closure hcp⟩, hcb⟩
    · rintro ⟨⟨hcs, hccl⟩, hcb⟩
      simp only [Set.mem_ofPred_eq] at hcb
      -- the truncation forces `c ∉ Mb`
      have hcMb : c ∉ Mb := by
        intro hcm
        rw [potential_of_mem hcm] at hcb
        exact absurd hcb (not_le.mpr hp_pos)
      -- and off `Mb` the ray is closed in the whole plane
      have hcp : c ∈ NakaneData.paramRay hN β := by
        have h2 : c ∈ closure (NakaneData.paramRay hN β) ∩ Mbᶜ := ⟨hccl, hcMb⟩
        rwa [closure_paramRay_inter_compl hN β] at h2
      exact ⟨⟨hcs, hcp⟩, hcb⟩
  have hKclosed : IsClosed (segment ℝ x y ∩ NakaneData.paramRay hN β ∩
      {c : ℂ | potential Mb Φ e ≤ potential Mb Φ c}) := by
    rw [hKeq]
    refine (hseg_closed.inter isClosed_closure).inter ?_
    exact isClosed_le continuous_const hN.continuous_potential
  have hKcpt : IsCompact (segment ℝ x y ∩ NakaneData.paramRay hN β ∩
      {c : ℂ | potential Mb Φ e ≤ potential Mb Φ c}) :=
    hseg_cpt.of_isClosed_subset hKclosed (fun c hc => hc.1.1)
  have hKne : (segment ℝ x y ∩ NakaneData.paramRay hN β ∩
      {c : ℂ | potential Mb Φ e ≤ potential Mb Φ c}).Nonempty :=
    ⟨e, ⟨hse, hpe⟩, le_refl (potential Mb Φ e)⟩
  -- the potential attains its maximum on the compact truncated set
  obtain ⟨e', he'K, hmax⟩ := hKcpt.exists_isMaxOn hKne hN.continuous_potential.continuousOn
  refine ⟨e', he'K.1, fun c hc => ?_⟩
  by_cases h : potential Mb Φ e ≤ potential Mb Φ c
  · exact hmax ⟨hc, h⟩
  · rw [not_le] at h
    exact le_trans h.le he'K.2

end Work.Top
