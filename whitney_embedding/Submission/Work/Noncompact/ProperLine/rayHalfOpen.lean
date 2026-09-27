import Submission.Work.Noncompact.Canals.arc_interior_empty
import Submission.Work.Noncompact.Routing.arcs_removal

/-!
# Dependency note (important for this directory)

This file must **not** import `Submission.Work.Noncompact.Routing.arcs_removal`: that module
brings in `Submission.Work.Whitney.PathTools.compl_totallyDisconnected_pathConnected`, which clashing
with `Submission.Work.Whitney.PathTools.plane_transport` (reachable from the `Canals` slit imports)
makes the import fail outright with `joinedIn_compl_of_isometry` declared twice.  Similarly
`Routing/arcs_removal.lean` must not be imported into any file that already pulls in
`plane_transport`.

Hence the slit-removal toolkit is split:

* `raySlit.lean`      : `Canals` slit family + `Canals.arc_interior_empty` (Mathlib only) and the
                        `n = 2` open slit;  no `arcs_removal`.
* `rayHalfOpen.lean`  : `Canals.arc_interior_empty` + `Routing.arcs_removal`;  no `Canals.SlitDefs`
                        / `Canals.slit_removal_surface`.

Consumers that need both must therefore go through a file that only imports the *statements* they
use, never the two together in one import closure.
-/
open Set Topology

namespace Work.Noncompact.ProperLine

/-- **Removing a half-open arc keeps its excluded endpoint.**  If `γ` is an arc inside the open
preconnected set `C`, then `C \ γ '' Ico 0 1` is preconnected: it is
`(C \ γ '' Icc 0 1) ∪ {γ 1}`, the first part is preconnected by the closed-arc removal
(`Routing.arcs_removal.isPreconnected_sdiff_image_arc`), and the endpoint `γ 1` lies in the closure
of that part because an arc does not fill a neighbourhood of its own endpoint
(`arc_interior_empty`).  This is the member of the slit-removal family that *keeps* an endpoint;
both `slit_removal` and `IsSlitIn` require a far end outside the ambient set, so neither covers it. -/
theorem isPreconnected_sdiff_Ico_image_arc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {C : Set M} (hC : IsOpen C)
    (hCc : IsPreconnected C) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) (hγC : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ C) :
    IsPreconnected (C \ γ '' Set.Ico (0:ℝ) 1) := by
  have hA : IsPreconnected (C \ γ '' Set.Icc (0:ℝ) 1) :=
    Work.Noncompact.Routing.isPreconnected_sdiff_image_arc hn hC hCc hγ hinj hγC
  have h1C : γ 1 ∈ C := hγC 1 ⟨zero_le_one, le_rfl⟩
  have h1cl : γ 1 ∈ closure (C \ γ '' Set.Icc (0:ℝ) 1) := by
    rw [mem_closure_iff]
    intro U hU hxU
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub' : U ∩ C ⊆ γ '' Set.Icc (0:ℝ) 1 := by
      intro z hz
      by_contra hzarc
      exact (Set.eq_empty_iff_forall_notMem.mp hcon) z ⟨hz.1, hz.2, hzarc⟩
    have hInt : γ 1 ∈ interior (γ '' Set.Icc (0:ℝ) 1) :=
      interior_maximal hsub' (hU.inter hC) ⟨hxU, h1C⟩
    rw [Work.Noncompact.Canals.arc_interior_empty (n := n) hn hγ hinj] at hInt
    exact hInt
  have hset : C \ γ '' Set.Ico (0:ℝ) 1
      = (C \ γ '' Set.Icc (0:ℝ) 1) ∪ {γ 1} := by
    ext x
    constructor
    · rintro ⟨hxC, hx⟩
      by_cases h : x = γ 1
      · exact Or.inr h
      · refine Or.inl ⟨hxC, fun hmem => ?_⟩
        obtain ⟨t, ht, rfl⟩ := hmem
        -- the two cases `t = 1` and `t < 1`: at `t < 1` injectivity rules out `γ t = γ 1`
        rcases lt_or_eq_of_le ht.2 with hlt | heq
        · exact hx ⟨t, ⟨ht.1, hlt⟩, rfl⟩
        · exact h (by rw [heq])
    · rintro (⟨hxC, hx⟩ | hflip)
      · refine ⟨hxC, fun hmem => ?_⟩
        obtain ⟨t, ht, rfl⟩ := hmem
        exact hx ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
      · refine ⟨hflip ▸ h1C, fun hmem => ?_⟩
        obtain ⟨t, ht, htx⟩ := hmem
        have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, ht.2.le⟩
        have h1Icc : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
        have ht1 : t = 1 := hinj htIcc h1Icc (by rw [htx, hflip])
        exact absurd ht1 (ne_of_lt ht.2)
  rw [hset]
  exact hA.subset_closure Set.subset_union_left (fun x hx => by
    rcases hx with hx | rfl
    · exact subset_closure hx
    · exact h1cl)

end Work.Noncompact.ProperLine
