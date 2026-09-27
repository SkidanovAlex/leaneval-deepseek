import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Auxi.SimplexCover

/-!
# A9 aux: a subdivision face has at most as many vertices as a coarse face containing it

`card_le_of_simp_subset`: if `simp s ⊆ simp σ` for a face `s` of `sdIter r K` and a face `σ ∈ K.faces`,
then `s.card ≤ σ.card`.  The case `σ.card ≥ 2` uses the shelling `SubdivTools.shell` of `σ` (a cover
of `simp σ` by subdivision faces with `card σ` vertices) together with `simp_cover`.
-/

open Set Metric PL Finset

namespace Work.Engulf

variable {N : ℕ}

theorem card_le_of_simp_subset (S : SubdivTools N) {r : ℕ} {K : Cx N} {hK : K.faces.Finite}
    {s σ : Finset (E N)} (hs : s ∈ (S.sdIter r K hK).faces) (hσ : σ ∈ K.faces)
    (hsub : simp s ⊆ simp σ) : s.card ≤ σ.card := by
  classical
  have hsne : s.Nonempty := (S.sdIter r K hK).nonempty_of_mem_faces hs
  rcases Nat.lt_or_ge σ.card 2 with hlt | hge
  · -- `σ` has a single vertex
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hσ
    have hcard1 : σ.card = 1 := by
      have := Finset.card_pos.2 ⟨v, hv⟩
      omega
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.1 hcard1
    rw [simp_singleton] at hsub
    have hsub' : s ⊆ {w} := fun u hu => by simpa using hsub (subset_simp hu)
    rw [Finset.card_singleton]
    exact Finset.card_le_card hsub'
  · -- `σ` has at least two vertices
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hσ
    have hssub : ({v} : Finset (E N)) ⊂ σ := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.singleton_subset_iff.2 hv, ?_⟩
      intro hEq
      have hc := congrArg Finset.card hEq
      simp at hc
      omega
    obtain ⟨ord, -, hord, hcov, -⟩ :=
      S.shell r K hK σ {v} hσ (Finset.singleton_nonempty v) hssub
    have hT : ∀ t ∈ ord.toFinset, t ∈ (S.sdIter r K hK).faces := by
      intro t ht
      exact (hord t (List.mem_toFinset.1 ht)).1
    have hcov' : simp s ⊆ ⋃ t ∈ ord.toFinset, simp t := by
      intro x hx
      have hxσ : x ∈ simp σ := hsub hx
      rw [← hcov] at hxσ
      rw [mem_iUnion₂] at hxσ ⊢
      obtain ⟨t, ht, hxt⟩ := hxσ
      exact ⟨t, List.mem_toFinset.2 ht, hxt⟩
    obtain ⟨t, htmem, hts⟩ := simp_cover hT hs hcov'
    have hst : s ⊆ t := ((S.sdIter r K hK).face_subset_face_iff hs (hT t htmem)).1 hts
    calc s.card ≤ t.card := Finset.card_le_card hst
      _ = σ.card := (hord t (List.mem_toFinset.1 htmem)).2.1

end Work.Engulf
