import Mathlib

namespace Work.SubBigon

/-- A bounded (in a `Bornology` sense) set in `ℝ × ℝ` has unbounded complement. -/
theorem not_isBounded_compl_of_isBounded {S : Set (ℝ × ℝ)} (hS : Bornology.IsBounded S) :
    ¬ Bornology.IsBounded Sᶜ := by
  intro hb
  have huniv : Bornology.IsBounded (Set.univ : Set (ℝ × ℝ)) := by
    rw [← Set.union_compl_self S]
    exact hS.union hb
  rw [isBounded_iff_forall_norm_le] at huniv
  obtain ⟨C, hC⟩ := huniv
  have h := hC (C + 1, 0) (Set.mem_univ _)
  rw [Prod.norm_def] at h
  rw [Real.norm_eq_abs, norm_zero, max_eq_left (abs_nonneg (C + 1))] at h
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (C + 1)) h
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ C + 1)] at h
  linarith

/-- The frontier of an open set `P` whose closure is `P ∪ J` with `J` disjoint from `P` is `J`. -/
theorem frontier_eq_of_closure_eq_union {P J : Set (ℝ × ℝ)}
    (hPopen : IsOpen P) (hPcl : closure P = P ∪ J) (hPJ : Disjoint P J) :
    frontier P = J := by
  rw [frontier, hPopen.interior_eq, hPcl]
  ext x
  constructor
  · rintro ⟨h | h, hx⟩
    · exact absurd h hx
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    intro hxP
    exact (Set.disjoint_left.mp hPJ hxP) h

theorem region_subset_of_boundary_subset {J J' P P' : Set (ℝ × ℝ)}
    (hPopen : IsOpen P) (hPbdd : Bornology.IsBounded P) (hPcl : closure P = P ∪ J)
    (hPJ : Disjoint P J)
    (hP'open : IsOpen P') (hP'bdd : Bornology.IsBounded P') (hP'pc : IsPathConnected P')
    (hP'sub : P' ⊆ J'ᶜ) (hP'cl : closure P' = P' ∪ J')
    (hJ'sub : J' ⊆ closure P) (hEpc : IsPathConnected ((closure P)ᶜ))
    (hJcl : J ⊆ closure ((closure P)ᶜ))
    (hne : (P' ∩ P).Nonempty) (hJJ' : J' ≠ J) :
    P' ⊆ P ∧ P' ≠ P := by
  -- The frontier of `P'` is (definitionally) `J'`.
  have hfrontierP' : frontier P' = J' :=
    frontier_eq_of_closure_eq_union hP'open hP'cl
      (Set.subset_compl_iff_disjoint_right.mp hP'sub)
  -- The exterior `E := (closure P)ᶜ` is unbounded.
  have hnotbddE : ¬ Bornology.IsBounded ((closure P)ᶜ) :=
    not_isBounded_compl_of_isBounded hPbdd.closure
  -- `E` is covered by the two disjoint open sets `P'` and `(closure P')ᶜ`.
  have hEsub : (closure P)ᶜ ⊆ P' ∪ (closure P')ᶜ := by
    intro x hx
    by_cases hxP' : x ∈ P'
    · exact Or.inl hxP'
    · refine Or.inr ?_
      rw [Set.mem_compl_iff] at hx ⊢
      intro hxcl
      rw [hP'cl] at hxcl
      rcases hxcl with h | h
      · exact hxP' h
      · exact hx (hJ'sub h)
  have hEpre : IsPreconnected ((closure P)ᶜ) := hEpc.isConnected.isPreconnected
  have hdisj2 : Disjoint P' ((closure P')ᶜ) :=
    Set.disjoint_compl_right_iff_subset.mpr subset_closure
  have hcompopen : IsOpen ((closure P')ᶜ) := isClosed_closure.isOpen_compl
  have hcase := hEpre.subset_or_subset hP'open hcompopen hdisj2 hEsub
  -- Since `E` is connected it lies entirely in one of the two pieces; it cannot lie
  -- in the bounded `P'`, so `P'` is disjoint from `E`.
  have hPE : Disjoint P' ((closure P)ᶜ) := by
    rcases hcase with hcase | hcase
    · exfalso
      exact hnotbddE (hP'bdd.subset hcase)
    · rw [Set.disjoint_left]
      intro x hxP' hxE
      exact (hcase hxE) (subset_closure hxP')
  -- `P'` is also disjoint from `J`, since every point of `J` lies in the closure of `E`
  -- and `P'` is an open neighbourhood of each of its points.
  have hP'J : Disjoint P' J := by
    rw [Set.disjoint_left]
    intro x hxP' hxJ
    have hxclE : x ∈ closure ((closure P)ᶜ) := hJcl hxJ
    have hnhds : P' ∈ nhds x := hP'open.mem_nhds hxP'
    have : (P' ∩ (closure P)ᶜ).Nonempty := mem_closure_iff_nhds.mp hxclE P' hnhds
    rcases this with ⟨y, hyP', hyE⟩
    exact (Set.disjoint_left.mp hPE hyP') hyE
  refine ⟨?_, ?_⟩
  · -- `P' ⊆ P`: a point of `P'` is in `closure P = P ∪ J` but not in `J`.
    intro x hx
    have hxE : x ∉ (closure P)ᶜ := fun h => (Set.disjoint_left.mp hPE hx) h
    have hxJ : x ∉ J := fun h => (Set.disjoint_left.mp hP'J hx) h
    have hxcl : x ∈ closure P := by
      by_contra h
      exact hxE h
    rw [hPcl] at hxcl
    rcases hxcl with h | h
    · exact h
    · exact absurd h hxJ
  · -- `P' ≠ P`: otherwise the frontiers, hence `J'` and `J`, would coincide.
    intro heq
    apply hJJ'
    rw [← hfrontierP', heq]
    exact frontier_eq_of_closure_eq_union hPopen hPcl hPJ

end Work.SubBigon
