import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- Urysohn-type bump function: on a compact Hausdorff space `W`, given an open partial
homeomorphism `e` (playing the role of a chart) and a compact set `S ⊆ e.source`, there is a
continuous function `χ : W → ℝ` with values in `[0,1]`, equal to `1` on `S` and vanishing outside
a compact set `K ⊆ e.source`.

Proof: `W` is normal; since `e.source` is open and contains the compact set `S`, regularity
(`IsCompact.exists_isOpen_closure_subset`) gives an open `V` with `S ⊆ V` and `closure V ⊆ e.source`.
Then `K := closure V` is compact (closed in a compact space) and lies in `e.source`, and
`S ⊆ V ⊆ interior K`, so Urysohn's lemma for the disjoint closed sets `(interior K)ᶜ` and `S`
(`exists_continuous_zero_one_of_isClosed`) produces `f` with `f = 0` on `(interior K)ᶜ` and `f = 1`
on `S`. Since `interior K ⊆ K`, off `K` we have `f = 0`, as required. -/
theorem exists_bcu_bump {n : ℕ} (W : TopCat) [CompactSpace W] [T2Space W]
    (e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))))
    (S : Set W) (hS : IsCompact S) (hSsub : S ⊆ e.source) :
    ∃ (χ : W → ℝ) (K : Set W), Continuous χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z ∈ S, χ z = 1) ∧ IsCompact K ∧ K ⊆ e.source ∧ (∀ z ∉ K, χ z = 0) := by
  have hSclosed : IsClosed S := hS.isClosed
  -- `e.source` is an open neighbourhood of the compact set `S`
  have hmem : e.source ∈ nhdsSet S := e.open_source.mem_nhdsSet.2 hSsub
  -- shrink it to an open set whose closure is still contained in `e.source`
  obtain ⟨V, hVopen, hSV, hVcl⟩ := hS.exists_isOpen_closure_subset hmem
  -- the compact set supporting the bump function
  have hSint : S ⊆ interior (closure V) :=
    hSV.trans (interior_maximal subset_closure hVopen)
  have hdisj : Disjoint ((interior (closure V))ᶜ : Set W) S := by
    rw [Set.disjoint_left]
    intro z hz hzS
    exact hz (hSint hzS)
  -- Urysohn: zero on the complement of the interior of `closure V`, one on `S`
  obtain ⟨f, hf0, hf1, hfIcc⟩ :=
    exists_continuous_zero_one_of_isClosed isOpen_interior.isClosed_compl hSclosed hdisj
  refine ⟨fun z => f z, closure V, f.continuous, fun z => ⟨(hfIcc z).1, (hfIcc z).2⟩,
    fun z hz => hf1 hz, isClosed_closure.isCompact, hVcl, ?_⟩
  intro z hz
  exact hf0 (fun hzi => hz (interior_subset hzi))

end Work.ThomBordism
