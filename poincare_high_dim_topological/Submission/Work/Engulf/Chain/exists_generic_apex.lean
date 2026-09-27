import Mathlib
import Submission.Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace
import Submission.Work.PL.Defs

namespace Work.Engulf.Chain

/-- **A generic apex for the cone (Newman §12)**: if the faces of `Γ` are finite, of dimension
`≤ p + 1` (`PL.DimLE Γ (p+1)`), `σ ∈ Γ.faces` has `σ.card ≤ p + 1`, and the ambient dimension
satisfies `2p + 4 ≤ N`, then there is a point `a : PL.E N` lying outside every affine span
`affineSpan ℝ (σ ∪ s)`, `s ∈ Γ.faces`.  (Then also `a ∉ Γ.space`, since for a face `s`,
`simp s ⊆ affineSpan s ⊆ affineSpan (σ ∪ s)`.)

Proof: each `σ ∪ s` has at most `2p + 3 ≤ N - 1` points, so its affine span is a *proper* affine
subspace of `PL.E N` (its direction is the `vectorSpan` of at most `N - 1` points, of finrank
`≤ N - 2 < N = finrank ℝ (PL.E N)`; use `finrank_vectorSpan_image_finset_le` together with
`AffineSubspace.direction_affineSpan`).  Then apply
`Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace` to the finitely many (use
`hfin.fintype`) proper affine subspaces `s ↦ affineSpan ℝ (σ ∪ s)`. -/
theorem exists_generic_apex {N p : ℕ} (Γ : PL.Cx N) (σ : Finset (PL.E N)) (hσ : σ ∈ Γ.faces)
    (hfin : Γ.faces.Finite) (hcard : σ.card ≤ p + 1) (hroom : 2 * p + 4 ≤ N)
    (hdim : PL.DimLE Γ (p + 1)) :
    ∃ a : PL.E N, ∀ s ∈ Γ.faces,
      a ∉ (affineSpan ℝ ((σ ∪ s : Finset (PL.E N)) : Set (PL.E N)) : Set (PL.E N)) := by
  classical
  have hfinrank : Module.finrank ℝ (PL.E N) = N := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  -- Every `affineSpan ℝ (σ ∪ s)`, `s ∈ Γ.faces`, is a proper affine subspace.
  have hproper : ∀ s ∈ Γ.faces,
      affineSpan ℝ (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))) ≠ ⊤ := by
    intro s hs
    have hsub : (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))).Finite := (σ ∪ s).finite_toSet
    have hcard_le : (σ ∪ s).card ≤ N := by
      have h1 : (σ ∪ s).card ≤ σ.card + s.card := Finset.card_union_le σ s
      have h2 : s.card ≤ p + 1 + 1 := hdim s hs
      omega
    have henc : (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))).encard
        ≤ Module.finrank ℝ (PL.E N) := by
      rw [Set.encard_coe_eq_coe_finsetCard, hfinrank]
      exact_mod_cast hcard_le
    have h := affineSpan_image_ne_top_of_encard_le_finrank (k := ℝ) hsub henc
      (id : PL.E N → PL.E N)
    simpa [Set.image_id] using h
  -- Index the (finitely many) faces.
  let ι := {s : Finset (PL.E N) // s ∈ Γ.faces}
  have : Fintype ι := hfin.fintype
  let F : ι → AffineSubspace ℝ (PL.E N) := fun i =>
    affineSpan ℝ (((σ ∪ (i : Finset (PL.E N)) : Finset (PL.E N)) : Set (PL.E N)))
  have hF : ∀ i, F i ≠ ⊤ := fun i => hproper i.1 i.2
  obtain ⟨a, -, ha⟩ :=
    Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace F hF (0 : PL.E N)
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨a, fun s hs => ?_⟩
  exact ha ⟨s, hs⟩

end Work.Engulf.Chain
