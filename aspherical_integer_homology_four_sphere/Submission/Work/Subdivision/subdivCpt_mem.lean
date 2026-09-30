import Mathlib
import Submission.Work.Subdivision.Filtration
import Submission.Work.Subdivision.SubdivAssembly
import Submission.Work.Subdivision.subdivCell_support

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision map respects the skeletal filtrations

The subdivision chain map `PolyCW.subdiv : cellChain P ⟶ sdChain P` carries the
`n`-skeleton of the cellular chain complex into the `n`-skeleton of the
subdivided chain complex:

`cellSubMod P hdd n k ≤ (sdSubMod P n k).comap ((subdivCpt P hdd k).hom)`.

This is the filtration-compatibility input for the skeletal induction proving
that `subdiv` is a quasi-isomorphism (`SubData.restrictMap`/`SubData.quotMap`).

In degree `k > n` the left-hand side is `⊥`, so there is nothing to prove.  In
degree `k ≤ n` the left-hand side is everything and the claim reduces to: the
subdivision chain `subdivCell P k e` of a `k`-cell `e` — and hence the image of
any `k`-chain under `subdivCpt P hdd k` — is supported on simplices all of whose
vertices are faces of `e` (`Work.Subdivision.subdivCell_support`), hence of
dimension `≤ k ≤ n`, so it lies in the submodule `sdSubMod P n k` spanned by such
simplices.
-/

namespace Work.Subdivision

/-- **Filtration compatibility, cell by cell.**  For `k ≤ n` the subdivision
chain of a single `k`-cell lies in the `n`-skeleton of the subdivided chain
complex: its support consists of simplices whose vertices are faces of the cell,
hence of dimension `≤ k ≤ n`. -/
theorem subdivCell_mem_sdSubMod (P : PolyCW) {n k : ℕ} (h : k ≤ n)
    (e : {e : P.Cell // P.dim e = k}) :
    PolyCW.subdivCell P k e ∈ PolyCW.sdSubMod P n k := by
  have hspan : Submodule.span ℤ {x : (P.sdChain).X k | ∃ σ : Simplex P.Cell k,
      (∀ i, σ i ≤ e.1) ∧ x = PolyCW.sdElem P σ} ≤ PolyCW.sdSubMod P n k := by
    rw [Submodule.span_le]
    rintro x ⟨σ, hσ, rfl⟩
    exact PolyCW.sdElem_mem_sdSubMod P
      (fun i => le_trans (P.dim_le (hσ i)) (by rw [e.2]; exact h))
  apply hspan
  rw [← Finsupp.sum_single (PolyCW.subdivCell P k e)]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  rw [← Finsupp.smul_single_one σ ((P.subdivCell k e) σ)]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨σ, subdivCell_support P k e σ hσ, rfl⟩)

theorem subdivCpt_mem (P : PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero) (n k : ℕ) :
    PolyCW.cellSubMod P hdd n k ≤
      Submodule.comap (ModuleCat.Hom.hom (PolyCW.subdivCpt P hdd k)) (PolyCW.sdSubMod P n k) := by
  by_cases hkn : k ≤ n
  · rw [PolyCW.cellSubMod, if_pos hkn]
    intro x _
    rw [Submodule.mem_comap]
    show PolyCW.subdivLM P k x ∈ PolyCW.sdSubMod P n k
    have h1 : PolyCW.subdivLM P k x = x.sum (fun e c => c • PolyCW.subdivCell P k e) := by
      rw [PolyCW.subdivLM]
      exact Finsupp.linearCombination_apply ℤ x
    rw [h1]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.smul_mem _ _ (subdivCell_mem_sdSubMod P hkn e)
  · rw [PolyCW.cellSubMod, if_neg hkn]
    exact bot_le

end Work.Subdivision
