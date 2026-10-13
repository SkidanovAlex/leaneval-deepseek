import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.star_proj

namespace Work.WilE7.GraphCellAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **Composing projections.**  Let `X` be a semi-Pfaffian set in `ℝ^{(n+M)+m}`.  Re-indexing
it along the (value preserving) identification `Fin ((n+M)+m) ≃ Fin (n+(m+M))` turns it into a
semi-Pfaffian set in `ℝ^{n+(m+M)}`, and projecting *that* to the first `n` coordinates is the
same as first projecting `X` to the first `n+M` coordinates and then dropping the following `M`.

This is the `SemiPf`-level companion of `sp_shift_set` (which does the same for `StarPiece`s):
the pointwise identity is `sp_projFirst_push`. -/
theorem projFirst_projFirst_reindex {n m M : ℕ} (X : SemiPf ((n + M) + m)) :
    projFirst n M '' WilkiesDesign.E.projFirst (n + M) m '' X.set =
      projFirst n (m + M) '' (SemiPf.reindex (spEquiv n M m) X).set := by
  have hfun : (fun x : Fin ((n + M) + m) → ℝ =>
        projFirst n (m + M) ((pullHomeo (spEquiv n M m)).symm x))
      = fun x => projFirst n M (projFirst (n + M) m x) := by
    funext x
    exact sp_projFirst_push x
  rw [sp_reindex_set_pull, sp_preimage_pull]
  simp only [Set.image_image, hfun]

theorem subPf_projFirst {n M : ℕ} {Y : Set (Fin (n + M) → ℝ)}
    (h : WilkiesDesign.E.SubPf (n + M) Y) : WilkiesDesign.E.SubPf n (WilkiesDesign.E.projFirst n M '' Y) := by
  obtain ⟨m, X, hX⟩ := h
  refine ⟨m + M, SemiPf.reindex (spEquiv n M m) X, ?_⟩
  rw [hX, projFirst_projFirst_reindex]

end Work.WilE7.GraphCellAux
