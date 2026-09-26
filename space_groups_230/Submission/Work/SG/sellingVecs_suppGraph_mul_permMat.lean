import Mathlib
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.EdgeSetDefs
import Submission.Work.SG.sb_permMat
import Submission.Work.SG.sellingVecs_edgeSet_eq
import Submission.Work.SG.edgeSet_permE
import Submission.Work.SG.edgeSet_suppGraph_mul_permMat

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

-- `hd` (the normal-form hypothesis) is not needed: `sellingVecs` depends only on the underlying
-- *undirected* edge set, so the ordering of the pairs of `E` is irrelevant.
set_option linter.unusedVariables false

/-- Relabelling bridge: if `τ` carries the graph `E` (edges in normal form) onto the support
graph of `W`, then the support graph of the relabelled superbase `W * permMat τ` defines the same
coset-minimal vectors as `E`.

Route: the underlying undirected edge set of `suppGraph Q (W * permMat τ)` is the `τ.symm`-image
of that of `suppGraph Q W` (because `sb (W * permMat τ) m = sb W (τ m)` and `bf` is symmetric by
`hsym`), while `E` has the same underlying undirected edge set as `permE τ E`, whose `τ`-image is
`(suppGraph Q W).toFinset`.  Applying the inverse relabelling shows that `E` and
`suppGraph Q (W * permMat τ)` have the same underlying undirected edge set, and `sellingVecs`
depends only on that set (the constraint `|x a - x b| ≤ 1` is symmetric in `a, b`). -/
theorem sellingVecs_suppGraph_mul_permMat {Q W : IMat} {τ : Equiv.Perm (Fin 4)}
    {E : List (Fin 4 × Fin 4)} (hsym : Q.transpose = Q) (hd : ∀ p ∈ E, p.1 < p.2)
    (h : (permE τ E).toFinset = (suppGraph Q W).toFinset) :
    sellingVecs (suppGraph Q (W * permMat τ)) = sellingVecs E := by
  apply sellingVecs_edgeSet_eq
  have hset : edgeSet (permE τ E) = edgeSet (suppGraph Q W) := by
    simp only [edgeSet, h]
  have h1 : (edgeSet E).image (Sym2.map τ) = edgeSet (suppGraph Q W) := by
    rw [← edgeSet_permE τ E, hset]
  rw [edgeSet_suppGraph_mul_permMat hsym, ← h1, Finset.image_image]
  have hcomp : Sym2.map τ.symm ∘ Sym2.map τ = id := by
    rw [← Sym2.map_comp]
    have : τ.symm ∘ τ = id := funext fun x => Equiv.symm_apply_apply τ x
    rw [this, Sym2.map_id]
  rw [hcomp, Finset.image_id]

end Work.SG
