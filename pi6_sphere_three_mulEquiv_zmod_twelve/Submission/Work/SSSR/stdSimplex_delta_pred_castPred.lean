import Mathlib
import Submission.Work.SSSR.singularFibration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial
/-- **The simplicial identity expressing a codimension-two face of a horn in the two possible
ways.**  For `j < k` (faces of `Δ[n+2]`), the composite of the coface `δ_{k.pred}` of `Δ[n]` with
the coface `δ_j` of `Δ[n+1]` (first `δ_{k-1} : Δ[n] ⟶ Δ[n+1]`, then `δ_j : Δ[n+1] ⟶ Δ[n+2]`)
equals the composite of `δ_{j.castPred}` with `δ_k`: both are the inclusion of the codimension-two
face of `Δ[n+2]` spanned by the vertices other than `j` and `k`.

This is essentially `CosimplicialObject.δ_comp_δ'` (for the cosimplicial object `SSet.stdSimplex`)
with `i := j.castPred` and `j := k`, plus `Fin.castSucc_castPred`; equivalently it is the pair of
identities `stdSimplex.facePairComplIso_hom_ι` / `..._ι'`. -/
theorem stdSimplex_delta_pred_castPred {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k) :
    SSet.stdSimplex.δ (n := n) (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SSet.stdSimplex.δ (n := n + 1) j
      = SSet.stdSimplex.δ (n := n) (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SSet.stdSimplex.δ (n := n + 1) k := by
  rw [← SSet.stdSimplex.facePairComplIso_hom_ι' j k hjk,
    ← SSet.stdSimplex.facePairComplIso_hom_ι j k hjk]

end Work.SSSR
