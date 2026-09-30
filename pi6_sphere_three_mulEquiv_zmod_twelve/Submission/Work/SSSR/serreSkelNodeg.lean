import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.StemsB.SerreFiltration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
theorem serreSkelNodeg {X : SSet.{0}} {P n : ℕ} (x : X _⦋n⦌) :
    x ∈ (X.skeleton P).obj (op ⦋n⦌) ↔ (SSet.S.mk x).toN.dim < P := by
  rw [← SSet.Subcomplex.ofSimplex_le_iff x (X.skeleton P), SSet.S.ofSimplex_eq_subcomplex_mk,
    ← SSet.S.subcomplex_toN (SSet.S.mk x)]
  rw [SSet.S.subcomplex, SSet.Subcomplex.ofSimplex_le_iff]
  exact SSet.mem_skeleton_obj_iff_of_nonDegenerate X
    ⟨(SSet.S.mk x).toN.simplex, (SSet.S.mk x).toN.nonDegenerate⟩ P

end Work.SSSR
