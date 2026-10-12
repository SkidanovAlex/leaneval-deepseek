import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Bomb_symm
import Submission.Work.BoseB4.Cre_ann_adjoint
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

open scoped BigOperators

/-! Each single-mode number operator `n_i = a_i† a_i` is self-adjoint for the
Bombieri form: `⟪a_i†a_i p, q⟫ = ⟪a_i p, a_i q⟫ = ⟪p, a_i†a_i q⟫`, using the
adjointness `Cre_ann_adjoint` (`a_i† = (a_i)*`) twice and the symmetry
`Bomb_symm`. -/
lemma modeNumOp_selfadj {m : ℕ} (i : Fin m) (p q : RealFock m) :
    bomb m (modeNumOp m i p) q = bomb m p (modeNumOp m i q) := by
  show bomb m (cre m i (ann m i p)) q = bomb m p (cre m i (ann m i q))
  rw [Cre_ann_adjoint i (ann m i p) q]
  rw [Bomb_symm p (cre m i (ann m i q))]
  rw [Cre_ann_adjoint i (ann m i q) p, Bomb_symm (ann m i q) (ann m i p)]

/-- The total number operator `N = ∑_i a_i†a_i` is self-adjoint for the
Bombieri form, being a finite sum of self-adjoint single-mode number operators
`modeNumOp_selfadj`. -/
theorem totNumOp_symm (m : ℕ) (Φ Ψ : Work.BoseB4.RealFock m) :
    Work.BoseB4.bomb m (Work.BoseB4.totNumOp m Φ) Ψ
      = Work.BoseB4.bomb m Φ (Work.BoseB4.totNumOp m Ψ) := by
  have hL : bomb m (totNumOp m Φ) Ψ = ∑ i : Fin m, bomb m (modeNumOp m i Φ) Ψ := by
    rw [totNumOp, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  have hR : bomb m Φ (totNumOp m Ψ) = ∑ i : Fin m, bomb m Φ (modeNumOp m i Ψ) := by
    rw [totNumOp, LinearMap.sum_apply, map_sum]
  rw [hL, hR]
  exact Finset.sum_congr rfl (fun i _ => modeNumOp_selfadj i Φ Ψ)

end Work.BoseB4
