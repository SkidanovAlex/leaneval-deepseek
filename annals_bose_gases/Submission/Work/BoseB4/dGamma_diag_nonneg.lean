import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseB4.Bomb_self_nonneg
import Submission.Work.BoseB4.Cre_ann_adjoint
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- **`dΓ(T) ≥ 0` is PSD for a positive diagonal `T`**: if `T` is diagonal with
nonnegative eigenvalues `λ`, then the quadratic form of its second quantisation
is nonnegative,
`⟪(∑_i λ_i n_i) Φ, Φ⟫ = ∑_i λ_i ‖a_i Φ‖² ≥ 0`,
where `n_i = a_i†a_i` and `‖·‖² = bomb` (the Bombieri form, whose diagonal is
nonnegative and for which `a_i†` is the adjoint of `a_i`). -/
theorem dGamma_diag_nonneg {m : ℕ} (lam : Fin m → ℝ) (h : ∀ i, 0 ≤ lam i)
    (Φ : Work.BoseB4.RealFock m) :
    0 ≤ Work.BoseB4.bomb m ((∑ i, lam i • Work.BoseB4.modeNumOp m i) Φ) Φ := by
  have hsplit : (∑ i, lam i • Work.BoseB4.modeNumOp m i) Φ
      = ∑ i, lam i • (Work.BoseB4.modeNumOp m i Φ) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply]
  rw [hsplit, map_sum, LinearMap.sum_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine mul_nonneg (h i) ?_
  show 0 ≤ Work.BoseB4.bomb m (Work.BoseB4.modeNumOp m i Φ) Φ
  rw [Work.BoseB4.modeNumOp, LinearMap.comp_apply, Work.BoseB4.Cre_ann_adjoint]
  exact Work.BoseB4.Bomb_self_nonneg _

end Work.BoseB4
