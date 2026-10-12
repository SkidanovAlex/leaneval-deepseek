import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Bomb_symm` — symmetry of the Bombieri form

The Bombieri (Fock) form `bomb m` on `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` is
`⟪p, q⟫ = Σ_α p_α q_α α!`.  Being a *sum over the support of `p` of the
coefficientwise product*, it is symmetric; this module records that, together
with the two evaluation lemmas it is proved through:

* `bomb_apply` — `bomb m p q = p.sum (fun α v => mfac α * v * q α)`;
* `bomb_apply_union` — the manifestly symmetric form
  `bomb m p q = ∑ α ∈ p.support ∪ q.support, mfac α * p α * q α`;
* `Bomb_symm` — `bomb m p q = bomb m q p`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- Evaluation of the Bombieri form: it is the `p`-weighted sum of the
coefficients of `q`, with the multi-index factorial weight. -/
theorem bomb_apply {m : ℕ} (p q : RealFock m) :
    bomb m p q = p.sum (fun α v => mfac α * v * q α) := by
  rw [bomb, Finsupp.lsum_apply]
  rw [Finsupp.sum, LinearMap.sum_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
    smul_eq_mul]
  ring

/-- The Bombieri form as a sum over the union of the two supports; this form is
manifestly symmetric in `p` and `q`. -/
theorem bomb_apply_union {m : ℕ} (p q : RealFock m) :
    bomb m p q = ∑ α ∈ p.support ∪ q.support, mfac α * p α * q α := by
  rw [bomb_apply,
    Finsupp.sum_of_support_subset p Finset.subset_union_left (fun α v => mfac α * v * q α)
      (by intro i _; ring)]

/-- The Bombieri form is symmetric. -/
theorem Bomb_symm {m : ℕ} (p q : Work.BoseB4.RealFock m) :
    Work.BoseB4.bomb m p q = Work.BoseB4.bomb m q p := by
  rw [bomb_apply_union, bomb_apply_union, Finset.union_comm q.support p.support]
  exact Finset.sum_congr rfl (fun x _ => by ring)

end Work.BoseB4
