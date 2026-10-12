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

/-!
# `Work.BoseB4.totNumOp_nonneg` — the total number operator is positive semi-definite

For the real bosonic Fock space `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` with the
Bombieri form `bomb m` (`⟪p, q⟫ = Σ_α α! p_α q_α`), the total number operator

    totNumOp m = ∑_l a_l† a_l

is positive semi-definite for the quadratic form of `bomb`:

    ⟪totNumOp Φ, Φ⟫ = Σ_l ‖a_l Φ‖² ≥ 0.

The mathematics is two lines: `a_l†` is the `bomb`-adjoint of `a_l`
(`Work.BoseB4.Cre_ann_adjoint`), so the `l`-th summand of the quadratic form is

    ⟪a_l†a_l Φ, Φ⟫ = ⟪a_l Φ, a_l Φ⟫ ≥ 0

(`Work.BoseB4.Bomb_self_nonneg`), and a finite sum of nonnegative reals is
nonnegative.  Note that no symmetry of `bomb` is needed: the adjointness is used
directly in the direction `bomb m (cre m l p) q = bomb m p (ann m l q)`.

Everything here is `sorry`-free and rests only on the standard axioms
(`propext`, `Quot.sound`, `Classical.choice`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- **Each mode number operator is positive semi-definite**: the quadratic form
of `n_l = a_l† a_l` is that of `a_l` on itself,
`⟪a_l†a_l Φ, Φ⟫ = ⟪a_lΦ, a_lΦ⟫ ≥ 0`, by the adjointness `a_l† = (a_l)*`. -/
lemma modeNumOp_quadform_nonneg {m : ℕ} (l : Fin m) (Φ : RealFock m) :
    0 ≤ bomb m (modeNumOp m l Φ) Φ := by
  have h := Bomb_self_nonneg (m := m) (ann m l Φ)
  rw [← Cre_ann_adjoint] at h
  simpa [modeNumOp, LinearMap.comp_apply] using h

/-- **The total number operator is positive semi-definite**: `⟪N Φ, Φ⟫ ≥ 0`. -/
theorem totNumOp_nonneg (m : ℕ) (Φ : Work.BoseB4.RealFock m) :
    0 ≤ Work.BoseB4.bomb m (Work.BoseB4.totNumOp m Φ) Φ := by
  have hsum : Work.BoseB4.bomb m (Work.BoseB4.totNumOp m Φ) Φ
      = ∑ i : Fin m, Work.BoseB4.bomb m (Work.BoseB4.modeNumOp m i Φ) Φ := by
    rw [Work.BoseB4.totNumOp, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  rw [hsum]
  exact Finset.sum_nonneg fun i _ => modeNumOp_quadform_nonneg i Φ

end Work.BoseB4
