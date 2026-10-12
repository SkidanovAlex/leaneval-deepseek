import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixR.WindowInhabited
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/HonestVacuum.lean` — the Fock vacuum of B4's model

`RView` (`Defs.lean`) does *not* require the §6 window `T.NWindow E.bigM` to be
inhabited by a nonzero state, and `RB4box` does.  That demand is a property of
FS's honest datum: the Fock vacuum is a nonzero eigenvector of the number
operator with eigenvalue `0`, so it lies in the window for every `𝓜 ≥ 0`.

This module supplies that fact for B4's real Fock model (`Work.BoseB4.RealFock`,
`Work.BoseB4.totNumOp`), on which the honest instance of `TildeData` is built
(`Work.BoseB4.tildeData`, whose `N` is `totNumOp m`), so that

* `Work.BoseB4.totNumOp m (vac m) = 0`, `vac m ≠ 0` (here), and
* `TildeData.window_nonempty_of_vac` (`WindowInhabited.lean`)

give the window inhabitation `hwin` that `RB4boxCanonView` assumes — i.e.
`RB4box`'s nondegeneracy conjunct, which `RB4boxCanonHold.lean`'s child proved is
*not* a consequence of `KzKernels`.

Nothing here is new mathematics: in the monomial-coefficient model
`RealFock m = (Fin m →₀ ℕ) →₀ ℝ`, the vacuum is the constant polynomial
`1 = x^0 = Finsupp.single 0 1`, and every annihilation `∂/∂x_l` kills it.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixR

open Work.BoseB4

/-- **The Fock vacuum of B4's real model**: the constant polynomial
`1 = x^0`, i.e. the coefficient function supported at the zero multi-index. -/
def vac (m : ℕ) : RealFock m := Finsupp.single (0 : Fin m →₀ ℕ) (1 : ℝ)

/-- Every annihilation kills the vacuum (`∂_l 1 = 0`). -/
theorem ann_vac (m : ℕ) (l : Fin m) : ann m l (vac m) = 0 := by
  simp [vac, ann, e]

/-- The number operator of one mode kills the vacuum. -/
theorem modeNumOp_vac (m : ℕ) (l : Fin m) : modeNumOp m l (vac m) = 0 := by
  rw [modeNumOp, LinearMap.comp_apply, ann_vac, map_zero]

/-- **`N = totNumOp` kills the vacuum** — the eigenvalue-`0` eigenvector. -/
theorem totNumOp_vac (m : ℕ) : totNumOp m (vac m) = 0 := by
  rw [totNumOp, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun l _ => modeNumOp_vac m l

/-- The vacuum is nonzero (`Finsupp.single` with a nonzero value). -/
theorem vac_ne_zero (m : ℕ) : vac m ≠ 0 := by
  simp [vac]

/-- **The vacuum fact in the form `WindowInhabited.lean` consumes**: there is a
nonzero vector killed by `totNumOp m`. -/
theorem vac_killed (m : ℕ) : ∃ f₀ : RealFock m, f₀ ≠ 0 ∧ totNumOp m f₀ = 0 :=
  ⟨vac m, vac_ne_zero m, totNumOp_vac m⟩

end Work.BoseFixR
