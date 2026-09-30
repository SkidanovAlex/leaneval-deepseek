import Mathlib
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Work.Charts

/-- **`ℓ(E) = 0` if and only if `L(E) = 0`**: the Riemann–Roch space of `E` is zero exactly
when its `F`-dimension vanishes.

`ℓ` is the dimension of `L` *by definition* (`Work.GCBasics.ell`), and a subspace of a
finite-dimensional vector space has dimension zero exactly when it is the bottom subspace
(`Submodule.finrank_eq_zero`).  The only non-formal input is that `L(E)` is finite dimensional
over `F`, which is `Work.CurveBasics.Linear.finiteDimensional_L`. -/
theorem ell_eq_zero_iff_L_eq_bot {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    {F : Type u} [Field F] [Algebra K F] (E : Work.GCBasics.Dv C F) :
    Work.GCBasics.ell C E = 0 ↔ Work.CurveBasics.Curve.L (C.baseChange F) E = ⊥ := by
  haveI : Module.Finite F ((C.baseChange F).L E) :=
    Work.CurveBasics.Linear.finiteDimensional_L (k := F) (C.baseChange F) _
  rw [Work.GCBasics.ell, Submodule.finrank_eq_zero]

/-- `i(D) = 0` if and only if the Riemann–Roch space `L(W_F - D)` is zero.

Both sides speak about the same `F`-vector space `L(W_F - D)`: the index of speciality is
`i(D) = ℓ(W_F - D)` *by definition* (RR5, `Charts.iOf`), and `ℓ(E) = 0 ↔ L(E) = ⊥` is
`Charts.ell_eq_zero_iff_L_eq_bot`. -/
theorem iOf_eq_zero_iff_L_eq_bot {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C] {R : Work.Charts.RochData C}
    {F : Type u} [Field F] [Algebra K F] (D : Work.GCBasics.Dv C F) :
    Work.Charts.iOf C R.W D = 0 ↔
      Work.CurveBasics.Curve.L (C.baseChange F) (Work.Charts.pullK C R.W - D) = ⊥ := by
  show Work.GCBasics.ell C (Work.Charts.pullK C R.W - D) = 0 ↔ _
  exact ell_eq_zero_iff_L_eq_bot C (Work.Charts.pullK C R.W - D)

end Work.Charts
