import Mathlib
import Submission.Work.GCBasics.DivApi
import Submission.Work.RiemannRoch.RR.l_add_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.GCBasics

open Work.CurveBasics

/-- The dimension `ℓ(D) = dim_F L(D)` of the Riemann-Roch space of a divisor of `C_F` is
unchanged by adding a principal divisor: `ℓ(D + div z) = ℓ(D)` for `z ≠ 0`. -/
theorem ell_add_div {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u}
    [Field F] [Algebra K F] (D : Dv C F) {z : (Curve.baseChange C F).functionField}
    (hz : z ≠ 0) : ell C (D + (Curve.baseChange C F).div z) = ell C D :=
  Work.RiemannRoch.RR.l_add_div (Curve.baseChange C F) D hz

/-- Linearly equivalent divisors have the same `ℓ`: multiplication by a nonzero rational
function `h` with `div h = D - D'` is an `F`-linear isomorphism `L(D') ≃ L(D)`. -/
theorem ell_eq_of_linEquiv {K : Type _} [Field K] {C : Work.CurveBasics.Curve K} {F : Type _}
    [Field F] [Algebra K F] {D D' : Work.GCBasics.Dv C F}
    (h : Work.GCBasics.LinEquiv C D D') : Work.GCBasics.ell C D = Work.GCBasics.ell C D' := by
  obtain ⟨z, hz, hdiv⟩ := h
  have key := ell_add_div (K := K) (C := C) (F := F) D' hz
  rw [hdiv, add_sub_cancel] at key
  exact key

end Work.GCBasics
