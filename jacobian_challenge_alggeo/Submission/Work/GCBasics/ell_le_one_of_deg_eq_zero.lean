import Mathlib
import Submission.Work.GCBasics.DivApi
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `ℓ(D) ≤ 1` for an effective divisor of degree zero

Let `C` be a smooth, proper, geometrically irreducible curve over a field `K`, let `F/K`
be a field extension, and let `D` be a divisor of `C_F`.  If `D` is effective and has
degree `0`, then `D = 0`: the degree of `D = ∑_Q n_Q [Q]` is `∑_Q n_Q [κ(Q) : F]`, all
summands are nonnegative, and every residue degree is positive, so all coefficients
vanish (`Work.CurveBasics.Divisor.deg_eq_zero_iff`).

Hence `ℓ(D) = ℓ(0)`, and if the latter is `1` we get `ℓ(D) = 1 ≤ 1`.
-/

namespace Work.GCBasics

theorem ell_le_one_of_deg_eq_zero {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type _} [Field F] [Algebra K F] {D : Work.GCBasics.Dv C F}
    (hD : Work.CurveBasics.Curve.Div.IsEffective D) (hdeg : Work.GCBasics.Ddeg C F D = 0)
    (h0 : Work.GCBasics.ell C (0 : Work.GCBasics.Dv C F) = 1) :
    Work.GCBasics.ell C D ≤ 1 := by
  have hD0 : D = 0 := (Work.CurveBasics.Divisor.deg_eq_zero_iff hD).mp hdeg
  rw [hD0, h0]

end Work.GCBasics
