import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.RiemannRoch.RR.finite_H1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.RiemannRoch.RR

open Work.RiemannRoch

/-- **Linear-algebra step behind the Riemann–Roch induction.**  For submodules `M ≤ N` of a
`k`-module `X` with `X ⧸ M` finite dimensional, the dimension of `X ⧸ M` is the dimension of
`X ⧸ N` plus the dimension of the image of `N` in `X ⧸ M` (i.e. of `N ⧸ M`). -/
theorem finrank_quotient_eq_add_finrank_map {k : Type u} [Field k] {X : Type u} [AddCommGroup X]
    [Module k X] (M N : Submodule k X) (hMN : M ≤ N) [Module.Finite k (X ⧸ M)] :
    Module.finrank k (X ⧸ M) =
      Module.finrank k (X ⧸ N) + Module.finrank k ↥(N.map (Submodule.mkQ M)) := by
  have h := Submodule.finrank_quotient_add_finrank (M := X ⧸ M) (N.map (Submodule.mkQ M))
  rw [LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotient M N hMN)] at h
  omega

/-- `Asub` is monotone in the divisor. -/
theorem Asub_mono {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) : Curve.Asub C D ≤ Curve.Asub C E :=
  Submodule.comap_mono (Curve.A_mono C h)

/-- **The Riemann–Roch step at the level of divisors.**  For `D ≤ E` the quotient `H1 C E` is
the quotient of `H1 C D` by the image of `A(E) + K`, so the dimension of `H1 C D` is the
dimension of `H1 C E` plus the dimension of that image `KquotAd C D E`. -/
theorem step {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (h : Work.RiemannRoch.Curve.HasFiniteGenus C) {D E : C.Div} (hDE : D ≤ E) :
    Module.finrank k (Work.RiemannRoch.Curve.H1 C D) =
      Module.finrank k (Work.RiemannRoch.Curve.H1 C E) +
        Module.finrank k ↥(Work.RiemannRoch.Curve.KquotAd C D E) := by
  haveI := finite_H1 C h D
  have hMN : Curve.Asub C D ⊔ Curve.diagK C ≤ Curve.Asub C E ⊔ Curve.diagK C :=
    sup_le_sup (Asub_mono C hDE) le_rfl
  have key := finrank_quotient_eq_add_finrank_map (k := k)
    (Curve.Asub C D ⊔ Curve.diagK C) (Curve.Asub C E ⊔ Curve.diagK C) hMN
  exact key

end Work.RiemannRoch.RR
