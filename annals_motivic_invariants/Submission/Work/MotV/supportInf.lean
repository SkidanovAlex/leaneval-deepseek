import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.ordBasic
import Submission.Work.MotV.normNatDegree
import Submission.Work.MotV.ordAevalSum
import Submission.Work.MotC2.algebraMap_smul_eq_aeval

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

/-- **The order at infinity of an element of the affine coordinate ring.**

Write `a ∈ N[E] = N[X,Y]/(Y² + (a₁X+a₃)Y - (X³+a₂X²+a₄X+a₆))` in the basis `{1, Y}` of the
coordinate ring over `N[X]`, say `a = p(x) + q(x)·y`.  At the point at infinity `x` has a pole of
order `2` and `y` a pole of order `3`, and the two possible pole orders `2·deg p` and `2·deg q + 3`
have opposite parity, so the leading terms never cancel: the order of `a` at infinity is
`-max(2·deg p, 2·deg q + 3)`.  This is exactly the degree of the norm `N_{N[X]}^{N[E]}(a)`, which is
`max (2 • deg p) (2 • deg q + 3)` by `CoordinateRing.degree_norm_smul_basis`. -/
theorem supportInf {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E) (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0) :
    Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a)
      = - ((Algebra.norm (Polynomial N) a).natDegree : ℤ) := by
  obtain ⟨p, q, hpq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := E) a
  have hpq0 : p ≠ 0 ∨ q ≠ 0 := by
    rcases eq_or_ne p 0 with hp | hp
    · rcases eq_or_ne q 0 with hq | hq
      · exact absurd (by rw [← hpq, hp, hq]; simp : a = 0) ha
      · exact Or.inr hq
    · exact Or.inl hp
  have hmap : algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a
      = Polynomial.aeval (Work.MotC2.genX E) p +
        Polynomial.aeval (Work.MotC2.genX E) q * Work.MotC2.genY E := by
    rw [← hpq, map_add, (Work.MotC2.algebraMap_smul_eq_aeval N E p).1,
      (Work.MotC2.algebraMap_smul_eq_aeval N E q).2]
  rw [hmap, ordAevalSum E H p q hpq0, normNatDegree E hpq]

end

end Work.MotV
