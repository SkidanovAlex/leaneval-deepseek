import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.Normality.Sym
import Submission.Work.CurveFacts.smooth_sections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveFacts

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry
set_option linter.style.haveILetI false
universe u

/-- The chart ring `Γ(Cⁿ, U)^{S_n}` of an invariant affine open `U` of the `n`-th power of a
curve is integrally closed: `Γ(Cⁿ, U)` is a smooth `K`-algebra and a domain (it is the ring of
sections of a nonempty affine open of the smooth integral scheme `Cⁿ`), so its invariants under
the finite group `S_n` are integrally closed
(`Work.Normality.isIntegrallyClosed_invariants_of_smooth`). -/
theorem chartRing_isIntegrallyClosed {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (U : (Work.SymQuot.symData C n).Chart) (h : Nonempty U.1) :
    IsIntegrallyClosed ↥((Work.SymQuot.symData C n).action.chartRing U.1 U.2.2) := by
  haveI : Nonempty U.1 := h
  -- `Cⁿ` is integral, so the sections over the nonempty open `U.1` form a domain
  haveI : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  haveI : IsDomain Γ((Work.SymQuot.prod C.toOver n).left, U.1) := inferInstance
  -- the structure morphism of `Cⁿ` is smooth over `K`
  haveI : Smooth (Work.SymQuot.prod C.toOver n).hom := Work.SymQuot.smooth_pi_prod C n
  -- the canonical `K`-algebra structure on the sections, and its smoothness
  let φ : K →+* Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
    (((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ U.1 le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K Γ((Work.SymQuot.prod C.toOver n).left, U.1) := φ.toAlgebra
  haveI : Algebra.Smooth K Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
    (smooth_sections (Work.SymQuot.prod C.toOver n).hom U.2.1).toAlgebra
  -- the `S_n`-action on the sections over the invariant open `U.1`, matching `chartRing`
  letI : MulSemiringAction (ULift.{u} (Equiv.Perm (Fin n)))
      Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
    (Work.SymQuot.symData C n).action.sectionMulSemiringAction U.1 U.2.2
  exact Work.Normality.isIntegrallyClosed_invariants_of_smooth (K := K)
    (B := Γ((Work.SymQuot.prod C.toOver n).left, U.1)) (G := ULift.{u} (Equiv.Perm (Fin n)))

end Work.CurveFacts
