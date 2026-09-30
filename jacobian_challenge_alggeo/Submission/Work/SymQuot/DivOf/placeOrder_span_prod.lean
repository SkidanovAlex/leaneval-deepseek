import Mathlib
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.placeOrder_prod_placeIdeal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open scoped Classical

namespace Work.SymQuot.DivOf

universe u

open Work.CurveBasics

theorem placeOrder_span_prod {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain (C.left.presheaf.obj (Opposite.op V))]
    {ι : Type*} (s : Finset ι) (f : ι → C.left.presheaf.obj (Opposite.op V))
    (hf : ∀ i ∈ s, f i ≠ 0) (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) :
    Work.SymQuot.DivOf.placeOrder C V (Ideal.span {∏ i ∈ s, f i}) z hz =
      ∑ i ∈ s, Work.SymQuot.DivOf.placeOrder C V (Ideal.span {f i}) z hz := by
  classical
  -- the maximal ideal `m_z` is irreducible in the associates of `Γ(C,V)`
  have hpirr : Irreducible (Associates.mk (placeIdeal C V z hz)) := by
    rw [← heightOneEquiv_apply C V hV ⟨z, hz⟩]
    exact (heightOneEquiv C V hV ⟨z, hz⟩).associates_irreducible
  -- the principal ideals `(f i)` are non-zero
  have hg : ∀ i ∈ s, (Ideal.span ({f i} : Set (C.left.presheaf.obj (Opposite.op V)))) ≠ ⊥ := by
    intro i hi h
    exact hf i hi (Ideal.span_singleton_eq_bot.mp h)
  -- multiplicativity of the multiplicity in a finite product of ideals
  have hcount := Work.SymQuot.DivOf.Associates.count_finset_prod (s := s)
    (f := fun i => Ideal.span ({f i} : Set (C.left.presheaf.obj (Opposite.op V))))
    hg (Associates.mk (placeIdeal C V z hz)) hpirr
  -- the product of the principal ideals is the principal ideal on the product
  rw [Ideal.prod_span_singleton] at hcount
  simpa only [placeOrder] using hcount

end Work.SymQuot.DivOf
