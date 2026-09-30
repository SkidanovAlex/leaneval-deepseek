import Mathlib
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf
open Work.CurveBasics

/-- **Two nonzero ideals of the coordinate ring of an affine open of a curve that nest and whose
orders of vanishing agree at every place are equal.**

Since `I ≤ J`, the order of `I` at any place is at least the order of `J`; the hypothesis
`hord` supplies the reverse inequality at every place `z ∈ V`.  As the places of `V` are exactly
the height one primes of the Dedekind domain `Γ(C,V)` (`heightOneSpectrum_equiv_place`), all the
exponents of `I` and of `J` in their prime factorizations agree, so `I = J`. -/
theorem eq_of_le_of_forall_placeOrder_le {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    {I J : Ideal Γ(C.left, V)} (hIJ : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hord : ∀ z (hz : z.point ∈ V), placeOrder C V I z hz ≤ placeOrder C V J z hz) :
    I = J := by
  -- Places of `V` are exactly the height one primes of the Dedekind domain `Γ(C,V)`.
  obtain ⟨e, he⟩ := heightOneSpectrum_equiv_place (C := C) hV
  -- At every height one prime the exponent of `I` is at most that of `J`.
  have hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum Γ(C.left, V),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≤
      (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
    intro v
    have hv : v.asIdeal = placeIdeal C V (e.symm v).1 (e.symm v).2 := by
      rw [← he (e.symm v), Equiv.apply_symm_apply]
    have h := hord (e.symm v).1 (e.symm v).2
    simpa only [placeOrder, ← hv] using h
  -- Hence `J ⊆ I`, because `I` and `J` are the intersections of the powers of the maximal ideals.
  have hJI : J ≤ I := by
    rw [← Ideal.iInf_maxPowDividing_eq (R := Γ(C.left, V)) hJ,
        ← Ideal.iInf_maxPowDividing_eq (R := Γ(C.left, V)) hI]
    refine le_iInf fun v => le_trans (iInf_le _ v) ?_
    exact Ideal.pow_le_pow_right (hcount v)
  exact le_antisymm hIJ hJI

end Work.SymQuot.DivOf

open Work.CurveBasics

/-- The statement as requested at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.eq_of_le_of_forall_placeOrder_le` (the declaration above,
which sits in the doubly opened namespace inherited from this file's original skeleton). -/
theorem eq_of_le_of_forall_placeOrder_le {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    {I J : Ideal Γ(C.left, V)} (hIJ : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hord : ∀ z (hz : z.point ∈ V), placeOrder C V I z hz ≤ placeOrder C V J z hz) :
    I = J :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.eq_of_le_of_forall_placeOrder_le V hV hIJ hI hJ hord

end Work.SymQuot.DivOf
