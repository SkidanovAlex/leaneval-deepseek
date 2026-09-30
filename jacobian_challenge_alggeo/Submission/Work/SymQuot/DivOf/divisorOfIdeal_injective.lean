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

/-- **Two nonzero ideals of a Dedekind domain with the same order at every height-one prime are
equal.**

Indeed an ideal of a Dedekind domain is the intersection `⨅_v v ^ (val_v I)` of the maximal powers
of the height-one primes `v` dividing it (`Ideal.iInf_maxPowDividing_eq`), where
`val_v I = (Associates.mk v.asIdeal).count (Associates.mk I).factors` is the multiplicity of `v`
in the prime factorization of `I`.  If all these multiplicities agree, the two intersections do. -/
theorem eq_of_forall_count_eq {R : Type u} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
        (Associates.mk v.asIdeal).count (Associates.mk I).factors =
        (Associates.mk v.asIdeal).count (Associates.mk J).factors) : I = J := by
  rw [← Ideal.iInf_maxPowDividing_eq hI, ← Ideal.iInf_maxPowDividing_eq hJ]
  congr 1
  funext v
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing,
      IsDedekindDomain.HeightOneSpectrum.maxPowDividing, h v]

namespace Work.SymQuot.DivOf
open Work.CurveBasics

/-- **The divisor of an ideal determines the ideal**: for a curve `C` over a field `F`, a nonempty
affine open `V ⊆ C` with `Γ(C,V)` a Dedekind domain, and nonzero ideals `J, K ⊆ Γ(C,V)`, the
divisors `Σ_z v_z(J) [z]` and `Σ_z v_z(K) [z]` agree only if `J = K`.

Indeed `divisorOfIdeal C V hV J` is the function `z ↦ placeOrder C V J z hz` on the places of `V`
(`divisorOfIdeal_apply`), so equality of divisors is equality of all the orders of vanishing.  The
places of `V` correspond bijectively to the height-one primes of `Γ(C,V)`, a place `z` being sent
to the prime `placeIdeal C V z hz` (`heightOneSpectrum_equiv_place`), and there `placeOrder` is
exactly `idealOrder`, the multiplicity of the prime in the factorization of the ideal.  All
multiplicities agree, so the ideals agree (`eq_of_forall_count_eq`). -/
theorem divisorOfIdeal_injective {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    {J K : Ideal Γ(C.left, V)} (hJ : J ≠ ⊥) (hK : K ≠ ⊥)
    (h : divisorOfIdeal C V hV J = divisorOfIdeal C V hV K) : J = K := by
  -- equality of the orders of vanishing at every place of `V`
  have hplaceOrder : ∀ z (hz : z.point ∈ V), placeOrder C V J z hz = placeOrder C V K z hz := by
    intro z hz
    have hz' : (divisorOfIdeal C V hV J) z = (divisorOfIdeal C V hV K) z :=
      congrArg (fun D : C.Div => D z) h
    rw [divisorOfIdeal_apply, divisorOfIdeal_apply, dite_eq_left hz, dite_eq_left hz] at hz'
    exact_mod_cast hz'
  -- the places of `V` are the height-one primes of `Γ(C,V)`
  obtain ⟨e, he⟩ := heightOneSpectrum_equiv_place (C := C) hV
  have hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum Γ(C.left, V),
      idealOrder C V J v = idealOrder C V K v := by
    intro v
    -- the place `z` of `V` corresponding to the prime `v`
    have hzv : v.asIdeal = placeIdeal C V (e.symm v).1 (e.symm v).2 := by
      have := he (e.symm v)
      rwa [Equiv.apply_symm_apply] at this
    have hord := hplaceOrder (e.symm v).1 (e.symm v).2
    have e1 : idealOrder C V J v = placeOrder C V J (e.symm v).1 (e.symm v).2 := by
      rw [idealOrder, placeOrder, hzv]
    have e2 : idealOrder C V K v = placeOrder C V K (e.symm v).1 (e.symm v).2 := by
      rw [idealOrder, placeOrder, hzv]
    rw [e1, e2, hord]
  exact eq_of_forall_count_eq hJ hK hcount

end Work.SymQuot.DivOf

open Work.CurveBasics

/-- The statement at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.divisorOfIdeal_injective` (the declaration above sits in
the doubly opened namespace inherited from this file's original skeleton). -/
theorem divisorOfIdeal_injective {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    {J K : Ideal Γ(C.left, V)} (hJ : J ≠ ⊥) (hK : K ≠ ⊥)
    (h : divisorOfIdeal C V hV J = divisorOfIdeal C V hV K) : J = K :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.divisorOfIdeal_injective V hV hJ hK h

end Work.SymQuot.DivOf
