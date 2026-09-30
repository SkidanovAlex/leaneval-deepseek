import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open scoped IntermediateField.algebraAdjoinAdjoin

namespace Work.CurveBasics.Order

open Work.CurveBasics

noncomputable section

variable {k : Type*} [Field k]

/-- Evaluation at the constant term induces the `k`-algebra isomorphism
`k[h] ⧸ (h) ≃+* k`. -/
def kxOrdIdealQuotEquiv (C : Curve k) (h : C.functionField) (hh : Transcendental k h) :
    (C.ordBase h ⧸ C.ordIdeal h) ≃+* k :=
  (Ideal.quotEquivOfEq (Curve.kx_span_gen_eq_ker C h hh)).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Curve.kxEvalZero C h hh).toRingHom)
      (fun c => ⟨algebraMap k (C.ordBase h) c, (Curve.kxEvalZero C h hh).commutes c⟩))

lemma kxOrdIdealQuotEquiv_mk (C : Curve k) (h : C.functionField) (hh : Transcendental k h)
    (y : C.ordBase h) :
    kxOrdIdealQuotEquiv C h hh (Ideal.Quotient.mk _ y) = Curve.kxEvalZero C h hh y := by
  simp only [kxOrdIdealQuotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

open Work.CurveBasics in
theorem inertiaDeg_kxPrimeOfPlace_eq_finrank_k {k : Type*} [Field k] (C : Curve k)
    (h : C.functionField) (hh : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase h) (C.ordClosure h)]
    (Q : C.Place) (hQ : 0 < C.ordAt h Q) :
    (kxPrimeOfPlace C h Q hQ.le).inertiaDeg (C.ordBase h)
      = Module.finrank k (C.ordClosure h ⧸ kxPrimeOfPlace C h Q hQ.le) := by
  classical
  set P := kxPrimeOfPlace C h Q hQ.le with hPdef
  have hLies : P.LiesOver (C.ordIdeal h) := kxPrimeOfPlace_liesOver C h hh Q hQ
  have hPprime : P.IsPrime := kxPrimeOfPlace_isPrime C h Q hQ.le
  haveI hInt : Algebra.IsIntegral (C.ordBase h) (C.ordClosure h) :=
    IsIntegralClosure.isIntegral_algebra (R := C.ordBase h) (B := C.functionField)
  have hpbot : C.ordIdeal h = P.under (C.ordBase h) := hLies.over
  have hpmax : (P.under (C.ordBase h)).IsMaximal := hpbot ▸ kxIdeal_isMaximal C h hh
  haveI : (P.under (C.ordBase h)).IsMaximal := hpmax
  haveI : P.IsPrime := hPprime
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (P.under (C.ordBase h))
  rw [Ideal.inertiaDeg_eq_of_isMaximal (P.under (C.ordBase h)) P]
  refine Algebra.finrank_eq_of_equiv_equiv
    ((Ideal.quotEquivOfEq hpbot.symm).trans (kxOrdIdealQuotEquiv C h hh))
    (RingEquiv.refl (C.ordClosure h ⧸ P)) ?_
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  show (algebraMap k (C.ordClosure h ⧸ P))
      (((Ideal.quotEquivOfEq hpbot.symm).trans (kxOrdIdealQuotEquiv C h hh))
        (Ideal.Quotient.mk (P.under (C.ordBase h)) y))
    = (algebraMap (C.ordBase h ⧸ P.under (C.ordBase h)) (C.ordClosure h ⧸ P))
        (Ideal.Quotient.mk (P.under (C.ordBase h)) y)
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, kxOrdIdealQuotEquiv_mk]
  have h1 : (algebraMap k (C.ordClosure h ⧸ P)) (Curve.kxEvalZero C h hh y)
      = Ideal.Quotient.mk P
          (algebraMap k (C.ordClosure h) (Curve.kxEvalZero C h hh y)) :=
    (Ideal.Quotient.mk_algebraMap k P (Curve.kxEvalZero C h hh y)).symm
  have h2 : (algebraMap (C.ordBase h ⧸ P.under (C.ordBase h)) (C.ordClosure h ⧸ P))
        (Ideal.Quotient.mk (P.under (C.ordBase h)) y)
      = Ideal.Quotient.mk P (algebraMap (C.ordBase h) (C.ordClosure h) y) := by
    rw [show (algebraMap (C.ordBase h ⧸ P.under (C.ordBase h)) (C.ordClosure h ⧸ P))
        = Ideal.quotientMap P (algebraMap (C.ordBase h) (C.ordClosure h))
            le_rfl from rfl]
    rw [Ideal.quotientMap_mk]
  rw [h1, h2, Ideal.Quotient.eq]
  have hker : y - algebraMap k (C.ordBase h) (Curve.kxEvalZero C h hh y) ∈ C.ordIdeal h := by
    rw [show C.ordIdeal h = RingHom.ker (Curve.kxEvalZero C h hh).toRingHom
        from Curve.kx_span_gen_eq_ker C h hh]
    rw [RingHom.mem_ker]
    simp
  have hkey : algebraMap (C.ordBase h) (C.ordClosure h) y
      - algebraMap k (C.ordClosure h) (Curve.kxEvalZero C h hh y) ∈ P := by
    have hmem : algebraMap (C.ordBase h) (C.ordClosure h)
        (y - algebraMap k (C.ordBase h) (Curve.kxEvalZero C h hh y)) ∈ P :=
      (Ideal.mem_under (C.ordBase h) P).mp (hpbot ▸ hker)
    simpa only [map_sub, IsScalarTower.algebraMap_apply k (C.ordBase h) (C.ordClosure h)]
      using hmem
  rw [← neg_sub]
  exact neg_mem hkey

end

end Work.CurveBasics.Order
