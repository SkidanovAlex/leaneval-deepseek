import Mathlib
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.KeyLemma.Curve.p1FunctionField
import Submission.Work.KeyLemma.Curve.card_embeddings_prime_over
import Submission.Work.CurveBasics.Order.ramificationIdx_eq_ordAt
import Submission.Work.CurveBasics.Order.inertiaDeg_eq_residueDegree
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.sum_ord_pos_eq_finrank_general
import Submission.Work.Charts.place_degree_eq_one_of_isAlgClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.KeyLemma.Curve

universe u

set_option synthInstance.maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry Limits

/-- **The number of branches specialising to a zero `Q` of `h` is `ord_Q h`** (corrected form of
`Work.KeyLemma.Curve.card_branches`).

This is the statement of `Work.KeyLemma.Curve.card_branches` with one change: the two
compatibilities of the algebra structures on `N` that `card_embeddings_prime_over` needs are
listed *as explicit hypotheses* (`hKE`, `hAE`) instead of being left to typeclass resolution.

Every hypothesis of the form `[IsScalarTower ↥S ↥T N]` in which `S` is a `Subalgebra` (or
`IntermediateField`) of `T ⊆ K(C)` is *automatically true* in Lean, because typeclass search
resolves the two `SMul` instances on `↥S` through the ambient action
(`Subalgebra.instSMulSubtypeMem`, `IntermediateField.instSMulSubtypeMem`) rather than through the
`Algebra` structure `[Algebra ↥S N]` which the hypothesis is meant to constrain.  Concretely, in
the context of `card_branches` one has `x • (1 : N) = (x : ↥C.functionField) • (1 : N)` by `rfl`,
so `IsScalarTower ↥(baseField C h) ↥C.functionField N` reduces to the identity
`algebraMap ↥C.functionField N ((x : E) * y) * z
  = algebraMap ↥C.functionField N (x : E) * (algebraMap ↥C.functionField N y * z)`,
which holds for *any* ring hom `↥C.functionField → N`, independently of `[Algebra ↥(baseField C h)
N]`.

The content that such a hypothesis is supposed to carry -- that `N` contains `E = K(C)` over
`K = k(h)` (the "normal closure" hypothesis of the blueprint) -- is therefore exactly the equation
`hKE` below, and similarly `hAE` for `k[h] = C.ordBase h ⊆ C.functionField ⊆ N`.  With these two
explicit hypotheses the intended proof goes through: the count is
`e(q|(h)) · f(q|(h)) = ord_Q h` by `card_embeddings_prime_over`,
`ramificationIdx_eq_ordAt`, `inertiaDeg_eq_residueDegree` and `[κ(Q) : k] = 1` (as `k = k̄`). -/
theorem card_branches_fixed {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) (hh : Transcendental k h)
    [FiniteDimensional ↥(baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(baseField C h) ↥C.functionField]
    {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(baseField C h) N]
    [IsGalois ↥(baseField C h) N]
    [FiniteDimensional ↥(baseField C h) N]
    [Algebra ↥(C.ordBase h) N]
    [IsScalarTower ↥(C.ordBase h) ↥(baseField C h) N]
    [Algebra ↥C.functionField N]
    [IsScalarTower ↥(baseField C h) ↥C.functionField N]
    (hKE : (algebraMap ↥(baseField C h) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(baseField C h) ↥C.functionField))
    (hAE : (algebraMap ↥(C.ordBase h) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(C.ordBase h) ↥C.functionField))
    [IsFractionRing ↥(integralClosure ↥(C.ordBase h) N) N]
    (P : Ideal ↥(integralClosure ↥(C.ordBase h) N)) [P.IsPrime] [P.LiesOver (C.ordIdeal h)]
    (Q : C.Place) (hQ : 0 < C.ordAt h Q) :
    Nat.card {σ : ↥C.functionField →ₐ[↥(baseField C h)] N //
      ∀ x ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le, ∃ c ∈ P,
        algebraMap ↥(integralClosure ↥(C.ordBase h) N) N c
          = σ (algebraMap ↥(C.ordClosure h) ↥C.functionField x)}
      = (C.ordAt h Q).toNat := by
  -- the ideals `(h)` and `q_Q` are prime
  haveI hprime : (C.ordIdeal h).IsPrime := Work.CurveBasics.Order.ordIdeal_isPrime C h hh
  haveI hqprime : (Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le).IsPrime :=
    Work.CurveBasics.kxPrimeOfPlace_isPrime C h Q hQ.le
  haveI hqover : (Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le).LiesOver (C.ordIdeal h) :=
    Work.CurveBasics.Order.kxPrimeOfPlace_liesOver C h hh Q hQ
  -- the compatibilities, in the `Algebra.toSMul` shape that `card_embeddings_prime_over` wants
  haveI hstKE := IsScalarTower.of_algebraMap_eq
    (R := ↥(baseField C h)) (S := ↥C.functionField) (A := N) (fun x => by rw [hKE]; rfl)
  haveI hstAE := IsScalarTower.of_algebraMap_eq
    (R := ↥(C.ordBase h)) (S := ↥C.functionField) (A := N) (fun x => by rw [hAE]; rfl)
  haveI hstAKE := IsScalarTower.of_algebraMap_eq
    (R := ↥(C.ordBase h)) (S := ↥(baseField C h)) (A := ↥C.functionField) (fun x => rfl)
  -- auxiliary self-towers needed to apply `IsIntegral.map` over `k[h]`
  haveI hstAAE : IsScalarTower ↥(C.ordBase h) ↥(C.ordBase h) ↥C.functionField :=
    IsScalarTower.of_algebraMap_eq (fun x => by simp)
  haveI hstAAN := IsScalarTower.of_algebraMap_eq
    (R := ↥(C.ordBase h)) (S := ↥(C.ordBase h)) (A := N) (fun x => by simp)
  -- the canonical `k[h]`-algebra map from the integral closure of `k[h]` in `K(C)` to that in `N`
  let φ : ↥(C.ordClosure h) →ₐ[↥(C.ordBase h)] N :=
    (IsScalarTower.toAlgHom ↥(C.ordBase h) ↥C.functionField N).comp
      (Subalgebra.val (C.ordClosure h))
  have hφ : ∀ b : ↥(C.ordClosure h),
      φ b = (IsScalarTower.toAlgHom ↥(C.ordBase h) ↥C.functionField N) (b : ↥C.functionField) := by
    intro b
    dsimp only [φ]
    rw [AlgHom.comp_apply, Subalgebra.coe_val]
  have hmem : ∀ b : ↥(C.ordClosure h), φ b ∈ integralClosure ↥(C.ordBase h) N := by
    intro b
    rw [mem_integralClosure_iff, hφ b]
    have hb : IsIntegral ↥(C.ordBase h) (b : ↥C.functionField) :=
      (IsIntegralClosure.isIntegral_iff (R := ↥(C.ordBase h)) (A := ↥(C.ordClosure h))
        (B := ↥C.functionField)).mpr ⟨b, rfl⟩
    exact IsIntegral.map (R := ↥(C.ordBase h)) (A := ↥(C.ordBase h))
      (B := ↥C.functionField) (C := N)
      (f := IsScalarTower.toAlgHom ↥(C.ordBase h) ↥C.functionField N) hb
  let f : ↥(C.ordClosure h) →ₐ[↥(C.ordBase h)] ↥(integralClosure ↥(C.ordBase h) N) :=
    φ.codRestrict _ hmem
  letI : Algebra ↥(C.ordClosure h) ↥(integralClosure ↥(C.ordBase h) N) := f.toRingHom.toAlgebra
  haveI hstABC : IsScalarTower ↥(C.ordBase h) ↥(C.ordClosure h)
      ↥(integralClosure ↥(C.ordBase h) N) :=
    IsScalarTower.of_algebraMap_eq (R := ↥(C.ordBase h)) (S := ↥(C.ordClosure h))
      (A := ↥(integralClosure ↥(C.ordBase h) N)) (fun x => (f.commutes x).symm)
  -- the algebraic count
  have hcount := card_embeddings_prime_over (A := ↥(C.ordBase h)) (K := ↥(baseField C h))
    (E := ↥C.functionField) (L := N) (B := ↥(C.ordClosure h))
    (C := ↥(integralClosure ↥(C.ordBase h) N)) (p := C.ordIdeal h)
    (q := Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le) (P := P)
  rw [hcount]
  -- `e = ord_Q h` and `f = [κ(Q) : k] = 1`
  have hram : (((Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le).ramificationIdx
        ↥(C.ordBase h) : ℕ) : ℤ) = C.ordAt h Q :=
    Work.CurveBasics.Order.ramificationIdx_eq_ordAt C h hh Q hQ
  have hfield : C.hom.residueDegree Q.point = 1 :=
    Work.Charts.place_degree_eq_one_of_isAlgClosed C Q
  have hiner : (Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le).inertiaDeg ↥(C.ordBase h) = 1 := by
    have h1 := Work.CurveBasics.Order.inertiaDeg_eq_residueDegree C h hh Q hQ
    rw [hfield] at h1
    exact Int.ofNat_inj.mp h1
  have he : (Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le).ramificationIdx ↥(C.ordBase h)
      = (C.ordAt h Q).toNat := by
    refine Int.ofNat_inj.mp ?_
    exact hram.trans (Int.toNat_of_nonneg hQ.le).symm
  rw [he, hiner, mul_one]

end Work.KeyLemma.Curve
