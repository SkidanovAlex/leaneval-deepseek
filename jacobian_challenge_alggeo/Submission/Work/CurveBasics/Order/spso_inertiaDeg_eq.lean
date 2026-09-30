import Mathlib
import Submission.Work.CurveBasics.Order.SumPrimesAux
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.kxClosure_residue_surjective
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open Work.CurveBasics
open scoped IntermediateField.algebraAdjoinAdjoin
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 8000000

namespace Work.CurveBasics.Order

noncomputable section

variable {k : Type*} [Field k]

/-- The `k`-algebra structure on the valuation subring at a place, induced by the inclusion
`k ⊆ K(C)`. -/
noncomputable instance instAlgebraValuationSubring (C : Curve k) (Q : C.Place) :
    Algebra k ↥(Q.valuationSubring) :=
  ((algebraMap k C.functionField).codRestrict Q.valuationSubring
    (fun c => Curve.Place.algebraMap_mem_valuationSubring C Q c)).toAlgebra

/-- If `e : K →+* κ` is a bijective ring homomorphism of fields and the two scalar actions on `M`
satisfy `a • m = e a • m`, then `M` has the same `finrank` over `K` and over `κ`. -/
private lemma finrank_eq_of_ringHom {K κ M : Type*} [Field K] [Field κ] [AddCommGroup M]
    [Module κ M] [Module K M] (e : K →+* κ) (he : Function.Bijective e)
    (h : ∀ (a : K) (m : M), a • m = e a • m) :
    Module.finrank K M = Module.finrank κ M := by
  letI : Algebra K κ := e.toAlgebra
  haveI : IsScalarTower K κ M := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]
    exact (h x (y • z)).symm⟩
  have h1 : Module.finrank K κ = 1 := by
    have hbij : Function.Bijective (Algebra.linearMap K κ) := by
      have : ⇑(Algebra.linearMap K κ) = ⇑e := by ext a; rw [Algebra.linearMap_apply]; rfl
      rw [this]; exact he
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap K κ) hbij)).symm.trans
      (Module.finrank_self K)
  have := Module.finrank_mul_finrank K κ M
  rw [h1, one_mul] at this
  exact this.symm

/-- The evaluation `k[x] → k` at the constant term is surjective. -/
private lemma kxEvalZero_surjective {C : Curve k} {x : C.functionField}
    (hx : Transcendental k x) : Function.Surjective (Curve.kxEvalZero C x hx) := by
  intro c
  exact ⟨algebraMap k (C.ordBase x) c, by rw [AlgHom.commutes, Algebra.algebraMap_self_apply]⟩

/-- The kernel of evaluation at the constant term is the ideal `(x) = k[x] · x`. -/
private lemma kxEvalZero_ker_eq_ordIdeal {C : Curve k} {x : C.functionField}
    (hx : Transcendental k x) :
    Curve.ordIdeal C x = RingHom.ker (Curve.kxEvalZero C x hx) := by
  convert Curve.kx_span_gen_eq_ker C x hx using 1
  · simp [Curve.ordIdeal, Curve.kxGen]
  · rfl

/-- For `z : k[x]`, the difference `z - z(0)` lies in the prime attached to a place at which `x`
vanishes. -/
private lemma sub_algebraMap_kxEvalZero_mem {C : Curve k} {x : C.functionField}
    (hx : Transcendental k x) {Q : C.Place} (hQ : 0 < C.ordAt x Q) (z : C.ordBase x) :
    (algebraMap (C.ordBase x) (C.ordClosure x) z
      - algebraMap k (C.ordClosure x) (Curve.kxEvalZero C x hx z))
    ∈ kxPrimeOfPlace C x Q hQ.le := by
  have hLies := kxPrimeOfPlace_liesOver C x hx Q hQ
  have hker := kxEvalZero_ker_eq_ordIdeal (C := C) (x := x) hx
  have hmem_ker : z - algebraMap k (C.ordBase x) (Curve.kxEvalZero C x hx z)
      ∈ Curve.ordIdeal C x := by
    rw [hker, RingHom.mem_ker]
    show Curve.kxEvalZero C x hx
      (z - algebraMap k (C.ordBase x) (Curve.kxEvalZero C x hx z)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hmem_under : z - algebraMap k (C.ordBase x) (Curve.kxEvalZero C x hx z)
      ∈ (kxPrimeOfPlace C x Q hQ.le).under (C.ordBase x) := by
    rw [← hLies.over]; exact hmem_ker
  rw [Ideal.mem_under] at hmem_under
  convert hmem_under using 1
  rw [map_sub, IsScalarTower.algebraMap_apply k (C.ordBase x) (C.ordClosure x)]

/-- **Step D.** The inertia degree of the prime attached to a place at which `x` vanishes is the
`k`-dimension of the residue ring `k[x]^int ⧸ q`. -/
private lemma inertiaDeg_eq_finrank_quotient (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase x) (C.ordClosure x)]
    (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    (kxPrimeOfPlace C x Q hQ.le).inertiaDeg (C.ordBase x)
      = Module.finrank k (C.ordClosure x ⧸ kxPrimeOfPlace C x Q hQ.le) := by
  have hLies := kxPrimeOfPlace_liesOver C x hx Q hQ
  haveI : (kxPrimeOfPlace C x Q hQ.le).IsPrime := kxPrimeOfPlace_isPrime C x Q hQ.le
  haveI : Algebra.IsIntegral (C.ordBase x) (C.ordClosure x) :=
    IsIntegralClosure.isIntegral_algebra (R := C.ordBase x) (B := C.functionField)
  haveI hp_max : ((kxPrimeOfPlace C x Q hQ.le).under (C.ordBase x)).IsMaximal := by
    rw [← hLies.over]; exact kxIdeal_isMaximal C x hx
  haveI : (kxPrimeOfPlace C x Q hQ.le).IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (kxPrimeOfPlace C x Q hQ.le)
      ((kxPrimeOfPlace C x Q hQ.le).under (C.ordBase x))
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    ((kxPrimeOfPlace C x Q hQ.le).under (C.ordBase x)) (kxPrimeOfPlace C x Q hQ.le)]
  have hker := kxEvalZero_ker_eq_ordIdeal (C := C) (x := x) hx
  have hsurj := kxEvalZero_surjective (C := C) (x := x) hx
  let eA : AlgEquiv k ((C.ordBase x) ⧸ Curve.ordIdeal C x) k :=
    (Ideal.quotientEquivAlgOfEq k hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  let iA : AlgEquiv k
      ((C.ordBase x) ⧸ (kxPrimeOfPlace C x Q hQ.le).under (C.ordBase x)) k :=
    (Ideal.quotientEquivAlgOfEq k hLies.over.symm).trans eA
  have hi (y : C.ordBase x) : iA (Ideal.Quotient.mk _ y) = Curve.kxEvalZero C x hx y := by
    change eA ((Ideal.quotientEquivAlgOfEq k hLies.over.symm) (Ideal.Quotient.mk _ y))
      = Curve.kxEvalZero C x hx y
    rw [Ideal.quotientEquivAlgOfEq_mk]
    change ((Ideal.quotientEquivAlgOfEq k hker).trans
        (Ideal.quotientKerAlgEquivOfSurjective hsurj))
      (Ideal.Quotient.mk (Curve.ordIdeal C x) y) = Curve.kxEvalZero C x hx y
    rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
  refine Algebra.finrank_eq_of_equiv_equiv (iA : _ ≃+* _) (RingEquiv.refl _) ?_
  ext z
  show (algebraMap k (C.ordClosure x ⧸ kxPrimeOfPlace C x Q hQ.le)) (iA (Ideal.Quotient.mk _ z))
    = (algebraMap ((C.ordBase x) ⧸ (kxPrimeOfPlace C x Q hQ.le).under (C.ordBase x))
        (C.ordClosure x ⧸ kxPrimeOfPlace C x Q hQ.le)) (Ideal.Quotient.mk _ z)
  rw [hi z]
  rw [← Ideal.Quotient.mk_algebraMap k]
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simpa [neg_sub] using neg_mem (sub_algebraMap_kxEvalZero_mem (C := C) hx hQ z)

/-- `k[x]^int ⧸ q` is `k`-linearly isomorphic to the residue field of the valuation subring
`O_Q`. -/
private lemma finrank_quotient_eq_finrank_valSubringResidueField (C : Curve k)
    (x : C.functionField) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase x) (C.ordClosure x)]
    (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    Module.finrank k (C.ordClosure x ⧸ kxPrimeOfPlace C x Q hQ.le)
      = Module.finrank k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) := by
  classical
  let hle := kxClosure_le_valuationSubring C x Q hQ.le
  let φ : C.ordClosure x →+* IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    (IsLocalRing.residue ↥(Q.valuationSubring)).comp (Subring.inclusion hle)
  have hO_coe (c : k) :
      ((algebraMap k ↥(Q.valuationSubring) c : ↥(Q.valuationSubring)) : C.functionField)
        = algebraMap k C.functionField c := rfl
  have hφ_smul (c : k) : φ (algebraMap k (C.ordClosure x) c) =
      algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) c := by
    have h2 : Subring.inclusion hle (algebraMap k (C.ordClosure x) c)
        = algebraMap k ↥(Q.valuationSubring) c := by
      apply Subtype.ext
      rw [Subring.coe_inclusion, hO_coe]
      rfl
    show IsLocalRing.residue ↥(Q.valuationSubring)
      (Subring.inclusion hle (algebraMap k (C.ordClosure x) c)) = _
    rw [h2, IsScalarTower.algebraMap_apply k ↥(Q.valuationSubring)
        (IsLocalRing.ResidueField ↥(Q.valuationSubring)), IsLocalRing.ResidueField.algebraMap_eq]
  have hker : RingHom.ker φ = kxPrimeOfPlace C x Q hQ.le := by
    show RingHom.ker
      ((IsLocalRing.residue ↥(Q.valuationSubring)).comp (Subring.inclusion hle)) = _
    rw [← RingHom.comap_ker (IsLocalRing.residue ↥(Q.valuationSubring)) (Subring.inclusion hle),
      IsLocalRing.ker_residue]
    rfl
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, hb⟩ := Work.CurveBasics.Order.kxClosure_residue_surjective C x hx Q hQ y
    refine ⟨b, ?_⟩
    show IsLocalRing.residue ↥(Q.valuationSubring) (Subring.inclusion hle b) = y
    rw [show Subring.inclusion hle b
        = (⟨(b : C.functionField), hle b.2⟩ : ↥(Q.valuationSubring)) from
      Subtype.ext (by rw [Subring.coe_inclusion])]
    exact hb
  let φalg : C.ordClosure x →ₐ[k] IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    { φ with commutes' := hφ_smul }
  have hsurj' : Function.Surjective φalg := hsurj
  have hker' : RingHom.ker φalg = kxPrimeOfPlace C x Q hQ.le := hker
  let Ψ : AlgEquiv k (C.ordClosure x ⧸ kxPrimeOfPlace C x Q hQ.le)
      (IsLocalRing.ResidueField ↥(Q.valuationSubring)) :=
    (Ideal.quotientEquivAlgOfEq k hker').symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj')
  exact Ψ.toLinearEquiv.finrank_eq

/-- **Step E.** The residue field of the valuation subring at a place has `k`-dimension equal to
the residue degree of the place. -/
private lemma finrank_valSubringResidueField_eq_residueDegree (C : Curve k)
    (x : C.functionField) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase x) (C.ordClosure x)]
    (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    Module.finrank k (IsLocalRing.ResidueField ↥(Q.valuationSubring))
      = C.hom.residueDegree Q.point := by
  classical
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  letI instAlgSt : Algebra k (C.left.presheaf.stalk Q.point) := Linear.instAlgebraStalk C Q
  haveI hST : IsScalarTower k (C.left.presheaf.stalk Q.point) C.functionField :=
    Linear.isScalarTower_stalk_field C Q
  let E : (C.left.presheaf.stalk Q.point) ≃+* ↥(Q.valuationSubring) :=
    IsDiscreteValuationRing.equivValuationSubring
  have hE_coe (a : C.left.presheaf.stalk Q.point) :
      ((E a : ↥(Q.valuationSubring)) : C.functionField) =
        algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := by
    dsimp only [E]
    rw [IsDiscreteValuationRing.equivValuationSubring]; rfl
  have hO_coe (c : k) :
      ((algebraMap k ↥(Q.valuationSubring) c : ↥(Q.valuationSubring)) : C.functionField)
        = algebraMap k C.functionField c := rfl
  have hE_smul (c : k) : E (algebraMap k (C.left.presheaf.stalk Q.point) c) =
      algebraMap k ↥(Q.valuationSubring) c := by
    apply Subtype.ext
    rw [hE_coe, hO_coe, IsScalarTower.algebraMap_apply k (C.left.presheaf.stalk Q.point)
      C.functionField]
  have hmlin (c : k) : IsLocalRing.ResidueField.mapEquiv E
      (show IsLocalRing.ResidueField (C.left.presheaf.stalk Q.point) from
        algebraMap k (C.left.residueField Q.point) c) =
      algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) c := by
    rw [← Linear.residue_algebraMap_eq C Q c]
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rw [show (E : (C.left.presheaf.stalk Q.point) →+* ↥(Q.valuationSubring))
        (algebraMap k (C.left.presheaf.stalk Q.point) c)
        = algebraMap k ↥(Q.valuationSubring) c from hE_smul c]
    rw [IsScalarTower.algebraMap_apply k ↥(Q.valuationSubring)
        (IsLocalRing.ResidueField ↥(Q.valuationSubring)), IsLocalRing.ResidueField.algebraMap_eq]
  let eRF : AlgEquiv k (C.left.residueField Q.point)
      (IsLocalRing.ResidueField ↥(Q.valuationSubring)) :=
    { IsLocalRing.ResidueField.mapEquiv E with commutes' := hmlin }
  rw [← eRF.toLinearEquiv.finrank_eq]
  exact (Work.CurveBasics.Place.degree_eq_finrank Q).symm

/-- **The inertia degree of the prime attached to a place is the residue degree of the place.**

Let `C` be a curve over `k`, `x : K(C)` transcendental, `A = k[x]`, `B = k[x]^int`, with
`K(C)/k(x)` finite and `B` a finite `A`-module (the separability-free setting of
`Work.CurveBasics.Order.spso_val_eq_atPrime`).  For a place `Q` with `0 < ord_Q x`, the prime
`q := kxPrimeOfPlace C x Q hQ.le = B ∩ 𝔪_Q` has inertia degree `[κ(Q) : k]`. -/
theorem spso_inertiaDeg_eq {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase x) (C.ordClosure x)]
    (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    ((kxPrimeOfPlace C x Q hQ.le).inertiaDeg (C.ordBase x) : ℤ)
      = (C.hom.residueDegree Q.point : ℤ) := by
  have hnat : (kxPrimeOfPlace C x Q hQ.le).inertiaDeg (C.ordBase x)
      = C.hom.residueDegree Q.point :=
    (inertiaDeg_eq_finrank_quotient C x hx Q hQ).trans
      ((finrank_quotient_eq_finrank_valSubringResidueField C x hx Q hQ).trans
        (finrank_valSubringResidueField_eq_residueDegree C x hx Q hQ))
  exact_mod_cast hnat

end

end Work.CurveBasics.Order
