import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Place.degree_eq_finrank
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.kxClosure_residue_surjective
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1600000

namespace Work.CurveBasics.Order

open Work.CurveBasics

noncomputable section

/-- The underlying element of the field of fractions of
`IsDiscreteValuationRing.equivValuationSubring`. -/
theorem isDiscreteValuationRing_equivValuationSubring_coe {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] (x : A) :
    ((IsDiscreteValuationRing.equivValuationSubring (A := A) (K := K) x :
        ↥((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring) : K) =
      algebraMap A K x := by
  rw [IsDiscreteValuationRing.equivValuationSubring]; rfl

open Work.CurveBasics in
theorem kxPrimeOfPlace_residueField_finrank {k : Type*} [Field k] (C : Curve k)
    (h : C.functionField) (hh : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase h) (C.ordClosure h)]
    (Q : C.Place) (hQ : 0 < C.ordAt h Q) :
    Module.finrank k (C.ordClosure h ⧸ kxPrimeOfPlace C h Q hQ.le)
      = C.hom.residueDegree Q.point := by
  classical
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  letI : Algebra k (C.left.presheaf.stalk Q.point) := Linear.instAlgebraStalk C Q
  letI : Algebra k ↑(C.left.residueField Q.point) := Curve.Place.instAlgebraResidueField C Q
  haveI hST : IsScalarTower k (C.left.presheaf.stalk Q.point) C.functionField :=
    Linear.isScalarTower_stalk_field C Q
  -- the `k`-algebra structure on the valuation subring, induced by `k ⊆ K(C)`
  letI instAlgO : Algebra k ↥(Q.valuationSubring) :=
    ((algebraMap k C.functionField).codRestrict Q.valuationSubring
      (fun c => Curve.Place.algebraMap_mem_valuationSubring C Q c)).toAlgebra
  have hO_coe (c : k) :
      ((algebraMap k ↥(Q.valuationSubring) c : ↥(Q.valuationSubring)) : C.functionField) =
        algebraMap k C.functionField c := rfl
  -- the ring isomorphism between the local ring at `Q` and the valuation subring
  let E : (C.left.presheaf.stalk Q.point) ≃+* ↥(Q.valuationSubring) :=
    IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk Q.point)
      (K := C.functionField)
  have hE_coe (x : C.left.presheaf.stalk Q.point) :
      ((E x : ↥(Q.valuationSubring)) : C.functionField) =
        algebraMap (C.left.presheaf.stalk Q.point) C.functionField x := by
    dsimp only [E]
    exact isDiscreteValuationRing_equivValuationSubring_coe x
  have hE_smul (c : k) :
      (E : C.left.presheaf.stalk Q.point →+* ↥(Q.valuationSubring))
        (algebraMap k (C.left.presheaf.stalk Q.point) c) =
        algebraMap k ↥(Q.valuationSubring) c := by
    rw [RingEquiv.coe_toRingHom E]
    apply Subtype.ext
    rw [hE_coe, hO_coe]
    rw [IsScalarTower.algebraMap_apply k (C.left.presheaf.stalk Q.point) C.functionField]
  -- the induced isomorphism of residue fields is `k`-linear
  have hmlin (c : k) : IsLocalRing.ResidueField.mapEquiv E
      (algebraMap k ↑(C.left.residueField Q.point) c) =
      algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) c := by
    calc IsLocalRing.ResidueField.mapEquiv E (algebraMap k ↑(C.left.residueField Q.point) c)
        = IsLocalRing.ResidueField.mapEquiv E
            (IsLocalRing.residue (C.left.presheaf.stalk Q.point)
              (algebraMap k (C.left.presheaf.stalk Q.point) c)) := by
          rw [← Linear.residue_algebraMap_eq C Q c]
      _ = IsLocalRing.residue ↥(Q.valuationSubring)
            ((E : C.left.presheaf.stalk Q.point →+* ↥(Q.valuationSubring))
              (algebraMap k (C.left.presheaf.stalk Q.point) c)) := by
          rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      _ = IsLocalRing.residue ↥(Q.valuationSubring)
            (algebraMap k ↥(Q.valuationSubring) c) := by rw [hE_smul]
      _ = algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) c := by
          rw [IsScalarTower.algebraMap_apply k ↥(Q.valuationSubring)
              (IsLocalRing.ResidueField ↥(Q.valuationSubring)),
            IsLocalRing.ResidueField.algebraMap_eq]
  let eRF : ↑(C.left.residueField Q.point) ≃ₗ[k]
      IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    LinearEquiv.ofBijective
      ({ toFun := fun x : ↑(C.left.residueField Q.point) =>
          IsLocalRing.ResidueField.mapEquiv E x
         map_add' := fun x y => map_add _ x y
         map_smul' := fun m x => by
           have h1 : m • x = algebraMap k ↑(C.left.residueField Q.point) m * x :=
             Algebra.smul_def m x
           have h2 : (RingHom.id k) m • IsLocalRing.ResidueField.mapEquiv E x =
               algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) m *
                 IsLocalRing.ResidueField.mapEquiv E x := by
             rw [Algebra.smul_def, RingHom.id_apply]
           calc IsLocalRing.ResidueField.mapEquiv E (m • x)
               = IsLocalRing.ResidueField.mapEquiv E
                   (algebraMap k ↑(C.left.residueField Q.point) m * x) :=
                 congrArg (IsLocalRing.ResidueField.mapEquiv E) h1
             _ = IsLocalRing.ResidueField.mapEquiv E
                   (algebraMap k ↑(C.left.residueField Q.point) m) *
                 IsLocalRing.ResidueField.mapEquiv E x :=
                 map_mul (IsLocalRing.ResidueField.mapEquiv E) _ _
             _ = algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) m *
                 IsLocalRing.ResidueField.mapEquiv E x :=
                 congrArg (fun z => z * IsLocalRing.ResidueField.mapEquiv E x) (hmlin m)
             _ = (RingHom.id k) m • IsLocalRing.ResidueField.mapEquiv E x := h2.symm } :
        ↑(C.left.residueField Q.point) →ₗ[k] IsLocalRing.ResidueField ↥(Q.valuationSubring))
      ⟨fun x y h => RingEquiv.injective _ h, fun y => RingEquiv.surjective _ y⟩
  -- ### the residue map on the integral closure
  let hle := kxClosure_le_valuationSubring C h Q hQ.le
  let φ : C.ordClosure h →+* IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    (IsLocalRing.residue ↥(Q.valuationSubring)).comp (Subring.inclusion hle)
  have hφ_smul (c : k) : φ (algebraMap k (C.ordClosure h) c) =
      algebraMap k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) c := by
    have h1 : ((algebraMap k (C.ordClosure h) c : C.ordClosure h) : C.functionField) =
        algebraMap k C.functionField c := rfl
    have h2 : Subring.inclusion hle (algebraMap k (C.ordClosure h) c) =
        (⟨algebraMap k C.functionField c,
          Curve.Place.algebraMap_mem_valuationSubring C Q c⟩ : ↥(Q.valuationSubring)) :=
      Subtype.ext (by rw [Subring.coe_inclusion]; exact h1)
    show IsLocalRing.residue ↥(Q.valuationSubring)
        (Subring.inclusion hle (algebraMap k (C.ordClosure h) c)) = _
    rw [h2, IsScalarTower.algebraMap_apply k ↥(Q.valuationSubring)
        (IsLocalRing.ResidueField ↥(Q.valuationSubring)),
      IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  have hker : RingHom.ker φ = kxPrimeOfPlace C h Q hQ.le := by
    show RingHom.ker ((IsLocalRing.residue ↥(Q.valuationSubring)).comp
      (Subring.inclusion hle)) = _
    rw [← RingHom.comap_ker (IsLocalRing.residue ↥(Q.valuationSubring))
      (Subring.inclusion hle), IsLocalRing.ker_residue]
    rfl
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, hb⟩ := kxClosure_residue_surjective C h hh Q hQ y
    refine ⟨b, ?_⟩
    show IsLocalRing.residue ↥(Q.valuationSubring) (Subring.inclusion hle b) = y
    rw [show Subring.inclusion hle b =
        (⟨(b : C.functionField), hle b.2⟩ : ↥(Q.valuationSubring)) from
      Subtype.ext (by rw [Subring.coe_inclusion])]
    exact hb
  let hφalg : C.ordClosure h →ₐ[k] IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    { φ with commutes' := hφ_smul }
  have hφalg_apply (a : C.ordClosure h) : hφalg a = φ a := rfl
  have hker' (a : C.ordClosure h) :
      φ a = 0 ↔ a ∈ kxPrimeOfPlace C h Q hQ.le := by
    rw [← RingHom.mem_ker, hker]
  let Φ : (C.ordClosure h ⧸ kxPrimeOfPlace C h Q hQ.le) →ₐ[k]
      IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    Ideal.Quotient.liftₐ _ hφalg
      (fun a ha => (hφalg_apply a).trans ((hker' a).mpr ha))
  have hΦmk (b : C.ordClosure h) : Φ (Ideal.Quotient.mk _ b) = φ b :=
    (AlgHom.congr_fun
      (Ideal.Quotient.liftₐ_comp (kxPrimeOfPlace C h Q hQ.le) hφalg
        (fun a ha => (hφalg_apply a).trans ((hker' a).mpr ha))) b).trans (hφalg_apply b)
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨b, hb⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ b, by rw [hΦmk]; exact hb⟩
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hΦmk a, hΦmk b] at hxy
    have h1 : φ (a - b) = 0 := by rw [RingHom.map_sub φ a b, hxy, sub_self]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := kxPrimeOfPlace C h Q hQ.le) a b).mpr
      ((hker' (a - b)).mp h1)
  have hfin1 : Module.finrank k (C.ordClosure h ⧸ kxPrimeOfPlace C h Q hQ.le) =
      Module.finrank k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) :=
    (AlgEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).toLinearEquiv.finrank_eq
  calc Module.finrank k (C.ordClosure h ⧸ kxPrimeOfPlace C h Q hQ.le)
      = Module.finrank k (IsLocalRing.ResidueField ↥(Q.valuationSubring)) := hfin1
    _ = Module.finrank k ↑(C.left.residueField Q.point) := eRF.finrank_eq.symm
    _ = C.hom.residueDegree Q.point := (Place.degree_eq_finrank Q).symm

end

end Work.CurveBasics.Order
