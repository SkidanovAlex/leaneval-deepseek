import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- Ramification index is invariant under an isomorphism of `R`-algebras.

This is the `AlgEquiv` version of `Ideal.ramificationIdx_smul`: it compares the
ramification index of `q` with that of its image under an `R`-algebra isomorphism. -/
theorem ramificationIdx_map_algEquiv {A B : Type*} [CommRing A] [CommRing B]
    {R : Type*} [CommRing R] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) (q : Ideal A) [q.IsPrime] :
    (q.map (f : A →+* B)).ramificationIdx R = q.ramificationIdx R := by
  have hq' : (q.map (f : A →+* B)).IsPrime := Ideal.map_isPrime_of_equiv f
  let p := q.under R
  have hL : (q.map (f : A →+* B)).LiesOver p := Ideal.map_equiv_liesOver q p f
  let Sq := Localization.AtPrime q
  let Sq' := Localization.AtPrime (q.map (f : A →+* B))
  have hIJ : q = (q.map (f : A →+* B)).comap (f : A →+* B) :=
    (Ideal.comap_map_of_bijective (f : A →+* B) f.bijective).symm
  let f' : Sq ≃ₐ[R] Sq' := Localization.localAlgEquiv q (q.map (f : A →+* B)) f hIJ
  letI : Algebra Sq Sq' := f'.toRingHom.toAlgebra
  have hST : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f'.toAlgHom
  let g : Sq ≃ₐ[Sq] Sq' := { f' with commutes' := fun _ => rfl }
  have hgg : (g : Sq →+* Sq') = algebraMap Sq Sq' := rfl
  let e : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
    Ideal.quotientEquivAlg _ _ g
      (by rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map, hgg])
  rw [Ideal.ramificationIdx_eq p q, Ideal.ramificationIdx_eq p (q.map (f : A →+* B)),
    e.toLinearEquiv.length_eq, Module.length_eq_of_surjective f'.surjective]

/-- Inertia degree is invariant under an isomorphism of `R`-algebras.

This is the `AlgEquiv` version of `Ideal.inertiaDeg_smul`. -/
theorem inertiaDeg_map_algEquiv {A B : Type*} [CommRing A] [CommRing B]
    {R : Type*} [CommRing R] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) (q : Ideal A) [q.IsPrime] :
    (q.map (f : A →+* B)).inertiaDeg R = q.inertiaDeg R := by
  have hq' : (q.map (f : A →+* B)).IsPrime := Ideal.map_isPrime_of_equiv f
  let p := q.under R
  have hp : p.IsPrime := inferInstance
  have hL : (q.map (f : A →+* B)).LiesOver p := Ideal.map_equiv_liesOver q p f
  letI := Localization.AtPrime.algebraOfLiesOver p q
  letI := Localization.AtPrime.algebraOfLiesOver p (q.map (f : A →+* B))
  rw [Ideal.inertiaDeg_eq p (q.map (f : A →+* B)), Ideal.inertiaDeg_eq p q]
  let e₂ := Ideal.residueFieldAlgEquiv' p (q.map (f : A →+* B)) q f.symm
    (Ideal.comap_symm f.toRingEquiv).symm
  exact e₂.toLinearEquiv.finrank_eq

theorem ramificationIdx_inertiaDeg_map_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (q : Ideal A) [q.IsPrime] {R : Type*} [CommRing R] [Algebra R A] [Algebra R B]
    (h : ∀ r : R, e (algebraMap R A r) = algebraMap R B r) :
    (q.map (e : A →+* B)).ramificationIdx R = q.ramificationIdx R ∧
      (q.map (e : A →+* B)).inertiaDeg R = q.inertiaDeg R := by
  let e' : A ≃ₐ[R] B := { e with commutes' := h }
  have hcoe : (e' : A →+* B) = (e : A →+* B) := rfl
  refine ⟨?_, ?_⟩
  · rw [← hcoe]
    exact ramificationIdx_map_algEquiv e' q
  · rw [← hcoe]
    exact inertiaDeg_map_algEquiv e' q

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
