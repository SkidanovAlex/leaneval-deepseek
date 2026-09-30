import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

/-- Localization at a submonoid `M` induces an order isomorphism between the interval of primes
`P ≤ J ≤ Q` in the localization `S` and the interval of primes `P.under R ≤ J ≤ Q.under R` in
`R`.  The forward map is `J ↦ J.under R`; the inverse is `J ↦ J.map (algebraMap R S)`. -/
private def localizationIccOrderIso {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {P Q : Ideal S} [P.IsPrime] [Q.IsPrime] (_h : P ≤ Q) :
    {J : Ideal S // J.IsPrime ∧ P ≤ J ∧ J ≤ Q} ≃o
      {J : Ideal R // J.IsPrime ∧ P.under R ≤ J ∧ J ≤ Q.under R} where
  toFun := fun J => ⟨J.1.under R,
      ⟨((IsLocalization.isPrime_iff_isPrime_disjoint M S J.1).1 J.2.1).1,
       Ideal.comap_mono J.2.2.1, Ideal.comap_mono J.2.2.2⟩⟩
  invFun := fun J => ⟨J.1.map (algebraMap R S),
      ⟨IsLocalization.isPrime_of_isPrime_disjoint M S J.1 J.2.1
        ((((IsLocalization.isPrime_iff_isPrime_disjoint M S Q).1 ‹Q.IsPrime›).2).mono_right J.2.2.2),
       (IsLocalization.map_under M S P).symm.trans_le (Ideal.map_mono J.2.2.1),
       (Ideal.map_mono J.2.2.2).trans_eq (IsLocalization.map_under M S Q)⟩⟩
  left_inv := fun J => Subtype.ext (IsLocalization.map_under M S J.1)
  right_inv := fun J => Subtype.ext
    (IsLocalization.under_map_of_isPrime_disjoint M S J.2.1
      ((((IsLocalization.isPrime_iff_isPrime_disjoint M S Q).1 ‹Q.IsPrime›).2).mono_right J.2.2.2))
  map_rel_iff' := by
    intro a b
    exact IsLocalization.under_le_under_iff M S

/-- Localization preserves relative heights up to order-isomorphism of the corresponding
intervals of prime ideals: if `S` is the localization of `R` at a submonoid `M` and `P ≤ Q` are
primes of `S`, then the poset of primes between `P` and `Q` in `S` has the same Krull dimension
as the poset of primes between `P.under R` and `Q.under R` in `R`. -/
theorem krullDim_Icc_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {P Q : Ideal S} [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    Order.krullDim {J : Ideal S // J.IsPrime ∧ P ≤ J ∧ J ≤ Q}
      = Order.krullDim {J : Ideal R // J.IsPrime ∧ P.under R ≤ J ∧ J ≤ Q.under R} :=
  Order.krullDim_eq_of_orderIso (localizationIccOrderIso M h)

end Work.BW.RB
