import Mathlib

/-!
# Functoriality of `ClassGroup.mulEquiv`

If `e : R ≃+* S` and `e' : S ≃+* T` are isomorphisms of (commutative, domain) rings, then
the induced isomorphisms of ideal class groups compose:
`ClassGroup.mulEquiv (e.trans e') = (ClassGroup.mulEquiv e).trans (ClassGroup.mulEquiv e')`.

This is the functoriality of `ClassGroup.mulEquiv` with respect to composition of ring
isomorphisms.  It is proved by chasing the definition of `ClassGroup.mulEquiv`, which is built
out of `ClassGroup.equiv`, `QuotientGroup.congr` and the fractional-ideal transport
`FractionalIdeal.ringEquivOfRingEquiv`, together with the composition lemmas for the last two.
-/

namespace Work.CFTLib

open NumberField
open scoped nonZeroDivisors

/-- Composition of `Units.mapEquiv`: a multiplicative equivalence of monoids defines a
multiplicative equivalence of their groups of units, and this construction is functorial. -/
lemma unitsMapEquiv_trans {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (e : M ≃* N) (e' : N ≃* P) :
    Units.mapEquiv (e.trans e') = (Units.mapEquiv e).trans (Units.mapEquiv e') :=
  MulEquiv.ext fun _ => Units.ext rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem classGroupMulEquiv_trans {R S T : Type} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [CommRing T] [IsDomain T] (e : R ≃+* S) (e' : S ≃+* T) :
    ClassGroup.mulEquiv (e.trans e') =
      (ClassGroup.mulEquiv e).trans (ClassGroup.mulEquiv e') := by
  refine MulEquiv.ext fun a => ?_
  rw [MulEquiv.trans_apply]
  simp only [ClassGroup.mulEquiv_apply, MulEquiv.apply_symm_apply]
  congr 1
  -- The group equivalence defining `ClassGroup.mulEquiv (e.trans e')` is the composite of the
  -- group equivalences defining `ClassGroup.mulEquiv e` and `ClassGroup.mulEquiv e'`.
  have hmap :
      Units.mapEquiv (↑(FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing T)
        (e.trans e')) : FractionalIdeal R⁰ (FractionRing R) ≃* FractionalIdeal T⁰ (FractionRing T)) =
      (Units.mapEquiv (↑(FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing S) e) :
          FractionalIdeal R⁰ (FractionRing R) ≃* FractionalIdeal S⁰ (FractionRing S))).trans
        (Units.mapEquiv (↑(FractionalIdeal.ringEquivOfRingEquiv (FractionRing S) (FractionRing T) e') :
          FractionalIdeal S⁰ (FractionRing S) ≃* FractionalIdeal T⁰ (FractionRing T))) := by
    rw [← unitsMapEquiv_trans]
    congr 1
    rw [FractionalIdeal.ringEquivOfRingEquiv_trans (K := FractionRing R) (L := FractionRing S)
        (M := FractionRing T) e e', RingEquiv.coe_mulEquiv_trans]
  -- Reduce to the classes of fractional ideals.
  generalize hq : (ClassGroup.equiv (FractionRing R)) a = q
  clear hq
  induction q using QuotientGroup.induction_on with
  | _ y =>
    simp only [QuotientGroup.congr_apply, QuotientGroup.congr_mk']
    rw [← MulEquiv.trans_apply, ← hmap]

end Work.CFTLib
