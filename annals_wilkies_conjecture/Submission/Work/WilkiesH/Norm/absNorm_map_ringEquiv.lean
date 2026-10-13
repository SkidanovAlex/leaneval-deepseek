import Mathlib

namespace Work.WilkiesH.Norm

theorem absNorm_map_ringEquiv {R S : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R]
    [CommRing S] [IsDedekindDomain S] [Infinite S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map (e : R →+* S)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map (e : R →+* S)) e rfl).symm.toEquiv

end Work.WilkiesH.Norm
