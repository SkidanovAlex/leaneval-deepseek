import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The absolute norm of an ideal is invariant under ring isomorphisms of Dedekind domains
(both infinite, so that the absolute norm is the cardinality of the quotient). -/
theorem absNorm_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Infinite R] [Infinite S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map (e : R →+* S)) = Ideal.absNorm I := by
  -- `Ideal.absNorm` is by definition the cardinality of the quotient ring,
  -- `Ideal.absNorm_apply` : `absNorm I = Submodule.cardQuot I`
  -- `Submodule.cardQuot_apply` : `cardQuot I = Nat.card (R ⧸ I)`
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  -- The ring equivalence `e` induces `R ⧸ I ≃+* S ⧸ I.map e`.
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map (e : R →+* S)) e rfl).toEquiv.symm

end Work.BW
