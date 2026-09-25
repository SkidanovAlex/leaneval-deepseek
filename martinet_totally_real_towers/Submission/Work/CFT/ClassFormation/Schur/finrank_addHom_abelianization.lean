import Mathlib

namespace Work.CFT.ClassFormation.Schur

open Additive Multiplicative

/-- Additive homomorphisms from `Additive G` into `ZMod p` are the same as additive
homomorphisms out of the abelianization of `G`: precomposition with the quotient map
`Abelianization.of` is a bijection, because `ZMod p` is commutative, so every such
homomorphism vanishes on commutators. -/
noncomputable def addHomAbelianizationAddEquiv (p : ℕ) (G : Type) [Group G] :
    (Additive G →+ ZMod p) ≃+ (Additive (Abelianization G) →+ ZMod p) where
  toEquiv := AddMonoidHom.toMultiplicativeRight.trans
    (Abelianization.lift.trans MonoidHom.toAdditiveLeft)
  map_add' f g := by
    show MonoidHom.toAdditiveLeft
        (Abelianization.lift (AddMonoidHom.toMultiplicativeRight (f + g))) =
      MonoidHom.toAdditiveLeft
          (Abelianization.lift (AddMonoidHom.toMultiplicativeRight f)) +
        MonoidHom.toAdditiveLeft
          (Abelianization.lift (AddMonoidHom.toMultiplicativeRight g))
    rw [show AddMonoidHom.toMultiplicativeRight (f + g) =
        AddMonoidHom.toMultiplicativeRight f * AddMonoidHom.toMultiplicativeRight g from rfl]
    rw [show Abelianization.lift
          (AddMonoidHom.toMultiplicativeRight f * AddMonoidHom.toMultiplicativeRight g) =
        Abelianization.lift (AddMonoidHom.toMultiplicativeRight f) *
          Abelianization.lift (AddMonoidHom.toMultiplicativeRight g) from
      MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl]
    rfl

/-- The rank over `ZMod p` of the group of additive homomorphisms `Additive G → ZMod p` agrees
with the rank of the additive homomorphisms out of the abelianization of `G`. -/
theorem finrank_addHom_abelianization (p : ℕ) (G : Type) [Group G] :
    Module.finrank (ZMod p) (Additive G →+ ZMod p) =
      Module.finrank (ZMod p) (Additive (Abelianization G) →+ ZMod p) := by
  exact ((addHomAbelianizationAddEquiv p G).toLinearEquiv (by
    intro c x
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective c
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact map_zsmul _ z x)).finrank_eq

end Work.CFT.ClassFormation.Schur
