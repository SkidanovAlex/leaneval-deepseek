import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.HALG

/-- Cardinality multiplicativity for a short exact sequence of abelian groups.
Write `Submission/Work/Pi6/HALG/card_eq_mul_card_of_shortExact.lean`, module
`Submission.Work.Pi6.HALG.card_eq_mul_card_of_shortExact`, namespace `Work.Pi6.HALG`.
Hints: `AddSubgroup.card_eq_card_quotient_mul_card_subgroup` (or
`Subgroup.card_eq_card_quotient_mul_card_subgroup`, Mathlib `GroupTheory/Coset/Card.lean`) applied
to `ker g : AddSubgroup B`, together with `Nat.card_congr` along `A ≃ ker g` (`Function.Exact`
gives `range f = ker g`) and `C ≃ B ⧸ ker g` (from surjectivity of `g`). -/
theorem card_eq_mul_card_of_shortExact {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hA : Finite A) (hC : Finite C) :
    Nat.card B = Nat.card A * Nat.card C := by
  have hker : f.range = g.ker := (AddMonoidHom.exact_iff.mp hex).symm
  have hquot : Nat.card (B ⧸ g.ker) = Nat.card C :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv
  have hsub : Nat.card g.ker = Nat.card A := by
    rw [← hker]
    refine (Nat.card_congr (AddEquiv.ofBijective f.rangeRestrict ?_).toEquiv).symm
    exact ⟨fun a b h => hf (Subtype.ext_iff.mp h), AddMonoidHom.rangeRestrict_surjective f⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, hquot, hsub]
  exact Nat.mul_comm _ _

end Work.Pi6.HALG
