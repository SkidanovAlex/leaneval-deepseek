import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

/-- The additive homomorphism `ℕ →+ M` sending `n` to `n • m`. -/
private def smulNatHom {M : Type*} [AddCommMonoid M] (m : M) : ℕ →+ M where
  toFun n := n • m
  map_zero' := zero_smul ℕ m
  map_add' x y := add_nsmul m x y

/-- The weight of the pushforward of an exponent vector along a map is the weight of the
exponent vector with respect to the pulled-back weight function. -/
lemma weight_mapDomain {σ τ M : Type*} [AddCommMonoid M]
    (w : τ → M) (f : σ → τ) (d : σ →₀ ℕ) :
    Finsupp.weight w (d.mapDomain f) = Finsupp.weight (w ∘ f) d := by
  have key := Finsupp.sum_mapDomain_index_addMonoidHom (f := f) (s := d)
    (fun b : τ => smulNatHom (w b))
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  exact key

theorem isWeightedHomogeneous_rename {σ τ M R : Type*} [CommSemiring R] [AddCommMonoid M]
    (w : τ → M) (f : σ → τ) (hf : Function.Injective f) {d : M} {p : MvPolynomial σ R}
    (hp : p.IsWeightedHomogeneous (w ∘ f) d) :
    (p.rename f).IsWeightedHomogeneous w d := by
  intro e he
  obtain ⟨u, hu, hu'⟩ := MvPolynomial.coeff_rename_ne_zero f p e he
  rw [← hu, weight_mapDomain w f u]
  exact hp hu'

end Work.RB
