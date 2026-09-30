import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted homogeneity is preserved by `MvPolynomial.killCompl`

If `f : σ → τ` is injective and `p : MvPolynomial τ R` is weighted homogeneous of degree `d`
with respect to a weight `w : τ → M`, then the polynomial `p.killCompl hf : MvPolynomial σ R`
(which only keeps the variables lying in the range of `f`, relabelled along `f`) is weighted
homogeneous of the same degree with respect to the pulled back weight `w ∘ f`.

The key point is the coefficient formula `coeff_killCompl`, together with the fact that
`Finsupp.weight (w ∘ f) s = Finsupp.weight w (s.mapDomain f)`, i.e. that the ambient weighted
degree is compatible with `Finsupp.mapDomain` for an injective `f`.
-/

namespace Work.RB

open MvPolynomial

/-- The weighted degree of a `Finsupp` commutes with `Finsupp.mapDomain` along an injective
map, after pulling the weights back. -/
private theorem weight_comp_mapDomain {σ τ M : Type*} [AddCommMonoid M]
    (w : τ → M) (f : σ → τ) (s : σ →₀ ℕ) :
    Finsupp.weight (w ∘ f) s = Finsupp.weight w (Finsupp.mapDomain f s) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (f := f) (h := fun b m => m • w b) (by intro b; simp)
      (by intro b m1 m2; simp [add_smul])]
  rfl

theorem isWeightedHomogeneous_killCompl {σ τ M R : Type*} [CommSemiring R] [AddCommMonoid M]
    (w : τ → M) {f : σ → τ} (hf : Function.Injective f) {d : M} {p : MvPolynomial τ R}
    (hp : p.IsWeightedHomogeneous w d) :
    (p.killCompl hf).IsWeightedHomogeneous (w ∘ f) d := by
  intro s hs
  rw [coeff_killCompl] at hs
  rw [weight_comp_mapDomain w f s]
  exact hp hs

end Work.RB
