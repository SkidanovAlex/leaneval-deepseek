import Submission.Work.Hering.Perm.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Wagner's proposition (Peterfalvi I §1, p. 188)

A. Wagner, *On collineation groups of projective spaces I*, Math. Z. 76 (1961) 411:
if `V` is an `F₂`-vector space of dimension `n ≥ 3` and `G ≤ GL(V)` is doubly transitive on
`V \ {0}`, then for every `3`-dimensional subspace `U`, `N_G(U)/C_G(U) ≅ Aut(U)`.

`Work.Hering.Wagner.prop` proves this. For the use in the `Hering` area the multiplicative
formulation (`V` an exponent-`2` abelian group, `G ≤ Aut(V)`) is the convenient one: `Aut(U)`
for a subgroup `U` of order `8` is `GL(3,2)`.
-/

set_option autoImplicit false

namespace Work.Hering

/-- **Wagner's proposition** (Peterfalvi I §1, p. 188), multiplicative form: if `V` is a finite
abelian group of exponent `2`, `Gm ≤ Aut(V)` is doubly transitive on `V \ {1}`, and `U ≤ V` has
order `8`, then every automorphism of `U` is induced by an element of `Gm`. -/
def WagnerProp : Prop :=
  ∀ {V : Type*} [Group V] [Finite V]
    (habel : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x * x = 1)
    (Gm : Subgroup (MulAut V))
    (h2 : ∀ a b c d : V, a ≠ 1 → b ≠ 1 → c ≠ 1 → d ≠ 1 → a ≠ b → c ≠ d →
        ∃ g ∈ Gm, g a = c ∧ g b = d)
    (U : Subgroup V) (hU : Nat.card U = 8)
    (φ : MulAut U),
    ∃ g ∈ Gm, ∀ u : U, g (u : V) = ((φ u : U) : V)

end Work.Hering
