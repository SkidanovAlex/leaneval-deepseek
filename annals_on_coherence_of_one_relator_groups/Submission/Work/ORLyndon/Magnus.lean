import Mathlib
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.Lyndon

/-!
# The two-term form of Lyndon's identity theorem (JL Claim 5.10)

This file records, in the vocabulary of `Work.ORLyndon`, the *two-term form* of Lyndon's identity
theorem used by Jaikin-Zapirain–Linton (Claim 5.10 of *On the coherence of one-relator groups and
their group algebras*): in a one-relator group `G = ⟨X | r⟩` with `r = u ^ l`, a Magnus subgroup
`A ≤ G` and the Fox decomposition `u - 1 = α + (t - 1) β` of the relator with respect to the free
product decomposition of `F(X)`, the relation module of the presentation sits in an exact sequence

`0 → K[G]/K[G](u - 1) → I^G_{K[A]} ⊕ K[G] → I_{K[G]} → 0`

whose first map has second component `a ↦ a (1 + u + ⋯ + u^{l-1}) β` (the mirror in left modules of
JL's `a ↦ β (1 + u + ⋯ + u^{l-1}) a`, which is written there for right modules).

The mathematical content (the exactness of this sequence) is *not* proved here: it is the interface
with the one-relator combinatorics (Magnus/Mayer–Vietoris input).  It is packaged as the proposition
`Work.ORLyndon.MagnusTwoTermExact`, which downstream nodes may take as an explicit hypothesis, in
the same way as `Work.ORLyndon.LyndonIdentity`.

What *is* proved here is the well-definedness of the second component: the map
`a ↦ a (1 + u + ⋯ + u^{l-1}) β` kills `(u - 1)` on the right, hence factors through the relation
module `K[G]/K[G](u - 1)`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {K : Type v} {G : Type u}

/-- The norm element `1 + u + ⋯ + u^{l-1}` of `u` in `K[G]`. -/
noncomputable def normElem (K : Type v) [Ring K] {G : Type u} [Monoid G] (l : ℕ) (u : G) :
    MonoidAlgebra K G :=
  ∑ i ∈ Finset.range l, ((MonoidAlgebra.of K G) u) ^ i

@[simp] theorem normElem_one [Ring K] {G : Type u} [Monoid G] (u : G) :
    normElem (K := K) 1 u = 1 := by
  rw [normElem, Finset.sum_range_one, pow_zero]

/-- The second component `a ↦ a (1 + u + ⋯ + u^{l-1}) β` of the first map of the two-term form, as
a left `K[G]`-linear endomorphism of `K[G]` (right multiplication by `(1 + u + ⋯ + u^{l-1}) β`). -/
noncomputable def magnusSecond (K : Type v) [Ring K] {G : Type u} [Monoid G]
    (l : ℕ) (u : G) (β : MonoidAlgebra K G) :
    MonoidAlgebra K G →ₗ[MonoidAlgebra K G] MonoidAlgebra K G :=
  LinearMap.mulRight (MonoidAlgebra K G) (normElem (K := K) l u * β)

theorem magnusSecond_apply [Ring K] [Monoid G] (l : ℕ) (u : G)
    (β a : MonoidAlgebra K G) :
    magnusSecond K l u β a = a * (normElem (K := K) l u * β) := by
  simp [magnusSecond, mul_assoc]

/-- The second component of the two-term form kills `(u - 1)`: for `u ^ l = 1` we have
`(u - 1) (1 + ⋯ + u^{l-1}) = u^l - 1 = 0`, hence `a ↦ a (1 + ⋯ + u^{l-1}) β` factors through
`K[G]/K[G](u - 1)`. -/
theorem magnusSecond_factors [Ring K] [Monoid G] {l : ℕ} {u : G} (hul : u ^ l = 1)
    (β a : MonoidAlgebra K G) :
    magnusSecond K l u β (a * ((MonoidAlgebra.of K G) u - 1)) = 0 := by
  rw [magnusSecond_apply, mul_assoc]
  have h : ((MonoidAlgebra.of K G) u - 1) * normElem (K := K) l u = 0 := by
    rw [normElem, mul_geom_sum, ← map_pow, hul, map_one, sub_self]
  rw [← mul_assoc ((MonoidAlgebra.of K G) u - 1) (normElem (K := K) l u) β, h, zero_mul,
    mul_zero]

/-- **JL Claim 5.10** (two-term form of Lyndon's identity theorem): the data of an exact sequence
of left `K[G]`-modules

`0 → K[G]/K[G](u - 1) → I^G_{K[A]} ⊕ K[G] → I_{K[G]} → 0`

whose first map has second component `a ↦ a (1 + u + ⋯ + u^{l-1}) β` (`magnusSecond K l u β`).

The field `γ` is the first map, `π` the second; `γ_injective`, `π_surjective` and `ker_eq_range`
are the exactness statements.  For the one-relator presentation `⟨X | r⟩` with `r = u ^ l`, `A` a
Magnus subgroup and `β = ∂u/∂t` (the Fox derivative with respect to the outside generator), this
data is *constructed* in `Work.ORLyndon.magnusTwoTerm_of_lyndon`
(`Submission/Work/ORLyndon/magnusTwoTerm_of_lyndon.lean`) from Lyndon's identity theorem and the
Freiheitssatz. -/
structure MagnusTwoTermExact (K : Type v) [Field K] {G : Type u} [Group G] (A : Subgroup G)
    (u : G) (l : ℕ) (β : MonoidAlgebra K G) where
  /-- the first map `K[G]/K[G](u - 1) → I^G_{K[A]} ⊕ K[G]` of the two-term sequence -/
  γ : (MonoidAlgebra K G ⧸ Ideal.span {((MonoidAlgebra.of K G) u) - 1}) →ₗ[MonoidAlgebra K G]
        (↥(augIdealIn K A) × MonoidAlgebra K G)
  /-- the second map `I^G_{K[A]} ⊕ K[G] → I_{K[G]}` of the two-term sequence -/
  π : (↥(augIdealIn K A) × MonoidAlgebra K G) →ₗ[MonoidAlgebra K G] ↥(augIdeal K G)
  /-- the second component of the first map is `a ↦ a (1 + ⋯ + u^{l-1}) β` -/
  γ_snd : ∀ a : MonoidAlgebra K G, (γ (Submodule.Quotient.mk a)).2 = magnusSecond K l u β a
  /-- the first map is injective -/
  γ_injective : Function.Injective γ
  /-- the second map is surjective -/
  π_surjective : Function.Surjective π
  /-- exactness in the middle: `ker π = range γ` -/
  ker_eq_range : LinearMap.ker π = LinearMap.range γ

end Work.ORLyndon
