import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.H0Map_bijective
import Submission.Work.Tate.Hm1Map_bijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.Tate

variable {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B] [Fintype G]

/-- An isomorphism of `G`-modules (an equivariant additive bijection) induces an isomorphism
`Ĥ⁰(G, A) ≃+ Ĥ⁰(G, B)`. -/
noncomputable def H0Equiv (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (hfb : Function.Bijective f) : H0 G A ≃+ H0 G B :=
  AddEquiv.ofBijective (H0Map G A B f hf) (H0Map_bijective f hf hfb)

/-- An isomorphism of `G`-modules induces an isomorphism `Ĥ⁻¹(G, A) ≃+ Ĥ⁻¹(G, B)`. -/
noncomputable def Hm1Equiv (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (hfb : Function.Bijective f) : Hm1 G A ≃+ Hm1 G B :=
  AddEquiv.ofBijective (Hm1Map G A B f hf) (Hm1Map_bijective f hf hfb)

@[simp] theorem H0Equiv_apply (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (hfb : Function.Bijective f) (x : H0 G A) :
    H0Equiv f hf hfb x = H0Map G A B f hf x := rfl

@[simp] theorem Hm1Equiv_apply (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (hfb : Function.Bijective f) (x : Hm1 G A) :
    Hm1Equiv f hf hfb x = Hm1Map G A B f hf x := rfl

end Work.Tate
