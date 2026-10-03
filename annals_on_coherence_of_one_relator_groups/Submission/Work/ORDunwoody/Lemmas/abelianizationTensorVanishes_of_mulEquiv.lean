import Mathlib
import Submission.Work.ORDunwoody.FP2
import Submission.Work.ORDunwoody.Lemmas.abelianizationTensorVanishes_of_surjective

/-!
# `AbelianizationTensorVanishes` is invariant under group isomorphism

`AbelianizationTensorVanishes k N` is the vanishing of `H₁(N;k) = N^{ab} ⊗_ℤ k`, i.e. the
statement that the `k`-module `N^{ab} ⊗_ℤ k` is a subsingleton.  Being a `Prop` about a
subsingleton, the condition can be transported across an isomorphism of groups: a
multiplicative equivalence `e : G ≃* H` is in particular a surjection `G →* H`, and
`H₁(-;k)` is functorial, so `H₁(G;k) = 0` implies `H₁(H;k) = 0` by
`abelianizationTensorVanishes_of_surjective`.
-/

set_option autoImplicit false

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody

/-- `H₁(-;k)` vanishing is invariant under group isomorphism: if `AbelianizationTensorVanishes k G`
holds and `G ≃* H`, then `AbelianizationTensorVanishes k H` holds. -/
theorem abelianizationTensorVanishes_of_mulEquiv {k : Type*} [CommRing k] {G H : Type*}
    [Group G] [Group H] (h : AbelianizationTensorVanishes k G) (e : G ≃* H) :
    AbelianizationTensorVanishes k H :=
  abelianizationTensorVanishes_of_surjective e.toMonoidHom e.surjective h

end Work.ORDunwoody.Lemmas
