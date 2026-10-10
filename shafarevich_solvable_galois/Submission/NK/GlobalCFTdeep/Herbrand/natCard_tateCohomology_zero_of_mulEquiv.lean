import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariance of the cardinality of `Ĥ⁰` under a compatible pair of multiplicative equivalences

Let `G`, `H` be finite groups acting multiplicatively on the commutative groups `M`, `N`.
Given a multiplicative equivalence `ψ : M ≃* N` and a group isomorphism `e : G ≃* H` satisfying
the compatibility `ψ (g • m) = e g • ψ m`, the degree-zero Tate cohomology groups agree in
cardinality:

  `Nat.card (Ĥ⁰(G, M)) = Nat.card (Ĥ⁰(H, N))`.

The mathematical content is that `Ĥ⁰(G, M) ≅ M^G ⧸ N_G(M)` depends only on the isomorphism class
of `M` as a `G`-module, and `ψ` is exactly an isomorphism of `G`-modules between `M` (with its
`G`-action) and `N` (with the `G`-action obtained by pulling back the `H`-action along `e`).
The formal proof therefore splits into two steps.

* `natCard_tateCohomology_zero_of_repEquiv`: isomorphic `ℤ`-linear representations have the same
  `Nat.card` in degree `0`, by functoriality of `tateCohomologyFunctor`.
* `natCard_tateCohomology_zero_of_mulEquiv_res` (from `TateZeroTransport`): restricting a
  representation along a group isomorphism does not change `Nat.card` in degree `0`.

Applying the first step to the intertwining equivalence induced by `ψ`, and the second to `e`,
gives the result.
-/

set_option autoImplicit false

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory

/-- A multiplicative equivalence of commutative groups induces an additive equivalence of the
underlying additive groups. -/
def addEquivOfMulEquiv {M N : Type} [CommGroup M] [CommGroup N] (ψ : M ≃* N) :
    Additive M ≃+ Additive N where
  toFun a := Additive.ofMul (ψ a.toMul)
  invFun b := Additive.ofMul (ψ.symm b.toMul)
  left_inv a := by simp
  right_inv b := by simp
  map_add' a b := by simp

@[simp] theorem addEquivOfMulEquiv_apply {M N : Type} [CommGroup M] [CommGroup N]
    (ψ : M ≃* N) (a : Additive M) :
    addEquivOfMulEquiv ψ a = Additive.ofMul (ψ a.toMul) := rfl

/-- An isomorphism of `ℤ`-linear representations of a finite group induces an identification of
the degree-zero Tate cohomology groups, hence of their cardinalities. -/
theorem natCard_tateCohomology_zero_of_repEquiv {G V W : Type} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    {ρ : Representation ℤ G V} {σ : Representation ℤ G W} (f : ρ.Equiv σ) :
    Nat.card (tateCohomology (Rep.of ρ) 0) = Nat.card (tateCohomology (Rep.of σ) 0) :=
  Nat.card_congr (Iso.toLinearEquiv
    ((tateCohomologyFunctor (R := ℤ) (G := G) 0).mapIso (Rep.mkIso f))).toEquiv

/-- **Invariance of `Ĥ⁰` under a compatible pair of multiplicative equivalences.**  If the
action of `H` on `N` is the transport of the action of `G` on `M` along `ψ : M ≃* N` and
`e : G ≃* H`, then `Ĥ⁰(G, M)` and `Ĥ⁰(H, N)` have the same cardinality. -/
theorem natCard_tateCohomology_zero_of_mulEquiv {G H M N : Type} [Group G] [Group H]
    [Fintype G] [Fintype H] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N]
    (e : G ≃* H) (ψ : M ≃* N) (h : ∀ (g : G) (m : M), ψ (g • m) = (e g) • ψ m) :
    Nat.card (tateCohomology (Rep.ofMulDistribMulAction G M) 0) =
      Nat.card (tateCohomology (Rep.ofMulDistribMulAction H N) 0) := by
  -- `ψ` linearised over `ℤ`, as an equivalence of the underlying additive groups
  let fA : Additive M ≃ₗ[ℤ] Additive N := (addEquivOfMulEquiv ψ).toIntLinearEquiv
  -- ... which intertwines the `G`-action on `M` with the pullback along `e` of the action on `N`
  have hf : ∀ g : G, fA ∘ₗ (Representation.ofMulDistribMulAction G M) g =
      ((Representation.ofMulDistribMulAction H N).comp e.toMonoidHom) g ∘ₗ fA := by
    intro g
    ext a
    simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply,
      MonoidHom.comp_apply]
    exact h g a.toMul
  -- `Ĥ⁰` only sees the isomorphism class of the representation
  have hcard := natCard_tateCohomology_zero_of_repEquiv (G := G)
    (ρ := Representation.ofMulDistribMulAction G M)
    (σ := (Representation.ofMulDistribMulAction H N).comp e.toMonoidHom)
    (Representation.Equiv.mk fA hf)
  -- restricting along `e` does not change `Ĥ⁰`
  have hres := NK.GlobalCFTdeep.natCard_tateCohomology_zero_of_mulEquiv_res e
    (Representation.ofMulDistribMulAction H N)
  exact hcard.trans hres

end NK.GlobalCFTdeep.Herbrand
