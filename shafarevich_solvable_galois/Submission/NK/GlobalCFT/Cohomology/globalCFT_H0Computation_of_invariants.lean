import Mathlib
import Submission.NK.GlobalCFT.Cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Cohomology

/-- **A group-theoretic form of the `H⁰`-computation.**

Let `ψ : G ≃* Multiplicative M` be a multiplicative isomorphism from a group `G` onto the
elements of an additive commutative group `M` (written multiplicatively), let `p ≤ M` be an
additive subgroup and `N ≤ G` a (normal) subgroup such that `ψ` carries `N` onto `p`, i.e.
`ψ q ∈ p ↔ q ∈ N` for all `q`.  Then `ψ` descends to an isomorphism
`G ⧸ N ≃* Multiplicative (M ⧸ p)`.

This is the abstract content of the `H⁰`-computation: take `G = C_K`, `M = (C_L)^{Gal(L/K)}`,
`p` the image of the norm map and `N = N_{L/K} C_L`. -/
noncomputable def quotientMulEquivOfInvariants {G : Type*} [Group G] {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] (p : Submodule R M) (N : Subgroup G) [N.Normal]
    (ψ : G ≃* Multiplicative M)
    (hnorm : ∀ q : G, (ψ q : M) ∈ p ↔ q ∈ N) :
    G ⧸ N ≃* Multiplicative (M ⧸ p) := by
  -- the quotient map `M → M ⧸ p`, transported to the multiplicative groups
  let g : Multiplicative M →* Multiplicative (M ⧸ p) :=
    AddMonoidHom.toMultiplicative (Submodule.mkQ p).toAddMonoidHom
  let f : G →* Multiplicative (M ⧸ p) := g.comp ψ.toMonoidHom
  have hf : ∀ q : G, f q = Multiplicative.ofAdd (Submodule.Quotient.mk (p := p) (ψ q : M)) := by
    intro q
    rw [MonoidHom.comp_apply]
    rfl
  -- the kernel of `f` is exactly `N`
  have key : ∀ q : G, f q = 1 ↔ q ∈ N := by
    intro q
    rw [hf q]
    constructor
    · intro h
      exact (hnorm q).mp ((Submodule.Quotient.mk_eq_zero p).mp h)
    · intro h
      exact (Submodule.Quotient.mk_eq_zero p).mpr ((hnorm q).mpr h)
  have hker : f.ker = N := by
    ext q
    rw [MonoidHom.mem_ker]
    exact key q
  have HN : N ≤ f.ker := le_of_eq hker.symm
  refine MulEquiv.ofBijective (QuotientGroup.lift N f HN) ⟨?_, ?_⟩
  · rintro a b hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective N b
    have h1 : (QuotientGroup.lift N f HN) (QuotientGroup.mk' N a') = f a' := rfl
    have h2 : (QuotientGroup.lift N f HN) (QuotientGroup.mk' N b') = f b' := rfl
    rw [h1, h2] at hab
    show QuotientGroup.mk' N a' = QuotientGroup.mk' N b'
    refine QuotientGroup.eq.mpr ?_
    refine (key (a'⁻¹ * b')).mp ?_
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  · intro y
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective p (Multiplicative.toAdd y)
    obtain ⟨q, hq⟩ := ψ.surjective (Multiplicative.ofAdd x)
    refine ⟨QuotientGroup.mk' N q, ?_⟩
    have h1 : (QuotientGroup.lift N f HN) (QuotientGroup.mk' N q) = f q := rfl
    rw [h1, hf q, hq]
    show Multiplicative.ofAdd (Submodule.Quotient.mk (p := p) x) = y
    exact hx

theorem globalCFT_H0Computation_of_invariants {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (ψ : C[K] ≃* Multiplicative ↥((IdeleClassGroup.rep K L).ρ.invariants))
    (hnorm : ∀ q : C[K], ψ q ∈ Submodule.comap ((IdeleClassGroup.rep K L).ρ.invariants).subtype
        (LinearMap.range (IdeleClassGroup.rep K L).ρ.norm) ↔
      q ∈ Idele.normClassSubgroup K L) :
    H0Computation K L := by
  refine ⟨⟨quotientMulEquivOfInvariants
    (Submodule.comap ((IdeleClassGroup.rep K L).ρ.invariants).subtype
      (LinearMap.range (IdeleClassGroup.rep K L).ρ.norm))
    (Idele.normClassSubgroup K L) ψ ?_⟩⟩
  exact hnorm

end NK.GlobalCFT.Cohomology
