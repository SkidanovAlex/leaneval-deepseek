import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every finite `G`-operator group is an equivariant quotient of a free group

If `G` is a group acting on a finite group `P` by group automorphisms
(`MulDistribMulAction G P`), then `P` is a `G`-equivariant quotient of a free group
`F_n = FreeGroup (Fin n)` on finitely many generators, where `G` acts on `F_n` by permuting
the generators:

* take `n = #P` and any bijection `e : P ≃ Fin n`;
* the action `σ` of `G` on the generators `Fin n` is the transport of the given action of `G`
  on `P` along `e` (`σ g = e ∘ (g • ·) ∘ e⁻¹`), which extends to the automorphism
  `FreeGroup.freeGroupCongr (σ g)` of `FreeGroup (Fin n)`;
* the surjection `φ = FreeGroup.lift e.symm` sends the generator `i` to `e.symm i ∈ P` and is
  `G`-equivariant by construction.

This is the elementary "generators/relations" input used to reduce embedding problems for finite
`G`-operator groups to embedding problems with free kernel.
-/

namespace Work.GenericKernelReduction

/-- `FreeGroup.freeGroupCongr` is multiplicative: mapping the free group along `p * q` is the
composite of mapping along `p` and along `q`.  (Note the multiplication convention: for
permutations `(p * q) x = p (q x)`, and `MulAut.freeGroupCongr p * FreeGroup.freeGroupCongr q`
acts as `FreeGroup.freeGroupCongr p ∘ FreeGroup.freeGroupCongr q`.) -/
lemma freeGroupCongr_mul {α : Type*} (p q : Equiv.Perm α) :
    FreeGroup.freeGroupCongr (p * q) = FreeGroup.freeGroupCongr p * FreeGroup.freeGroupCongr q := by
  have h : (p * q : Equiv.Perm α) = q.trans p := by ext x; rfl
  rw [h, ← FreeGroup.freeGroupCongr_trans]
  ext x
  rfl

/-- The permutation group of a type acts on the free group on that type by permuting the
generators; concretely `p • x = FreeGroup.map p x`.  This is `FreeGroup.freeGroupCongr` packaged
as a monoid homomorphism. -/
noncomputable def permFreeGroupHom (α : Type*) : Equiv.Perm α →* MulAut (FreeGroup α) where
  toFun p := FreeGroup.freeGroupCongr p
  map_one' := FreeGroup.freeGroupCongr_refl
  map_mul' p q := freeGroupCongr_mul p q

set_option linter.style.haveILetI false in
/-- **Every finite `G`-operator group is an equivariant quotient of a free group.**

For a finite group `P` with an action of a group `G` by group automorphisms, there is a finite
generating set `Fin n` such that the free group `FreeGroup (Fin n)`, with the induced action `ρ`
of `G` on it, admits a surjective `G`-equivariant homomorphism onto `P`. -/
theorem exists_equivariant_surjection_freeGroup {G : Type*} [Group G] [Finite G] {P : Type*}
    [Group P] [Finite P] [MulDistribMulAction G P] :
    ∃ (n : ℕ) (ρ : G →* MulAut (FreeGroup (Fin n))) (φ : FreeGroup (Fin n) →* P),
      Function.Surjective φ ∧
      ∀ (g : G) (x : FreeGroup (Fin n)),
        φ (ρ g x) = (MulDistribMulAction.toMulAut G P g) (φ x) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  -- generate `P` by the whole of `P`, indexed by `Fin n` via a bijection `e`.
  let n := Fintype.card P
  let e : P ≃ Fin n := Fintype.equivFin P
  -- the induced action of `G` on the generators `Fin n`: `σ g = e ∘ (g • ·) ∘ e⁻¹`.
  let σ : G →* Equiv.Perm (Fin n) :=
    { toFun := fun g => (e.symm.trans (MulDistribMulAction.toMulAut G P g)).trans e
      map_one' := by ext i; simp
      map_mul' := by
        intro g h; ext i
        simp [Equiv.Perm.mul_apply, Equiv.trans_apply, MulAut.mul_apply, map_mul] }
  let ρ : G →* MulAut (FreeGroup (Fin n)) := (permFreeGroupHom (Fin n)).comp σ
  refine ⟨n, ρ, FreeGroup.lift (⇑e.symm), ?_, ?_⟩
  · -- surjectivity: the generator labelled by `e p` maps to `p`.
    intro p
    exact ⟨FreeGroup.of (e p), by simp [FreeGroup.lift_apply_of]⟩
  · -- equivariance, checked on generators and extended by freeness.
    intro g x
    have hgen : ∀ i : Fin n,
        (FreeGroup.lift (⇑e.symm)) (ρ g (FreeGroup.of i)) =
          (MulDistribMulAction.toMulAut G P g) ((FreeGroup.lift (⇑e.symm)) (FreeGroup.of i)) := by
      intro i
      have hσ : σ g i = e ((MulDistribMulAction.toMulAut G P g) (e.symm i)) := rfl
      have hρ : ρ g (FreeGroup.of i) = FreeGroup.of (σ g i) := by
        show FreeGroup.freeGroupCongr (σ g) (FreeGroup.of i) = FreeGroup.of (σ g i)
        rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
      rw [hρ, FreeGroup.lift_apply_of, hσ]
      simp
    have key : (FreeGroup.lift (⇑e.symm)).comp (ρ g) =
        ((MulDistribMulAction.toMulAut G P g).toMonoidHom).comp (FreeGroup.lift (⇑e.symm)) := by
      apply FreeGroup.ext_hom
      intro i
      simpa using hgen i
    simpa using DFunLike.congr_fun key x

end Work.GenericKernelReduction
