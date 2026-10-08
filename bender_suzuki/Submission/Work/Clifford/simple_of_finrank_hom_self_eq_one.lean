import Mathlib
import Submission.Work.CharCore.fdRep_simple_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# The converse of Schur's lemma for finite dimensional complex representations

If `V` is a finite dimensional complex representation of a finite group `G` and the space of
`G`-equivariant endomorphisms of `V` is one dimensional, then `V` is a simple object of
`FDRep ℂ G` (equivalently, `V.ρ` is irreducible).

The proof is the classical argument: by Maschke's theorem every subrepresentation has a
complement, so for a subrepresentation `S` of `V` we may project onto `S` along a complement;
this projection is `G`-equivariant, hence an endomorphism of `V` in `FDRep ℂ G`.  Since every
such endomorphism is a scalar, a nonzero projection is automatically surjective, which forces
`S = ⊤`.
-/

noncomputable section

open scoped MonoidAlgebra
open CategoryTheory

namespace Work.Clifford

/-- **Converse of Schur's lemma for semisimple modules.**  Let `M` be a module over a ring `R`
which is an algebra over a field `k`, with `M` semisimple over `R`.  If the space of
`R`-linear endomorphisms of `M` is one dimensional over `k`, then `M` is a simple `R`-module.

The proof projects onto an arbitrary submodule `S` along a complement (which exists by
semisimplicity) and uses that the resulting endomorphism is a scalar multiple of the
identity. -/
theorem isSimpleModule_of_finrank_end_eq_one {k R M : Type*} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [IsSemisimpleModule R M] [Nontrivial M]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  -- the identity is a nonzero endomorphism
  have h1 : (1 : Module.End R M) ≠ 0 := by
    intro hz
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial M).exists_pair_ne
    refine hxy ?_
    have hx : x = 0 := by
      have := congrArg (fun f : Module.End R M => f x) hz
      simpa using this
    have hy : y = 0 := by
      have := congrArg (fun f : Module.End R M => f y) hz
      simpa using this
    rw [hx, hy]
  -- hence every endomorphism is a scalar multiple of the identity
  have key : ∀ f : Module.End R M, ∃ c : k, c • (1 : Module.End R M) = f :=
    (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) h1).mp h
  haveI : Nontrivial (Submodule R M) := by
    refine ⟨⊥, ⊤, fun hz => ?_⟩
    have hsub : Subsingleton M := by
      refine ⟨fun x y => ?_⟩
      have hx : x ∈ (⊥ : Submodule R M) := by rw [hz]; exact Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule R M) := by rw [hz]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub
  refine IsSimpleModule.mk (toIsSimpleOrder := IsSimpleOrder.mk fun S => ?_)
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · refine Or.inr ?_
    obtain ⟨T, hc⟩ := exists_isCompl S
    have hrange : (Submodule.projection S T hc).range = S := Submodule.range_projection hc
    have hp : Submodule.projection S T hc ≠ 0 := by
      intro hp0
      exact hS (by rw [← hrange, hp0, LinearMap.range_zero])
    obtain ⟨c, hc'⟩ := key (Submodule.projection S T hc)
    have hc0 : c ≠ 0 := by
      intro hc0
      refine hp ?_
      rw [← hc', hc0, zero_smul]
    have htop : (Submodule.projection S T hc).range = ⊤ := by
      rw [← hc']
      have hone : (1 : Module.End R M) = LinearMap.id := rfl
      rw [hone]
      refine LinearMap.range_eq_top.mpr fun y => ⟨c⁻¹ • y, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ hc0,
        one_smul]
    rwa [hrange] at htop

/-- **Converse of Schur's lemma** for finite dimensional complex representations of a finite
group: a representation whose space of equivariant endomorphisms is one dimensional is
simple. -/
theorem simple_of_finrank_hom_self_eq_one {G : Type*} [Group G] [Fintype G] (V : FDRep ℂ G)
    (h : Module.finrank ℂ (V ⟶ V) = 1) : CategoryTheory.Simple V := by
  -- rewrite `V ⟶ V` as the space of `ℂ[G]`-linear endomorphisms of the module `V.ρ.asModule`
  have e₁ : (V ⟶ V) ≃ₗ[ℂ] Representation.IntertwiningMap V.ρ V.ρ :=
    (Representation.linHom.invariantsEquivFDRepHom V V).symm.trans
      (Representation.invariantsEquivIntertwiningMap V.ρ V.ρ)
  have e₂ : Representation.IntertwiningMap V.ρ V.ρ ≃ₗ[ℂ]
      Module.End ℂ[G] (Representation.asModule V.ρ) :=
    (Representation.IntertwiningMap.equivAlgEnd V.ρ).toLinearEquiv
  have hEnd : Module.finrank ℂ (Module.End ℂ[G] (Representation.asModule V.ρ)) = 1 := by
    rw [← LinearEquiv.finrank_eq e₂, ← LinearEquiv.finrank_eq e₁]
    exact h
  -- `V` is a nontrivial representation
  have hnt : Nontrivial ↥V := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    haveI : Subsingleton (V ⟶ V) := ⟨fun f g => by
      apply Action.hom_ext
      apply FGModuleCat.hom_ext
      ext x
      exact Subsingleton.elim _ _⟩
    have h0 : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
    rw [h] at h0
    exact Nat.one_ne_zero h0
  haveI hntM : Nontrivial (Representation.asModule V.ρ) := hnt
  have hsimple : IsSimpleModule ℂ[G] (Representation.asModule V.ρ) :=
    isSimpleModule_of_finrank_end_eq_one hEnd
  exact (Work.CharCore.fdRep_simple_iff V).mpr
    ((Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mpr hsimple)

end Work.Clifford
