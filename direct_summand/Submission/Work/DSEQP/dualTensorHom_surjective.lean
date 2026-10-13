import Mathlib

/-!
# Surjectivity of `M^* ⊗ N → Hom(M, N)` for `M` finitely presented and `N` flat

For a commutative ring `R`, a finitely presented `R`-module `M` and a flat `R`-module `N`,
the canonical evaluation map
`dualTensorHom R M N : M^* ⊗[R] N → (M →ₗ[R] N)`, `f ⊗ n ↦ (m ↦ f m • n)`, is surjective.

The proof writes `M` as the cokernel of a map `g : R^m → R^n` between finite free modules
(`Module.FinitePresentation.exists_fin'`).  The dual sequence
`Dual M --f.dualMap--> Dual R^n --g.dualMap--> Dual R^m` is exact, and — `N` being flat —
stays exact after tensoring with `N`.  For the finite free module `R^n` the map
`dualTensorHom` is an isomorphism, which turns the exactness statement into the required
surjectivity of `dualTensorHom R M N`.
-/

open TensorProduct

namespace Work.DSEQP

/-- Dualising a right exact sequence of `R`-modules is exact: if `M --g--> N --f--> P` is
exact with `f` surjective, then `P^* --f^*--> N^* --g^*--> M^*` is exact. -/
lemma dualMap_exact {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] P) (g : M →ₗ[R] N) (hf : Function.Surjective f) (h : Function.Exact g f) :
    Function.Exact f.dualMap g.dualMap := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective f hf,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range g, h]

theorem dualTensorHom_surjective (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R N] : Function.Surjective (dualTensorHom R M N) := by
  -- A finite free presentation of `M`: `(Fin m → R) --g--> (Fin n → R) --f--> M`.
  obtain ⟨n, m, f, g, hf, hex⟩ := Module.FinitePresentation.exists_fin' R M
  have hker : LinearMap.ker f = LinearMap.range g := LinearMap.exact_iff.mp hex
  -- Dualising and tensoring with the flat module `N` preserves exactness.
  have hexd : Function.Exact f.dualMap g.dualMap := dualMap_exact f g hf hex
  have hexN : Function.Exact (LinearMap.rTensor N f.dualMap) (LinearMap.rTensor N g.dualMap) :=
    Module.Flat.rTensor_exact N hexd
  have hfg : f ∘ₗ g = 0 := by
    apply DFunLike.ext
    intro z
    have hz : g z ∈ LinearMap.ker f := by
      rw [hker]
      exact LinearMap.mem_range_self g z
    simpa using LinearMap.mem_ker.mp hz
  intro x
  -- The induced map `x ∘ f` on the finite free module `(Fin n → R)`.
  set y : (Fin n → R) →ₗ[R] N := LinearMap.lcomp R N f x with hydef
  have hy : dualTensorHom R (Fin n → R) N
      ((dualTensorHomEquiv R (Fin n → R) N).symm y) = y :=
    (dualTensorHomEquiv R (Fin n → R) N).apply_symm_apply y
  -- `y` is killed by `g.lcomp`, since `f ∘ g = 0`.
  have hgy : LinearMap.lcomp R N g y = 0 := by
    apply DFunLike.ext
    intro z
    simp only [LinearMap.lcomp_apply, hydef, LinearMap.zero_apply]
    have hz : f (g z) = 0 := by
      have h := DFunLike.congr_fun hfg z
      simpa using h
    simp [hz]
  -- The preimage of `y` under the isomorphism for the free module `R^n` is killed by
  -- `g.dualMap ⊗ N`.
  have hnat : dualTensorHom R (Fin m → R) N
      (LinearMap.rTensor N g.dualMap ((dualTensorHomEquiv R (Fin n → R) N).symm y)) =
      LinearMap.lcomp R N g (dualTensorHom R (Fin n → R) N
        ((dualTensorHomEquiv R (Fin n → R) N).symm y)) := by
    have h := DFunLike.congr_fun (dualTensorHom_comp_rTensor_dualMap (R := R) (M := Fin m → R)
      (N := Fin n → R) (P := N) g) ((dualTensorHomEquiv R (Fin n → R) N).symm y)
    simpa using h
  have hw : LinearMap.rTensor N g.dualMap
      ((dualTensorHomEquiv R (Fin n → R) N).symm y) = 0 := by
    refine (dualTensorHomEquiv R (Fin m → R) N).injective ?_
    rw [map_zero]
    change dualTensorHom R (Fin m → R) N (LinearMap.rTensor N g.dualMap
      ((dualTensorHomEquiv R (Fin n → R) N).symm y)) = 0
    rw [hnat, hy, hgy]
  -- Exactness of the dual sequence after tensoring exhibits the preimage in the range of
  -- `f.dualMap ⊗ N`.
  have hmem : (dualTensorHomEquiv R (Fin n → R) N).symm y ∈
      LinearMap.range (LinearMap.rTensor N f.dualMap) := by
    rw [← LinearMap.exact_iff.mp hexN, LinearMap.mem_ker]
    exact hw
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hmem
  -- `z` is the required preimage of `x`.
  refine ⟨z, ?_⟩
  refine LinearMap.lcomp_injective_of_surjective (R := R) (S := R) (N := N) f hf ?_
  have hnat' : LinearMap.lcomp R N f (dualTensorHom R M N z) =
      dualTensorHom R (Fin n → R) N (LinearMap.rTensor N f.dualMap z) := by
    have h := DFunLike.congr_fun (dualTensorHom_comp_rTensor_dualMap (R := R) (M := Fin n → R)
      (N := M) (P := N) f) z
    simpa using h.symm
  rw [hnat', hz, hy]

end Work.DSEQP
