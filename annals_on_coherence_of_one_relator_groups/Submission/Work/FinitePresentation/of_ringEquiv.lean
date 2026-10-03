import Mathlib

set_option linter.style.haveILetI false

universe u v

namespace Work.FinitePresentation

/-- Finitely presented modules are transported along a ring equivalence together with a
compatible additive equivalence of the underlying additive groups.

The argument is the standard one: write `M` as a quotient `(Fin n → R) ⧸ K` with `K` finitely
generated (`Module.FinitePresentation.exists_fin`), then conjugate the quotient map by the ring
equivalence `φ` (acting coefficientwise) and by `ψ`, producing a surjection
`(Fin n → S) →ₗ[S] N` whose kernel is the `φ`-image of `K`, hence finitely generated. -/
theorem of_ringEquiv {R S : Type u} [Ring R] [Ring S] {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] (φ : R ≃+* S) (ψ : M ≃+ N) (hψ : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m) : Module.FinitePresentation R M → Module.FinitePresentation S N := by
  intro h
  -- `φ` makes the two module structures comparable, so semilinear maps over `φ` are available.
  haveI hφ1 : RingHomInvPair (φ : R →+* S) (φ.symm : S →+* R) := RingHomInvPair.of_ringEquiv φ
  haveI hφ2 : RingHomInvPair (φ.symm : S →+* R) (φ : R →+* S) := RingHomInvPair.of_ringEquiv_symm φ
  -- Write `M` as a quotient of a finite free `R`-module by a finitely generated submodule.
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  let p : (Fin n → R) →ₗ[R] M := e.symm.toLinearMap.comp K.mkQ
  have hp : Function.Surjective p := e.symm.surjective.comp K.mkQ_surjective
  have hpk : LinearMap.ker p = K := by simp [p, LinearMap.ker_comp, Submodule.ker_mkQ]
  -- The coefficientwise ring equivalence `(Fin n → R) ≃ (Fin n → S)`, as a `φ`-semilinear map.
  let Φ : (Fin n → R) ≃ₛₗ[(φ : R →+* S)] (Fin n → S) :=
  { toFun := fun x i => φ (x i)
    invFun := fun x i => φ.symm (x i)
    left_inv := fun x => by ext i; simp
    right_inv := fun x => by ext i; simp
    map_add' := fun x y => by ext i; simp
    map_smul' := fun r x => by ext i; simp [map_mul] }
  let Φi : (Fin n → S) → (Fin n → R) := fun x i => φ.symm (x i)
  have hΦi_add : ∀ x y : Fin n → S, Φi (x + y) = Φi x + Φi y := by
    intro x y; ext i; simp [Φi]
  have hΦi_smul : ∀ (s : S) (x : Fin n → S), Φi (s • x) = φ.symm s • Φi x := by
    intro s x; ext i; simp [Φi, map_mul]
  have hΦ_Φi : ∀ x, Φ (Φi x) = x := by intro x; ext i; simp [Φ, Φi]
  have hΦi_Φ : ∀ y, Φi (Φ y) = y := by intro y; ext i; simp [Φ, Φi]
  -- Conjugate the surjection `p` by `Φ` (on the source) and `ψ` (on the target).
  let p' : (Fin n → S) →ₗ[S] N :=
  { toFun := fun x => ψ (p (Φi x))
    map_add' := by intro x y; rw [hΦi_add, p.map_add, ψ.map_add]
    map_smul' := by
      intro s x
      rw [hΦi_smul, p.map_smul, hψ (φ.symm s) (p (Φi x)), φ.apply_symm_apply]
      simp }
  have hp' : Function.Surjective p' := by
    intro y
    obtain ⟨z, hz⟩ := hp (ψ.symm y)
    refine ⟨Φ z, ?_⟩
    show ψ (p (Φi (Φ z))) = y
    rw [hΦi_Φ z, hz, ψ.apply_symm_apply]
  -- Its kernel is the `Φ`-image of `K`, hence finitely generated.
  have hker : LinearMap.ker p' = Submodule.map (Φ.toLinearMap) K := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_map]
    change ψ (p (Φi x)) = 0 ↔ ∃ y ∈ K, Φ y = x
    constructor
    · intro hx
      refine ⟨Φi x, ?_, hΦ_Φi x⟩
      rw [← hpk]
      exact LinearMap.mem_ker.mpr (ψ.injective (by rw [hx, ψ.map_zero]))
    · rintro ⟨k, hk, rfl⟩
      have hk' : k ∈ LinearMap.ker p := by rwa [hpk]
      change ψ (p (Φi (Φ k))) = 0
      rw [hΦi_Φ k, LinearMap.mem_ker.mp hk', ψ.map_zero]
  have hK' : (LinearMap.ker p').FG := by
    rw [hker]
    exact Submodule.FG.map Φ.toLinearMap hK
  exact Module.finitePresentation_of_free_of_surjective p' hp' hK'

end Work.FinitePresentation
