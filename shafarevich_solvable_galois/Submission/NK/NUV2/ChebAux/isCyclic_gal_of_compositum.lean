import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.ChebAux

/-- If `E` is the compositum of a Galois extension `L/K` and a Galois extension `M/K` (inside `E`),
then `Gal(E/M)` is cyclic whenever `Gal(L/K)` is cyclic: restriction to `L` gives an injective
group homomorphism `Gal(E/M) →* Gal(L/K)`, and subgroups of cyclic groups are cyclic. -/
theorem isCyclic_gal_of_compositum {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois M E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcyc : IsCyclic (L ≃ₐ[K] L)) : IsCyclic (E ≃ₐ[M] E) := by
  -- The restriction map `Gal(E/M) →* Gal(L/K)`: view an `M`-algebra automorphism of `E`
  -- as a `K`-algebra automorphism (restriction of scalars) and restrict it to the normal
  -- subfield `L ⊆ E`.
  let φ : (E ≃ₐ[M] E) →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom (F := K) L).comp
      (AlgEquiv.restrictScalarsHom K (S := M) (A := E))
  refine isCyclic_of_injective φ ?_
  -- `φ` is injective: an automorphism acting trivially on `L` and fixing `M` is trivial,
  -- because `E` is generated over `K` by `L` and `M`.
  intro σ τ h
  have hres : (σ.restrictScalars K).restrictNormal L
      = (τ.restrictScalars K).restrictNormal L := h
  have hL : ∀ x : L, σ (algebraMap L E x) = τ (algebraMap L E x) := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes (χ := σ.restrictScalars K) L x
    have h2 := AlgEquiv.restrictNormal_commutes (χ := τ.restrictScalars K) L x
    calc σ (algebraMap L E x)
        = (σ.restrictScalars K) (algebraMap L E x) := rfl
      _ = algebraMap L E (((σ.restrictScalars K).restrictNormal L) x) := h1.symm
      _ = algebraMap L E (((τ.restrictScalars K).restrictNormal L) x) := by rw [hres]
      _ = (τ.restrictScalars K) (algebraMap L E x) := h2
      _ = τ (algebraMap L E x) := rfl
  have hAlg : (σ.restrictScalars K).toAlgHom = (τ.restrictScalars K).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    intro x hx
    rcases hx with ⟨y, hy⟩ | ⟨m, hm⟩
    · rw [← hy]; exact hL y
    · rw [← hm]; simp
  exact AlgEquiv.ext (fun x => AlgHom.congr_fun hAlg x)

end NK.NUV2.ChebAux
