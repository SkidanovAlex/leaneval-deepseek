import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Submission.NK.GlobalCFT.Inclusion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Inclusion

/-- **Noether's generalisation of Hilbert's Theorem 90** in the form needed here: every
`Gal(L/K)`-cocycle `a` with values in `Lˣ`, where the action is the natural one and the
cocycle condition is written `a (σ * τ) = a σ * σ (a τ)`, is a coboundary
`a σ = σ b * b⁻¹`.

The cocycle convention used by `groupCohomology.IsMulCocycle₁` is the mirror image
`a (σ * τ) = σ (a τ) * a σ`; since `Lˣ` is commutative the two agree, which is the only
translation needed to invoke Mathlib's `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`
(Noether's theorem: `H¹(Aut_K L, Lˣ) = 0` for any finite extension `L/K`). -/
theorem hilbert90_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (a : (L ≃ₐ[K] L) → Lˣ)
    (ha : ∀ σ τ : L ≃ₐ[K] L, a (σ * τ) = a σ * Units.map σ.toMonoidHom (a τ)) :
    ∃ b : Lˣ, ∀ σ : L ≃ₐ[K] L, a σ = Units.map σ.toMonoidHom b * b⁻¹ := by
  -- Translate the cocycle condition into Mathlib's convention (`Lˣ` is commutative).
  have hc : groupCohomology.IsMulCocycle₁ a := by
    intro σ τ
    rw [ha σ τ]
    exact mul_comm _ _
  -- Noether's theorem: `H¹(Aut_K L, Lˣ) = 0`, i.e. every `1`-cocycle is a coboundary.
  obtain ⟨b, hb⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units a hc
  refine ⟨b, fun σ => ?_⟩
  -- `hb σ : σ • b / b = a σ`, and `σ • b = Units.map σ b`.
  have h := hb σ
  rw [AlgEquiv.smul_units_def, div_eq_mul_inv] at h
  exact h.symm

end NK.GlobalCFT.Inclusion
