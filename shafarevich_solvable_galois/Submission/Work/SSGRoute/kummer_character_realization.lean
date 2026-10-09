import Mathlib
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Classical

/-- **Realization of Kummer characters.**

Let `E/U` be a finite Galois extension whose degree `d = [E : U]` divides `n`, and let
`ω : Gal(E/U) → μ_n(U)` be a character with values in the `n`-th roots of unity of `U`.
Then there is `γ ∈ E` with `γ ^ n ∈ U` and `σ γ / γ = ω σ` for every `σ ∈ Gal(E/U)`.

The proof is Hilbert's theorem 90 (Noether's crossed-homomorphism form) applied to the crossed
homomorphism `σ ↦ ω σ` (a unit of `E`): it produces `b ∈ Eˣ` with `ω σ = σ b / b`; then `b ^ n`
is fixed by every `σ`, hence lies in `U` by the Galois fixed-field theorem. -/
theorem kummer_character_realization
    {U E : Type*} [Field U] [Field E] [Algebra U E]
    [FiniteDimensional U E] [IsGalois U E] [IsCyclic Gal(E/U)]
    (hζ : ∃ ζ : U, IsPrimitiveRoot ζ (Module.finrank U E))
    {n : ℕ} (hdvd : Module.finrank U E ∣ n)
    (ω : Gal(E/U) →* ↥(rootsOfUnity n U)) :
    ∃ γ : E, γ ^ n ∈ Set.range (algebraMap U E) ∧
      ∀ σ : Gal(E/U),
        σ γ / γ = algebraMap U E (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U) := by
  -- The character, viewed as a unit of `E`.
  let f : Gal(E/U) → Eˣ := fun σ =>
    Units.map (algebraMap U E).toMonoidHom (((ω σ : ↥(rootsOfUnity n U)) : Uˣ))
  have hfval : ∀ σ : Gal(E/U), ((f σ : Eˣ) : E)
      = algebraMap U E (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U) := by
    intro σ
    simp [f]
  -- The values of `f` are `n`-th roots of unity.
  have hfpow : ∀ σ : Gal(E/U), (f σ : E) ^ n = 1 := by
    intro σ
    have hu : ((((ω σ : ↥(rootsOfUnity n U)) : Uˣ)) : U) ^ n = 1 :=
      (mem_rootsOfUnity' n ((ω σ : ↥(rootsOfUnity n U)) : Uˣ)).mp (ω σ).2
    rw [hfval σ, ← map_pow, hu, map_one]
  -- `f` is a crossed homomorphism, because `σ` fixes the values of `ω`.
  have hcross : ∀ σ τ : Gal(E/U),
      ((f (σ * τ) : Eˣ) : E) = ((f σ : Eˣ) : E) * σ ((f τ : Eˣ) : E) := by
    intro σ τ
    have hfix : σ ((f τ : Eˣ) : E) = ((f τ : Eˣ) : E) := by
      rw [hfval τ]
      exact AlgEquiv.commutes σ _
    rw [hfval (σ * τ), hfval σ, hfix, hfval τ, map_mul ω σ τ, Subgroup.coe_mul]
    exact map_mul (algebraMap U E) _ _
  -- Hilbert 90: `f` is a coboundary.
  obtain ⟨b, hb⟩ := Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom f hcross
  have hbne : (b : E) ≠ 0 := b.ne_zero
  refine ⟨(b : E), ?_, ?_⟩
  · -- `b ^ n` is fixed by `Gal(E/U)`, hence lies in `U`.
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    have hsb : σ (b : E) = (f σ : E) * (b : E) := by
      rw [hb σ]
      rw [div_mul_cancel₀ _ hbne]
    rw [map_pow, hsb, mul_pow, hfpow σ, one_mul]
  · -- `σ b / b = ω σ`.
    intro σ
    rw [← hb σ, hfval σ]

end Work.SSGRoute
