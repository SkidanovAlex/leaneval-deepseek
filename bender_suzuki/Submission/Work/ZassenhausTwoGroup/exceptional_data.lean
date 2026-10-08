import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-- **Exceptional data.**  A `τ`-coherent orthonormal set `S` of characters of `H` admits an
extension `τ'` which agrees with `τ` on `ℤ[S]^0`, is an isometry of the full lattice `ℤ[S]`,
sends each element of `S` to a virtual character of `G`, and in fact sends each element of `S`
to `±` an irreducible character of `G`.

The last (exceptional) property is not an extra hypothesis: it is forced by the first two.
Indeed `S` being orthonormal (`horth`) and `τ'` being an isometry of `ℤ[S]` (`hiso`) give
`⟪τ' χ, τ' χ⟫ = ⟪χ, χ⟫ = 1` for every `χ ∈ S`, and a virtual character of norm one is `±` an
irreducible character: this is exactly `Work.Coherence.isometry_image_irr`. -/
theorem exceptional_data {H : Type} [Group H] [Fintype H] {G : Type} [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hC : Work.Coherence.Coherent S τ) (horth : Work.Coherence.Orthonormal S) :
    ∃ τ' : (H → ℂ) →ₗ[ℤ] (G → ℂ),
      (∀ α ∈ Work.Coherence.ZSpan0 S, τ' α = τ α) ∧
      Work.Coherence.IsometryOnAll S τ' ∧
      (∀ χ ∈ S, Work.Coherence.IsVChar (τ' χ)) ∧
      ∀ χ ∈ S, ∃ e ∈ Work.Coherence.Irr G, τ' χ = e ∨ τ' χ = -e := by
  obtain ⟨τ', h₀, hiso, hvchar⟩ := hC
  exact ⟨τ', h₀, hiso, hvchar,
    fun χ hχ => Work.Coherence.isometry_image_irr horth hiso hχ (hvchar χ hχ)⟩

end Work.ZassenhausTwoGroup
