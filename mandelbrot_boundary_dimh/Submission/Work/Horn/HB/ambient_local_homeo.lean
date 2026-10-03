import Mathlib

namespace Work.Horn.HB

/-- A covering map of the open subspace `D` over the twice-punctured plane restricts, as an
ambient map `g : ℂ → ℂ`, to a local homeomorphism on `D ∩ g ⁻¹' {0, v}ᶜ`.  (The openness of `D`
is what allows the local charts of the covering map to be promoted to charts of `g` as a map of
`ℂ`.) -/
theorem ambient_local_homeo {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} (hDo : IsOpen D)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v}) :
    IsLocalHomeomorphOn g (D ∩ g ⁻¹' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v}) := by
  set s : Set ℂ := {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} with hs
  -- the covering map of the subspace `D` is a local homeomorphism
  have h1 : IsLocalHomeomorphOn (fun z : ↥D => g z) ((fun z : ↥D => g z) ⁻¹' s) :=
    hcov.isLocalHomeomorphOn
  -- the inclusion `↥D → ℂ` is an open embedding, hence a local homeomorphism
  have h2 : IsLocalHomeomorphOn (Subtype.val : ↥D → ℂ) ((fun z : ↥D => g z) ⁻¹' s) :=
    (hDo.isOpenEmbedding_subtypeVal.isLocalHomeomorph).isLocalHomeomorphOn
  have h3 := IsLocalHomeomorphOn.of_comp_right h1 h2
  have hset : (Subtype.val '' ((fun z : ↥D => g z) ⁻¹' s)) = D ∩ g ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hyD, hy⟩
      exact ⟨⟨y, hyD⟩, hy, rfl⟩
  rw [hset] at h3
  rwa [hs] at h3

end Work.Horn.HB
