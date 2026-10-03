import Mathlib

namespace Work.Horn

/-- If `p : ℂ → ℂ`, restricted to `Ω` as a map `↥Ω → ℂ`, is a covering map over `D`, then the
restriction of `p` to the preimage `{z ∈ Ω | p z ∈ D}`, viewed as a map onto `↥D`, is a covering
map.

This is Mathlib's `IsCoveringMapOn.isCoveringMap_restrictPreimage` up to the canonical
homeomorphism identifying `↥{z : ℂ | z ∈ Ω ∧ p z ∈ D}` with
`↥((fun z : ↥Ω => p z) ⁻¹' D)`. -/
theorem isCoveringMapOn_restrictToPreimage {Ω D : Set ℂ} {p : ℂ → ℂ}
    (hcov : IsCoveringMapOn (fun z : ↥Ω => p z) D) :
    IsCoveringMap (fun w : ↥{z : ℂ | z ∈ Ω ∧ p z ∈ D} => (⟨p w.1, w.2.2⟩ : ↥D)) := by
  have h := hcov.isCoveringMap_restrictPreimage
  let g : ↥{z : ℂ | z ∈ Ω ∧ p z ∈ D} ≃ₜ ↥((fun z : ↥Ω => p z) ⁻¹' D) :=
  { toFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
    invFun := fun v => ⟨v.1.1, v.1.2, v.2⟩
    left_inv := fun w => rfl
    right_inv := fun v => rfl
    continuous_toFun := by continuity
    continuous_invFun := by continuity }
  have h2 := h.comp_homeomorph g
  convert h2 using 1
  ext w
  rfl

end Work.Horn
