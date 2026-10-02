import Mathlib
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.radialRay_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Rays

/-- If the sublevel sets of a dynamic ray are nonempty for every radius `> 1`, then each of them
is infinite: every point of the ray has Böttcher modulus `> 1`, so if a sublevel set `S_ρ` were
finite and nonempty there would be a minimal modulus `m > 1` in it, and `S_σ = ∅` for
`1 < σ < m`, contradicting the hypothesis. -/
theorem dynRay_sublevel_infinite {c : ℂ} {φ : ℂ → ℂ} {θ : ℝ} {ρ : ℝ} (hρ : 1 < ρ)
    (hne : ∀ σ : ℝ, 1 < σ → ∃ z : ℂ, z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ σ) :
    {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}.Infinite := by
  intro hfin
  -- the sublevel set is nonempty by the hypothesis at radius `ρ`
  have hneS : {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}.Nonempty := by
    obtain ⟨z, hz, hzφ⟩ := hne ρ hρ
    exact ⟨z, hz, hzφ⟩
  -- hence it has a point of minimal Böttcher modulus
  obtain ⟨z₀, hz₀, hmin⟩ :=
    Set.exists_min_image {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}
      (fun z : ℂ => ‖φ z‖) hfin hneS
  -- every point of the ray has Böttcher modulus `> 1`
  have hz₀gt : 1 < ‖φ z₀‖ := radialRay_norm hz₀.1.2
  have hz₀ρ : ‖φ z₀‖ ≤ ρ := hz₀.2
  -- an intermediate radius below the minimal modulus contradicts the hypothesis
  obtain ⟨z, hz, hzφ⟩ := hne ((1 + ‖φ z₀‖) / 2) (by linarith)
  have hzS : z ∈ {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} :=
    ⟨hz, by linarith⟩
  have := hmin z hzS
  linarith

end Work.Landing.Rays
