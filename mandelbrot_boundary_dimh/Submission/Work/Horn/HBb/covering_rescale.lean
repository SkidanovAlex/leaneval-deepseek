import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts

namespace Work.Horn.HBb

open MandelDim Set Metric Filter Topology

/-- The map `ζ ↦ s * ζ` sends a covering of `S` by `G|D` to a covering of `s • S` by the
conjugated map `z ↦ s * G (z / s)`: conjugation by the homeomorphism `Homeomorph.mulLeft₀ s hs`
of `ℂ` preserves the property of being a covering map. -/
theorem covering_rescale {G : ℂ → ℂ} {D : Set ℂ} {s : ℂ} (hs : s ≠ 0) {S : Set ℂ}
    (hcov : IsCoveringMapOn (fun z : ↥D => G z) S) :
    IsCoveringMapOn (fun z : ↥((fun ζ : ℂ => s * ζ) '' D) => s * G (z / s))
      ((fun ζ : ℂ => s * ζ) '' S) := by
  -- The rescaling homeomorphism `φ : ζ ↦ s * ζ` of `ℂ`.
  let φ : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ s hs
  -- Membership of `z / s` in `D` for `z ∈ s • D`.
  have hmem : ∀ z : ↥((fun ζ : ℂ => s * ζ) '' D), (z : ℂ) / s ∈ D := by
    intro z
    obtain ⟨w, hw, hwz⟩ := z.2
    rw [← hwz]
    rw [show (fun ζ : ℂ => s * ζ) w / s = w from mul_div_cancel_left₀ w hs]
    exact hw
  -- The homeomorphism `↥(s • D) ≃ₜ ↥D` induced by `φ⁻¹`, `z ↦ z / s`.
  let Ψ : ↥((fun ζ : ℂ => s * ζ) '' D) ≃ₜ ↥D :=
  { toFun := fun z => ⟨(z : ℂ) / s, hmem z⟩
    invFun := fun w => ⟨s * (w : ℂ), ⟨(w : ℂ), w.2, rfl⟩⟩
    left_inv := by intro z; ext; exact mul_div_cancel₀ (z : ℂ) hs
    right_inv := by intro w; ext; exact mul_div_cancel_left₀ (w : ℂ) hs
    continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.div_const s) hmem
    continuous_invFun := Continuous.subtype_mk (continuous_const.mul continuous_subtype_val)
      (fun w => ⟨(w : ℂ), w.2, rfl⟩) }
  -- Post-composition with the homeomorphism `φ` rescales the base.
  have h2 : IsCoveringMapOn (fun z : ↥D => φ (G z)) (φ.symm ⁻¹' S) := hcov.homeomorph_comp φ
  -- Pre-composition with the homeomorphism `Ψ` rescales the domain.
  have h3 : IsCoveringMapOn ((fun z : ↥D => φ (G z)) ∘ Ψ) (φ.symm ⁻¹' S) :=
    h2.comp_homeomorph Ψ
  have hbase : φ.symm ⁻¹' S = (fun ζ : ℂ => s * ζ) '' S := by
    rw [← φ.image_eq_preimage_symm]
    exact Set.image_congr fun z _ => by simp [φ]
  have hmap : ((fun z : ↥D => φ (G z)) ∘ Ψ) =
      fun z : ↥((fun ζ : ℂ => s * ζ) '' D) => s * G (z / s) := by
    funext z
    show φ (G (Ψ z : ↥D)) = s * G ((z : ℂ) / s)
    have h : (Ψ z : ℂ) = (z : ℂ) / s := rfl
    rw [h]
    simp [φ]
  rw [hbase, hmap] at h3
  exact h3

end Work.Horn.HBb
