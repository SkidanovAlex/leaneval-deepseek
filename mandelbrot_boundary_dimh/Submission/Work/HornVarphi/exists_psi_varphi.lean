import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Parab.Setup
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# A holomorphic right inverse of the Fatou coordinate on the repelling sector

For §4.1 data `d : ParabData f₀ D₀`, the Fatou coordinate `d.φ` is holomorphic on its maximal
domain `Dφ` and injective on Shishikura's repelling sector `Q₀ = QLeft d.ξ₀ ⊆ Dφ`.  An injective
holomorphic function on an open set has nowhere vanishing derivative
(`Work.Parab.inversion.deriv_ne_zero_of_injOn`), so it is a local biholomorphism everywhere on
`Q₀`.  Since it is injective there, these local inverses patch to a single holomorphic map `ψ`
defined on the image `d.φ '' Q₀`, which is the two-sided inverse of `d.φ` on `Q₀`.
-/

namespace Work.HornVarphi

open Complex Set Metric Filter
open scoped Topology

/-- **A holomorphic inverse of `φ` on the left sector.**

`ψ` is the set-theoretic inverse of the bijection `d.φ : QLeft ξ₀ → d.φ '' QLeft ξ₀`; it is
holomorphic because `d.φ` has non-vanishing derivative on the open sector (being injective and
holomorphic), i.e. the inverse function theorem applies at every point. -/
theorem exists_psi_varphi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) : ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (d.φ '' MandelDim.QLeft d.ξ₀) ∧ (∀ u ∈ MandelDim.QLeft d.ξ₀, ψ (d.φ u) = u) ∧ (∀ ζ ∈ d.φ '' MandelDim.QLeft d.ξ₀, ψ ζ ∈ MandelDim.QLeft d.ξ₀ ∧ d.φ (ψ ζ) = ζ) := by
  classical
  -- The inverse map: send `ζ` to the (unique) preimage of `ζ` lying in the sector.
  let ψ : ℂ → ℂ := fun ζ => if h : ∃ u ∈ MandelDim.QLeft d.ξ₀, d.φ u = ζ then h.choose else 0
  have hψeq : ∀ (ζ : ℂ) (h : ∃ u ∈ MandelDim.QLeft d.ξ₀, d.φ u = ζ), ψ ζ = h.choose :=
    fun ζ h => dite_eq_left h
  -- `ψ` is a left inverse of `φ` on the sector.
  have hψleft : ∀ u ∈ MandelDim.QLeft d.ξ₀, ψ (d.φ u) = u := by
    intro u hu
    have h : ∃ u' ∈ MandelDim.QLeft d.ξ₀, d.φ u' = d.φ u := ⟨u, hu, rfl⟩
    rw [hψeq (d.φ u) h]
    exact d.φ_inj h.choose_spec.1 hu h.choose_spec.2
  -- and a right inverse on the image.
  have hψmem : ∀ ζ ∈ d.φ '' MandelDim.QLeft d.ξ₀, ψ ζ ∈ MandelDim.QLeft d.ξ₀ ∧ d.φ (ψ ζ) = ζ := by
    intro ζ hζ
    rw [hψeq ζ hζ]
    exact ⟨hζ.choose_spec.1, hζ.choose_spec.2⟩
  refine ⟨ψ, ?_, hψleft, hψmem⟩
  -- Holomorphy: at `d.φ u₀`, `ψ` agrees with the local inverse of `φ` at `u₀`, which is holomorphic.
  intro ζ hζ
  obtain ⟨u₀, hu₀, rfl⟩ := hζ
  have hana : AnalyticAt ℂ d.φ u₀ := d.φ_holo.analyticAt (d.Dφ_open.mem_nhds (d.Q_sub hu₀))
  have hsd : HasStrictDerivAt d.φ (deriv d.φ u₀) u₀ := hana.hasStrictDerivAt
  have hne : deriv d.φ u₀ ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn (Work.Parab.isOpen_QLeft d.ξ₀)
      (d.φ_holo.mono d.Q_sub) d.φ_inj u₀ hu₀
  -- `ψ (φ x) = x` for `x` near `u₀`, since the sector is open and contains `u₀`.
  have hg : ∀ᶠ x in 𝓝 u₀, ψ (d.φ x) = x := by
    filter_upwards [(Work.Parab.isOpen_QLeft d.ξ₀).mem_nhds hu₀] with x hx
    exact hψleft x hx
  -- hence `ψ` has a strict derivative at `d.φ u₀`, by the inverse function theorem.
  exact (hsd.to_local_left_inverse hne hg).hasDerivAt.differentiableAt.differentiableWithinAt

end Work.HornVarphi
