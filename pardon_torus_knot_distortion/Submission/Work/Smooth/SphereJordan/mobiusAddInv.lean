import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

open Filter
open scoped _root_.Topology

namespace Work.Smooth.SphereJordan

noncomputable section

open Classical

/-!
# The Möbius homeomorphism `z ↦ λ + z⁻¹` of the Riemann sphere

This file constructs the self-homeomorphism of the Riemann sphere `ℂ ∪ {∞}` sending
`∞ ↦ λ`, `0 ↦ ∞` and `z ↦ λ + z⁻¹` for `z ≠ 0`.  It is the coordinate change used to move
a base point of a simple closed curve off `∞` (a Möbius transformation of `ℂ ∪ {∞}`).

The construction proceeds in two steps, each of which is a composition of homeomorphisms:

* `invMap` — the inversion `z ↦ z⁻¹` of the Riemann sphere (with `0 ↦ ∞`, `∞ ↦ 0`), whose
  continuity follows from `tendsto_inv₀_cobounded`, `tendsto_inv₀_nhdsNE_zero` and the
  identification `coclosedCompact ℂ = cobounded ℂ` of the neighbourhoods of infinity in the
  one-point compactification of a proper space;
* `Homeomorph.onePointCongr (Homeomorph.addRight λ)` — the translation `z ↦ z + λ` of the
  finite part, fixing `∞`.

Their composite is the required Möbius transformation.
-/

/-- The inversion `z ↦ z⁻¹` of the Riemann sphere, with `0 ↦ ∞` and `∞ ↦ 0`. -/
def invMap : RiemannSphere → RiemannSphere :=
  fun x => x.elim ((0 : ℂ) : RiemannSphere)
    (fun z => if z = 0 then infty else ((z⁻¹ : ℂ) : RiemannSphere))

theorem invMap_infty : invMap infty = ((0 : ℂ) : RiemannSphere) := rfl

theorem invMap_coe_zero : invMap ((0 : ℂ) : RiemannSphere) = infty := by
  simp [invMap]

theorem invMap_coe_ne {z : ℂ} (hz : z ≠ 0) :
    invMap (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [invMap, hz]

/-- The inversion of the Riemann sphere is an involution. -/
theorem invMap_involutive : Function.Involutive invMap := by
  intro x
  induction x using OnePoint.rec with
  | infty => simp [invMap]
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · simp [invMap]
    · rw [invMap_coe_ne hz, invMap_coe_ne (inv_ne_zero hz), inv_inv]

/-- Inversion on the plane tends to the base point `0` of the Riemann sphere as `z → ∞`. -/
theorem tendsto_inv_coclosedCompact_zero :
    Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : RiemannSphere)) (coclosedCompact ℂ)
      (𝓝 (((0 : ℂ)) : RiemannSphere)) := by
  have h1 : Tendsto (fun z : ℂ => z⁻¹) (coclosedCompact ℂ) (𝓝 (0 : ℂ)) := by
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  exact (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp h1

/-- Inversion on the plane tends to `∞` of the Riemann sphere as `z → 0` through nonzero
points. -/
theorem tendsto_inv_nhdsNE_zero_infty :
    Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : RiemannSphere)) (𝓝[≠] (0 : ℂ)) (𝓝 infty) := by
  have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ)) (coclosedCompact ℂ) := by
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  exact OnePoint.tendsto_coe_infty.comp h1

/-- The extension of inversion to the Riemann sphere is continuous on the finite part (where it
is given by the piecewise formula `0 ↦ ∞`, `z ↦ z⁻¹`). -/
theorem continuous_invMap_coe :
    Continuous (fun z : ℂ => if z = 0 then infty else ((z⁻¹ : ℂ) : RiemannSphere)) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · have heq : (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun w : ℂ => if w = 0 then infty else ((w⁻¹ : ℂ) : RiemannSphere)) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{0}ᶜ, self_mem_nhdsWithin, ?_⟩
      intro w hw
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
      simp [hw]
    have h2 := tendsto_inv_nhdsNE_zero_infty.congr' heq
    have hpure : Tendsto
        (fun w : ℂ => if w = 0 then infty else ((w⁻¹ : ℂ) : RiemannSphere))
        (pure (0 : ℂ)) (𝓝 infty) := by
      simpa using tendsto_pure_nhds
        (fun w : ℂ => if w = 0 then infty else ((w⁻¹ : ℂ) : RiemannSphere)) (0 : ℂ)
    have hsup := h2.sup hpure
    rw [nhdsNE_sup_pure] at hsup
    rw [ContinuousAt]
    simpa using hsup
  · have heq : (fun w : ℂ => if w = 0 then infty else ((w⁻¹ : ℂ) : RiemannSphere)) =ᶠ[𝓝 z]
        (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere)) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨{0}ᶜ, IsOpen.mem_nhds isOpen_compl_singleton (by simpa using hz), ?_⟩
      intro w hw
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
      simp [hw]
    rw [continuousAt_congr heq]
    exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_id.inv₀ hz)

/-- The inversion `z ↦ z⁻¹` is a continuous self-map of the Riemann sphere. -/
theorem continuous_invMap : Continuous invMap := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun z : ℂ => if z = 0 then infty else ((z⁻¹ : ℂ) : RiemannSphere))
        (coclosedCompact ℂ) (𝓝 (((0 : ℂ)) : RiemannSphere)) := by
      refine tendsto_inv_coclosedCompact_zero.congr' ?_
      refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{0}ᶜ, ?_, ?_⟩
      · rw [Filter.coclosedCompact_eq_cocompact]
        exact isCompact_singleton.compl_mem_cocompact
      · intro w hw
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
        simp [hw]
    simpa [invMap] using h
  · simpa [invMap] using continuous_invMap_coe

/-- **Inversion as a homeomorphism of the Riemann sphere** (`0 ↦ ∞`, `∞ ↦ 0`,
`z ↦ z⁻¹` for `z ≠ 0`). -/
def invHomeomorph : RiemannSphere ≃ₜ RiemannSphere where
  toFun := invMap
  invFun := invMap
  left_inv := invMap_involutive
  right_inv := invMap_involutive
  continuous_toFun := continuous_invMap
  continuous_invFun := continuous_invMap

@[simp] theorem invHomeomorph_infty :
    invHomeomorph infty = ((0 : ℂ) : RiemannSphere) := rfl

@[simp] theorem invHomeomorph_coe_zero :
    invHomeomorph ((0 : ℂ) : RiemannSphere) = infty := invMap_coe_zero

@[simp] theorem invHomeomorph_coe_ne {z : ℂ} (hz : z ≠ 0) :
    invHomeomorph (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := invMap_coe_ne hz

/-- **The Möbius homeomorphism `z ↦ λ + z⁻¹` of the Riemann sphere**: it sends `∞` to the finite
point `λ`, the finite point `0` to `∞`, and `z ≠ 0` to `λ + z⁻¹`. -/
theorem mobiusAddInv (lam : ℂ) : ∃ Φ : RiemannSphere ≃ₜ RiemannSphere, Φ infty = (↑lam : RiemannSphere) ∧ Φ (↑(0 : ℂ)) = infty ∧ ∀ z : ℂ, z ≠ 0 → Φ (↑z : RiemannSphere) = ↑(lam + z⁻¹) := by
  refine ⟨invHomeomorph.trans (Homeomorph.onePointCongr (Homeomorph.addRight lam)), ?_, ?_, ?_⟩
  · simp [Homeomorph.trans_apply]
  · simp [Homeomorph.trans_apply]
  · intro z hz
    simp [Homeomorph.trans_apply, invHomeomorph_coe_ne hz, add_comm]

end

end Work.Smooth.SphereJordan
