import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Gates
import Submission.Work.Fatou.Qreg.InjGeom

/-!
# PERT · `RBlock4`: holomorphy of the lifted return map `R̃_f = retOf Φm (Qm Ξ α) α`

The lifted return map of §4.2 is `R̃_f = Φ ∘ T_f ∘ Φ⁻¹` on the gate image `Φ '' Q`
(`Work.Pert.retOf`).  This file proves that it is **holomorphic on the image of the waist**
`Φm '' (Qm Ξ α ∩ Qp Ξ α)` — which is exactly what the assembly needs, since the two gates overlap
only on the waist and (because `Tt α '' Qp ξ α = Qm ξ α`) the deck translation of a waist point
lands back inside the lower gate.

The mathematical content is the inverse function theorem for a holomorphic injection with nowhere
vanishing derivative on an open set: at a point `z₀ = invOn Φ Q w` of the gate the chosen preimage
coincides, near `w`, with the local inverse `g` of `Φ` at `z₀` (which has a strict derivative
because `Φ` is *analytic* at `z₀`), so `retOf Φ Q α = Φ ∘ Tt α ∘ invOn Φ Q` is a composition of
differentiable maps near `w`.

* `differentiableAt_retOf` — the general pointwise statement (helper);
* `retOf_holo` — the requested statement, obtained from it plus `Work.Pert.Tt_mem_Qm_iff`.
-/

namespace Work.Pert.RBlock4

open Complex Set Filter

open scoped Topology

noncomputable section

/-- **Pointwise holomorphy of the lifted return map.**  If `Φ` is differentiable and injective on
the open set `Q`, if `deriv Φ` vanishes nowhere on `Q`, if `w = Φ z` for some `z ∈ Q`, and if `Φ` is
differentiable at the deck-translated point `Tt α (invOn Φ Q w)`, then `retOf Φ Q α` is
differentiable at `w`.

Indeed, `invOn Φ Q` agrees near `w` with the local inverse `g` of `Φ` at `z₀ = invOn Φ Q w`
(which exists by the inverse function theorem, `Φ` being analytic at `z₀`), and
`retOf Φ Q α = Φ ∘ Tt α ∘ invOn Φ Q`. -/
theorem differentiableAt_retOf {Φ : ℂ → ℂ} {Q : Set ℂ} {α w : ℂ}
    (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q)
    (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    (hw : ∃ z ∈ Q, Φ z = w)
    (hd : DifferentiableAt ℂ Φ (Tt α (invOn Φ Q w))) :
    DifferentiableAt ℂ (retOf Φ Q α) w := by
  have hzQ : invOn Φ Q w ∈ Q := invOn_mem hw
  have hΦz : Φ (invOn Φ Q w) = w := invOn_spec hw
  have hcne : deriv Φ (invOn Φ Q w) ≠ 0 := hder _ hzQ
  -- `Φ` is analytic (hence strictly differentiable) at the preimage `z₀ = invOn Φ Q w`
  have hstr : HasStrictDerivAt Φ (deriv Φ (invOn Φ Q w)) (invOn Φ Q w) :=
    (hΦ.analyticAt (hQ.mem_nhds hzQ)).hasStrictDerivAt
  -- `g`, the local inverse of `Φ` at `z₀`
  set g : ℂ → ℂ :=
    hstr.localInverse Φ (deriv Φ (invOn Φ Q w)) (invOn Φ Q w) hcne with hgdef
  -- `g` is a right inverse of `Φ` near `w`
  have hright : ∀ᶠ y in 𝓝 w, Φ (g y) = y := by
    have h := hstr.eventually_right_inverse hcne
    rw [← hgdef] at h
    rwa [hΦz] at h
  -- `g w = z₀`
  have hgw : g w = invOn Φ Q w := by
    have h := (hstr.eventually_left_inverse hcne).self_of_nhds
    rw [← hgdef] at h
    rwa [hΦz] at h
  -- `g` has a derivative at `w`, hence is continuous and differentiable there
  have hgd : HasDerivAt g (deriv Φ (invOn Φ Q w))⁻¹ (Φ (invOn Φ Q w)) :=
    HasStrictDerivAt.hasDerivAt (hstr.to_localInverse hcne)
  have hgcont : ContinuousAt g w := by
    have h := HasDerivAt.continuousAt hgd
    rwa [hΦz] at h
  -- hence `g` stays inside the open gate near `w`
  have hmem : ∀ᶠ y in 𝓝 w, g y ∈ Q := by
    have h : Tendsto g (𝓝 w) (𝓝 (g w)) := hgcont
    rw [hgw] at h
    exact h.eventually (hQ.mem_nhds hzQ)
  -- so the chosen preimage `invOn Φ Q` coincides with `g` near `w`
  have hev : invOn Φ Q =ᶠ[𝓝 w] g := by
    filter_upwards [hright, hmem] with y hy1 hy2
    exact invOn_eq hinj ⟨_, hy2, hy1⟩ hy2 hy1
  -- therefore `invOn Φ Q` is differentiable at `w`
  have hd_inv : DifferentiableAt ℂ (invOn Φ Q) w := by
    refine hev.differentiableAt_iff.mpr ?_
    have h := HasDerivAt.differentiableAt hgd
    rwa [hΦz] at h
  -- and the chain rule finishes
  have hTt : DifferentiableAt ℂ (fun y => Tt α (invOn Φ Q y)) w :=
    (differentiableAt_id.sub_const (1 / α : ℂ)).comp w hd_inv
  exact hd.comp w hTt

/-- The lower gate `Qm Ξ α` is open. -/
theorem isOpen_Qm (Ξ : ℝ) (α : ℂ) : IsOpen (Qm Ξ α) := by
  unfold Qm
  exact Work.Fatou.Qreg.isOpen_Qreg _ _

/-- **Holomorphy of the lifted return map on the image of the waist.**  On
`Φm '' (Qm Ξ α ∩ Qp Ξ α)` the chosen preimage `invOn Φm (Qm Ξ α) ·` lands in the waist, whose deck
translate `Tt α` lies in the lower gate (`Tt α '' Qp Ξ α = Qm Ξ α`, `Work.Pert.Tt_mem_Qm_iff`); so
`Φm ∘ Tt α ∘ invOn Φm (Qm Ξ α) ·` is holomorphic there by `differentiableAt_retOf`. -/
theorem retOf_holo {Φm : ℂ → ℂ} {Ξ : ℝ} {α : ℂ}
    (hΦm : DifferentiableOn ℂ Φm (Work.Pert.Qm Ξ α))
    (hinj : Set.InjOn Φm (Work.Pert.Qm Ξ α))
    (hder : ∀ z ∈ Work.Pert.Qm Ξ α, deriv Φm z ≠ 0) :
    DifferentiableOn ℂ (Work.Pert.retOf Φm (Work.Pert.Qm Ξ α) α)
      (Φm '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hzM : z ∈ Qm Ξ α := hz.1
  have hzP : z ∈ Qp Ξ α := hz.2
  have hex : ∃ ζ ∈ Qm Ξ α, Φm ζ = Φm z := ⟨z, hzM, rfl⟩
  have hd : DifferentiableAt ℂ Φm (Tt α (invOn Φm (Qm Ξ α) (Φm z))) := by
    rw [invOn_eq hinj hex hzM rfl]
    exact hΦm.differentiableAt ((isOpen_Qm Ξ α).mem_nhds (Tt_mem_Qm_iff.mpr hzP))
  exact (differentiableAt_retOf (isOpen_Qm Ξ α) hΦm hinj hder hex hd).differentiableWithinAt

end

end Work.Pert.RBlock4
