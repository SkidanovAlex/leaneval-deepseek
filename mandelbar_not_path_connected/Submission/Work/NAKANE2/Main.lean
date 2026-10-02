/-
# `Work.NAKANE2` — Nakane's local homeomorphism (R1)

The headline of the area: `Work.NAKANE2.phiLocalHomeo : Work.NAKANE.PhiLocalHomeo`, i.e.
`IsLocalHomeomorphOn Φ Mbᶜ`, proved by the inverse function theorem from

* (B1) `Work.NAKANE2.phi_hasStrictFDerivAt` — `Φ` is strictly `ℝ`-differentiable off the mandelbar
  (module `Submission.Work.NAKANE2.Far.phi_hasStrictFDerivAt`),
* (S) `Work.NAKANE2.lipschitzSection` — the Shishikura surgery section
  (module `Submission.Work.NAKANE2.Surgery.lipschitzSection`),
* (D1) `Work.NAKANE2.deriv_varphiCrit_self_ne_zero` (module
  `Submission.Work.NAKANE2.Deriv.deriv_varphiCrit_self_ne_zero`),
* (D2) `Work.NAKANE2.surjective_of_lipschitzSection` and `Work.NAKANE2.equivOfSurjective`
  (module `Submission.Work.NAKANE2.IFT.Basic`),
* (D3) `Work.NAKANE2.localHomeoAt_of_strict` (same module).

Together with NAKANE's assembly (`Work.NAKANE.nakaneHomeo_of_localHomeo`) this discharges the
single classical input of `Work.ParamRays.NakaneHomeo`.
-/
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.IFT.Basic
import Submission.Work.NAKANE2.Deriv.deriv_varphiCrit_self_ne_zero
import Submission.Work.NAKANE2.Surgery.lipschitzSection
import Submission.Work.NAKANE2.Far.phi_hasStrictFDerivAt
import Submission.Work.NAKANE.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.NAKANE2

/-- **(R1).**  The parameter Böttcher map `Φ c = φ_c(c)` of the tricorn family is a local
homeomorphism off the mandelbar.

Route: at `c₀ ∉ Mb` the map `Φ` is strictly `ℝ`-differentiable with derivative `L`
(`phi_hasStrictFDerivAt`); the surgery provides a Lipschitz section of the model map
`v ↦ φ_{c₀}(c₀ + v)`, whose derivative at `0` is multiplication by the nonvanishing number
`deriv (varphiCrit c₀) c₀` (`deriv_varphiCrit_self_ne_zero`), hence surjective.  By
`surjective_of_lipschitzSection` the derivative `L` is surjective, hence a
`ContinuousLinearEquiv`, and Mathlib's inverse function theorem
(`localHomeoAt_of_strict`) produces the required `OpenPartialHomeomorph`. -/
theorem phiLocalHomeo : Work.NAKANE.PhiLocalHomeo := by
  intro c₀ hc₀
  obtain ⟨L, hL⟩ := Far.phi_hasStrictFDerivAt hc₀
  obtain ⟨r, K, hr, hsec⟩ := Surgery.lipschitzSection hc₀
  -- the derivative of the model map `v ↦ φ_{c₀}(c₀ + v)` at `0`
  have hne : deriv (Work.Bottcher.varphiCrit c₀) c₀ ≠ 0 :=
    Deriv.deriv_varphiCrit_self_ne_zero hc₀
  set H : ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv (Work.Bottcher.varphiCrit c₀) c₀)).restrictScalars ℝ
    with hHdef
  have hmem : c₀ ∈ Work.ParamRays.critDomain c₀ := Work.ParamRays.self_mem_critDomain hc₀
  have hdiff : DifferentiableAt ℂ (Work.Bottcher.varphiCrit c₀) c₀ :=
    (Work.Bottcher.analyticOnNhd_varphiCrit c₀ c₀ hmem).differentiableAt
  have hL2 : HasFDerivAt (Work.Bottcher.varphiCrit c₀) H c₀ := by
    rw [hHdef]
    exact HasFDerivAt.restrictScalars ℝ hdiff.hasDerivAt.hasFDerivAt
  have hshift : HasFDerivAt (fun v : ℂ => c₀ + v) (1 : ℂ →L[ℝ] ℂ) (0 : ℂ) :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).const_add c₀
  set h : ℂ → ℂ := fun v => Work.Bottcher.varphiCrit c₀ (c₀ + v) with hh
  have hHfd : HasFDerivAt h H 0 := by
    have hL2' : HasFDerivAt (Work.Bottcher.varphiCrit c₀) H (c₀ + 0) := by
      rw [add_zero]; exact hL2
    have hh2 : HasFDerivAt (Work.Bottcher.varphiCrit c₀ ∘ (fun v : ℂ => c₀ + v))
        (H.comp (1 : ℂ →L[ℝ] ℂ)) 0 :=
      HasFDerivAt.comp (0 : ℂ) hL2' hshift
    have hcomp : H.comp (1 : ℂ →L[ℝ] ℂ) = H := by ext z; rfl
    rw [hcomp] at hh2
    simpa [h, Function.comp_def] using hh2
  have hHsurj : Function.Surjective H := by
    intro y
    refine ⟨y * (deriv (Work.Bottcher.varphiCrit c₀) c₀)⁻¹, ?_⟩
    have hval : H (y * (deriv (Work.Bottcher.varphiCrit c₀) c₀)⁻¹)
        = (y * (deriv (Work.Bottcher.varphiCrit c₀) c₀)⁻¹) *
            (deriv (Work.Bottcher.varphiCrit c₀) c₀) := by
      rw [hHdef]
      show (ContinuousLinearMap.toSpanSingleton ℂ (deriv (Work.Bottcher.varphiCrit c₀) c₀))
          (y * (deriv (Work.Bottcher.varphiCrit c₀) c₀)⁻¹)
        = (y * (deriv (Work.Bottcher.varphiCrit c₀) c₀)⁻¹) *
            (deriv (Work.Bottcher.varphiCrit c₀) c₀)
      rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hval, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have h0 : h 0 = Work.NAKANE2.Phi c₀ := by
    simp [h, Work.NAKANE2.Phi_eq_varphiCrit hc₀]
  have hsecc : ∀ v : ℂ, ‖v‖ < r →
      ∃ c : ℂ, Work.NAKANE2.Phi c = h v ∧ ‖c - c₀‖ ≤ K * ‖v‖ := by
    intro v hv
    obtain ⟨c, -, h1, h2⟩ := hsec v hv
    exact ⟨c, h1, h2⟩
  have hsurj : Function.Surjective L :=
    surjective_of_lipschitzSection hL.hasFDerivAt hHfd hHsurj hr h0 hsecc
  obtain ⟨e, hew⟩ := equivOfSurjective L hsurj
  have hstrict : HasStrictFDerivAt Work.NAKANE2.Phi (e : ℂ →L[ℝ] ℂ) c₀ := by
    rw [hew]
    exact hL
  exact localHomeoAt_of_strict hstrict

/-- **Nakane's homeomorphism theorem**, from (R1) alone: the parameter Böttcher map is a
homeomorphism of the exterior of the mandelbar onto the exterior unit disc. -/
theorem nakaneHomeo : Work.ParamRays.NakaneHomeo :=
  Work.NAKANE.nakaneHomeo_of_localHomeo phiLocalHomeo

end Work.NAKANE2
