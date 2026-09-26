/-
# The (vanishing) residue of the contour integrand at the removable coincidence

The residue theorem for the left rectangle needs, at the single singular point it keeps, the limit

  `(z - z₀) · kerForm ℓ d r τ z → 2πi · Res_{z=z₀}`.

At the *pole* `z₀ = poleℂ τ = τ - 1` this is `Work.Asymptotics.dlc_tendsto_residue` and the limit is
`kerExp r (poleℂ τ) / (2πi)`.  At the *removable coincidence* `z₀ = coincℂ τ = ST⁻¹τ` the residue
vanishes (`Work.LayerCont.hasResidue_Kfun_coinc`, CKMRV's `φ(TS) = 0`), so the limit is `0`:

* `Work.LayerCont.Coinc.tendsto_coinc_residue`.

The proof is the mirror of `dlc_tendsto_residue`: compose the residue statement on `ℍ` with
`Tendsto ofComplex (𝓝[≠] (coincℂ τ)) (𝓝[≠] ζ₀)`, then multiply by the (continuous) factor
`kerExp r z / i` and rewrite `kerForm`.
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.Defs

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.LayerCont.Coinc

open Work.Asymptotics

/-- **The residue limit of the contour integrand at the removable coincidence.**  The limit of
`(z - coincℂ τ) · kerForm ℓ d r τ z` as `z → coincℂ τ` (punctured) is `0`, because
`Res_{z = ST⁻¹τ} K^{(d)}(τ,z) = 0`. -/
theorem tendsto_coinc_residue (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (hne : Work.Residues.jprime τ ≠ 0) :
    Tendsto (fun z : ℂ => (z - coincℂ τ) * kerForm ℓ d r τ z)
      (nhdsWithin (coincℂ τ) {coincℂ τ}ᶜ) (nhds 0) := by
  set ζ₀ : UpperHalfPlane := ModularGroup.S • ((-1 : ℝ) +ᵥ τ) with hζ₀
  have hζ₀coe : (ζ₀ : ℂ) = coincℂ τ := by rw [hζ₀]; rfl
  have hres := Work.LayerCont.hasResidue_Kfun_coinc ℓ d hd τ hne
  have hz0im : 0 < (coincℂ τ).im := coincℂ_im_pos τ
  have hUmem : {z : ℂ | 0 < z.im} ∈ nhdsWithin (coincℂ τ) {coincℂ τ}ᶜ :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz0im)
  have hcont : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex z) (coincℂ τ) :=
    continuousOn_ofComplex_of_im_pos.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz0im)
  have hofc : Tendsto (fun z : ℂ => UpperHalfPlane.ofComplex z)
      (nhdsWithin (coincℂ τ) {coincℂ τ}ᶜ)
      (nhdsWithin ζ₀ {ζ₀}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun z : ℂ => UpperHalfPlane.ofComplex z)
          (nhds (coincℂ τ)) (nhds ζ₀) := by
        have h' := hcont.tendsto
        rwa [show UpperHalfPlane.ofComplex (coincℂ τ) = ζ₀ from ofComplex_coincℂ τ] at h'
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, hUmem] with z hz hzim
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro hcon
      refine hz ?_
      have h1 : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = coincℂ τ := by
        rw [hcon, hζ₀coe]
      rwa [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk] at h1
  have hcomp := hres.comp hofc
  have hcomp' : Tendsto (fun z : ℂ =>
      (z - coincℂ τ) * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z))
      (nhdsWithin (coincℂ τ) {coincℂ τ}ᶜ) (nhds 0) := by
    refine hcomp.congr' ?_
    filter_upwards [hUmem] with z hzim
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk, hζ₀coe]
  have hexp : Tendsto (fun z : ℂ => kerExp r z / Complex.I)
      (nhdsWithin (coincℂ τ) {coincℂ τ}ᶜ) (nhds (kerExp r (coincℂ τ) / Complex.I)) := by
    have hc : ContinuousAt (fun z : ℂ => kerExp r z / Complex.I) (coincℂ τ) := by
      simp only [kerExp]
      fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hcomp'.mul hexp
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards with z
  simp only [kerForm]
  ring

end Work.LayerCont.Coinc
