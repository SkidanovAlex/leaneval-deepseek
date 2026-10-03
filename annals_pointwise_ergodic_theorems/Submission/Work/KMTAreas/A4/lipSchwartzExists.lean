/-
# Existence of the smoothing Schwartz function of Proposition `lip`

Proposition `lip` of Krause--Mirek--Tao smooths the progression average
`m ↦ (N')⁻¹ ∑_{m' ∈ [N']} f(x + q m')` by a fixed Schwartz weight

`w(m) = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε (m - m'))`

whose *frequency support is contained in `[-1,1]`*: this is the only property of `ψ` that the
smoothing step uses (it makes the Poisson summation over the dual variable finite — see
`Work.KMTAreas.A4.lipPoissonVanish`), together with the normalisation `∫ ψ = 1`.

This file supplies the existence of such a `ψ`.  The construction is the standard one: take a
smooth bump `χ` which equals `1` at the origin and vanishes outside `(-1,1)`, and let `ψ` be its
*inverse* Fourier transform.  Then `𝓕 ψ = χ` by Fourier inversion, so

* `∫ y, ψ y = (𝓕 ψ) 0 = χ 0 = 1`, and
* `𝓕 ψ s = χ s = 0` whenever `|s| > 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

/-! ## A compactly supported smooth bump `χ` with `χ 0 = 1` and `χ = 0` off `(-1,1)` -/

/-- The bump function underlying the construction: a smooth function which is `1` on `[-1/2,1/2]`
and vanishes outside `(-1,1)`. -/
noncomputable def lipSchBump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

theorem lipSchBump_rIn : lipSchBump.rIn = 1/2 := rfl

theorem lipSchBump_rOut : lipSchBump.rOut = 1 := rfl

/-- The bump function of `lipSchBump`, viewed as a complex-valued function. -/
noncomputable def lipSchBumpFun : ℝ → ℂ := fun x => ((lipSchBump x : ℝ) : ℂ)

theorem lipSchBumpFun_hasCompactSupport : HasCompactSupport lipSchBumpFun :=
  lipSchBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)

theorem lipSchBumpFun_contDiff : ContDiff ℝ (⊤ : ℕ∞) lipSchBumpFun :=
  Complex.ofRealCLM.contDiff.comp lipSchBump.contDiff

/-- The bump function as a Schwartz function: it is complex-valued, smooth, compactly supported,
equals `1` at the origin and vanishes off `(-1,1)`. -/
noncomputable def lipSchChi : SchwartzMap ℝ ℂ :=
  lipSchBumpFun_hasCompactSupport.toSchwartzMap lipSchBumpFun_contDiff

theorem lipSchChi_apply (x : ℝ) : lipSchChi x = lipSchBumpFun x := rfl

theorem lipSchChi_zero : lipSchChi 0 = 1 := by
  rw [lipSchChi_apply]
  show ((lipSchBump 0 : ℝ) : ℂ) = 1
  have h0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) lipSchBump.rIn := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [lipSchBump_rIn]
  rw [ContDiffBump.one_of_mem_closedBall lipSchBump h0]
  norm_num

theorem lipSchChi_eq_zero (x : ℝ) (hx : 1 ≤ |x|) : lipSchChi x = 0 := by
  rw [lipSchChi_apply]
  show ((lipSchBump x : ℝ) : ℂ) = 0
  rw [ContDiffBump.zero_of_le_dist lipSchBump (x := x) (by
    rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, lipSchBump_rOut]; exact hx)]
  norm_num

/-! ## The inverse Fourier transform of `χ` -/

/-- The smoothing weight of Proposition `lip`: the inverse Fourier transform of the bump `χ`.  Its
Fourier transform is exactly `χ`, hence is supported in `[-1,1]`. -/
noncomputable def lipSchPsi : SchwartzMap ℝ ℂ := 𝓕⁻ lipSchChi

theorem lipSchPsi_fourier : 𝓕 lipSchPsi = lipSchChi :=
  FourierInvPair.fourier_fourierInv_eq lipSchChi

theorem lipSchPsi_integral : ∫ y : ℝ, (lipSchPsi : ℝ → ℂ) y = 1 := by
  have h : (𝓕 lipSchPsi) 0 = ∫ y : ℝ, (lipSchPsi : ℝ → ℂ) y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp
  rw [← h, lipSchPsi_fourier, lipSchChi_zero]

theorem lipSchPsi_fourier_eq_zero (s : ℝ) (hs : 1 < |s|) : schFT lipSchPsi s = 0 := by
  show (𝓕 lipSchPsi) s = 0
  rw [lipSchPsi_fourier]
  exact lipSchChi_eq_zero s (le_of_lt hs)

theorem lipSchwartzExists :
    ∃ ψ : Work.Analysis.InverseTheory.SchwartzR,
      (∫ y : ℝ, (ψ : ℝ → ℂ) y = 1) ∧ (∀ s : ℝ, 1 < |s| → Work.KMTAreas.A4.schFT ψ s = 0) :=
  ⟨lipSchPsi, lipSchPsi_integral, lipSchPsi_fourier_eq_zero⟩

end Work.KMTAreas.A4
