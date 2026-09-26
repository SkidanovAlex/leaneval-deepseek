import Submission.Work.Interpolation.adapter_decay
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.Thm31Adapter

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


/-!
# The Theorem 3.1 adapter, carrying the strip decay of the solution

`Work.FunctionalEquations.Thm31Adapter` shows that the hypotheses (1)--(5) of CKMRV
Theorem 3.1 for a pair of radial profiles `F, F̃ : ℍ → ℝ → ℂ` produce *some*
`Work.FE.FunctionalEquationSolution d`.  Here we record the same construction with the
witness pinned down: the solution it produces has `F`-component the radial lift
`(τ, x) ↦ F τ ‖x‖` (extended by `0` off the upper half plane) and likewise for `F̃`.

That gives the requested statement at once, since the decay hypotheses of
`Work.Interpolation.adapter_decay` are stated for exactly those extensions.

## Main results

* `Work.Interpolation.exists_solution_of_satisfiesThm31` : the pinned-down witness.
* `Work.Interpolation.adapter_decay` : the requested lemma.
-/

namespace Work.Interpolation

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap UpperHalfPlane Manifold

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The extension of a radial profile family to the upper half plane, evaluated at a point
`(τ, x)`, is `F τ ‖x‖` for `Im τ > 0` and `0` otherwise. -/
lemma extFun_eq (F : ℍ → ℝ → ℂ) :
    Work.FunctionalEquations.extFun (d := d) F
      = (fun τ x => if h : 0 < τ.im then F ⟨τ, h⟩ ‖x‖ else 0) := by
  funext τ x
  rw [Work.FunctionalEquations.extFun]
  by_cases h : 0 < τ.im
  · simp [dif_pos h, Work.FunctionalEquations.radialLift_apply]
  · simp [dif_neg h]

/-- **Pinned-down Theorem 3.1 adapter.**  The proof of `Work.FunctionalEquations.Thm31Adapter`
produces the solution whose components are the radial lifts of `F` and `F̃`. -/
theorem exists_solution_of_satisfiesThm31 {d k₀ : ℕ} [NeZero d] (hd : Even d)
    (F Ft : ℍ → ℝ → ℂ) (h : Work.Kernels.SatisfiesThm31 d k₀ F Ft)
    (hsF : ∀ τ : ℍ, ContDiff ℝ ∞ (F τ)) (hsFt : ∀ τ : ℍ, ContDiff ℝ ∞ (Ft τ))
    (heF : ∀ τ : ℍ, Function.Even (F τ)) (heFt : ∀ τ : ℍ, Function.Even (Ft τ)) :
    ∃ S : Work.FE.FunctionalEquationSolution d,
      S.F = (fun τ x => if h : 0 < τ.im then F ⟨τ, h⟩ ‖x‖ else 0) ∧
      S.Ftilde = (fun τ x => if h : 0 < τ.im then Ft ⟨τ, h⟩ ‖x‖ else 0) := by
  rcases h with ⟨hhol1, hhol2, hgrowth1, hgrowth2, hunif, hrec1, hrec2, hfe⟩
  refine ⟨⟨Work.FunctionalEquations.extFun F, Work.FunctionalEquations.extFun Ft,
    fun x => Work.FunctionalEquations.differentiableOn_extFun F hhol1 x,
    fun x => Work.FunctionalEquations.differentiableOn_extFun Ft hhol2 x,
    fun τ => Work.FunctionalEquations.contDiff_extFun F hsF heF τ,
    fun τ => Work.FunctionalEquations.contDiff_extFun Ft hsFt heFt τ,
    fun τ => Work.FunctionalEquations.radial_extFun F τ,
    fun τ => Work.FunctionalEquations.radial_extFun Ft τ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, extFun_eq F, extFun_eq Ft⟩
  · intro k ℓ
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hb⟩ := hgrowth1 k ℓ
    refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
    intro τ x hτ
    rw [Work.FunctionalEquations.radialDeriv_extFun F heF hτ ℓ x]
    simpa using hb ⟨τ, hτ⟩ ‖x‖
  · intro k ℓ
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hb⟩ := hgrowth2 k ℓ
    refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
    intro τ x hτ
    rw [Work.FunctionalEquations.radialDeriv_extFun Ft heFt hτ ℓ x]
    simpa using hb ⟨τ, hτ⟩ ‖x‖
  · obtain ⟨α, β, hα, hβ, hb⟩ := hunif
    refine ⟨α, β, hα, hβ, fun τ x hτ h1 h2 => ?_⟩
    rw [Work.FunctionalEquations.extFun_of_pos (F := F) (τ := τ) hτ,
        Work.FunctionalEquations.radialLift_apply]
    calc ‖F ⟨τ, hτ⟩ ‖x‖‖ ≤ max ‖F ⟨τ, hτ⟩ ‖x‖‖ ‖Ft ⟨τ, hτ⟩ ‖x‖‖ := le_max_left _ _
      _ ≤ α * ((⟨τ, hτ⟩ : ℍ).im) ^ (-β) := hb ⟨τ, hτ⟩ ‖x‖
            (by rw [UpperHalfPlane.mk_re]; exact h1) (by rw [UpperHalfPlane.mk_re]; exact h2)
      _ = α * τ.im ^ (-β) := by rw [UpperHalfPlane.mk_im]
  · obtain ⟨α, β, hα, hβ, hb⟩ := hunif
    refine ⟨α, β, hα, hβ, fun τ x hτ h1 h2 => ?_⟩
    rw [Work.FunctionalEquations.extFun_of_pos (F := Ft) (τ := τ) hτ,
        Work.FunctionalEquations.radialLift_apply]
    calc ‖Ft ⟨τ, hτ⟩ ‖x‖‖ ≤ max ‖F ⟨τ, hτ⟩ ‖x‖‖ ‖Ft ⟨τ, hτ⟩ ‖x‖‖ := le_max_right _ _
      _ ≤ α * ((⟨τ, hτ⟩ : ℍ).im) ^ (-β) := hb ⟨τ, hτ⟩ ‖x‖
            (by rw [UpperHalfPlane.mk_re]; exact h1) (by rw [UpperHalfPlane.mk_re]; exact h2)
      _ = α * τ.im ^ (-β) := by rw [UpperHalfPlane.mk_im]
  · intro τ x hτ
    have hτ2 : 0 < (τ + 2).im := by simpa using hτ
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    rw [Work.FunctionalEquations.extFun_of_pos (F := F) (τ := τ + 2) hτ2,
        Work.FunctionalEquations.extFun_of_pos (F := F) (τ := τ + 1) hτ1,
        Work.FunctionalEquations.extFun_of_pos (F := F) (τ := τ) hτ]
    simp only [Work.FunctionalEquations.radialLift_apply]
    have hv2 : ((2 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 2, hτ2⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    have hv1 : ((1 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 1, hτ1⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    rw [← hv2, ← hv1]
    exact hrec1 ⟨τ, hτ⟩ ‖x‖
  · intro τ x hτ
    have hτ2 : 0 < (τ + 2).im := by simpa using hτ
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    rw [Work.FunctionalEquations.extFun_of_pos (F := Ft) (τ := τ + 2) hτ2,
        Work.FunctionalEquations.extFun_of_pos (F := Ft) (τ := τ + 1) hτ1,
        Work.FunctionalEquations.extFun_of_pos (F := Ft) (τ := τ) hτ]
    simp only [Work.FunctionalEquations.radialLift_apply]
    have hv2 : ((2 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 2, hτ2⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    have hv1 : ((1 : ℝ) +ᵥ (⟨τ, hτ⟩ : ℍ)) = (⟨τ + 1, hτ1⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_mk,
          UpperHalfPlane.coe_mk]
      push_cast; ring
    rw [← hv2, ← hv1]
    exact hrec2 ⟨τ, hτ⟩ ‖x‖
  · intro τ x hτ
    have hS : ((ModularGroup.S • (⟨τ, hτ⟩ : ℍ) : ℍ) : ℂ) = -1 / τ := by
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk,
          inv_neg, div_eq_mul_inv, neg_one_mul]
    have hneg : 0 < (-1 / τ).im := by rw [← hS]; exact UpperHalfPlane.im_pos _
    have hSe : (⟨-1 / τ, hneg⟩ : ℍ) = ModularGroup.S • (⟨τ, hτ⟩ : ℍ) := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_mk]; exact hS.symm
    rw [Work.FunctionalEquations.extFun_of_pos (F := F) (τ := τ) hτ,
        Work.FunctionalEquations.extFun_of_pos (F := Ft) (τ := -1 / τ) hneg,
        Work.FunctionalEquations.radialLift_apply,
        Work.FunctionalEquations.radialLift_apply]
    have hslash : Work.FE.slashFactor d τ = (Complex.I / (((⟨τ, hτ⟩ : ℍ)) : ℂ)) ^ (d / 2) := by
      rw [Work.FunctionalEquations.slashFactor_eq_of_even (d := d) hd τ, UpperHalfPlane.coe_mk]
    have hgauss : Work.Core.gaussianFun d τ x = Work.Kernels.gaussTerm ⟨τ, hτ⟩ ‖x‖ := by
      simp only [Work.Core.gaussianFun, Work.Kernels.gaussTerm, Complex.ofReal_pow]
    rw [hslash, hSe, hgauss]
    exact hfe ⟨τ, hτ⟩ ‖x‖

/-- **Requested lemma.**  A pair of radial profiles satisfying the hypotheses of Theorem 3.1
and whose radial lifts decay in the strip extends to a `FunctionalEquationSolution` *with
those very components*, and the decay is inherited. -/
theorem adapter_decay {d k₀ : ℕ} [NeZero d] {c : ℝ} (hd : Even d)
    (F Ft : ℍ → ℝ → ℂ) (h : Work.Kernels.SatisfiesThm31 d k₀ F Ft)
    (hsF : ∀ τ : ℍ, ContDiff ℝ ∞ (F τ)) (hsFt : ∀ τ : ℍ, ContDiff ℝ ∞ (Ft τ))
    (heF : ∀ τ : ℍ, Function.Even (F τ)) (heFt : ∀ τ : ℍ, Function.Even (Ft τ))
    (hdecF : Work.FE.TendsToZeroInStrip d c
      (fun τ x => if h : 0 < τ.im then F ⟨τ, h⟩ ‖x‖ else 0))
    (hdecFt : Work.FE.TendsToZeroInStrip d c
      (fun τ x => if h : 0 < τ.im then Ft ⟨τ, h⟩ ‖x‖ else 0)) :
    ∃ S : Work.FE.FunctionalEquationSolution d,
      S.F = (fun τ x => if h : 0 < τ.im then F ⟨τ, h⟩ ‖x‖ else 0) ∧
      S.Ftilde = (fun τ x => if h : 0 < τ.im then Ft ⟨τ, h⟩ ‖x‖ else 0) ∧
      Work.FE.TendsToZeroInStrip d c S.F ∧ Work.FE.TendsToZeroInStrip d c S.Ftilde := by
  obtain ⟨S, hSF, hSFt⟩ := exists_solution_of_satisfiesThm31 (d := d) (k₀ := k₀) hd F Ft h
    hsF hsFt heF heFt
  exact ⟨S, hSF, hSFt, hSF.symm ▸ hdecF, hSFt.symm ▸ hdecFt⟩

end

end Work.Interpolation


end Work.CKFinal.Shadow
