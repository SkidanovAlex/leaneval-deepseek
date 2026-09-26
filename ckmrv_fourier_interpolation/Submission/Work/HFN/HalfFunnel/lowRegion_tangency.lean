/-
# The low-strip `r`-seminorm bound near the two tangency points `±1/2 + i/2`

The target of this file is `Work.Asymptotics.HalfFunnel.lowRegion_tangency`: the uniform bound
`|r|^k ‖∂_r^l (kernelTransform (Kfun ℓ d) τ ·) r‖ ≤ C` on the part of the low strip
`{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}` meeting the two balls of radius `1/8` about the tangency points
`±1/2 + i/2 ∈ ∂𝒟`.

## Architecture

The pole `z₁ = poleOne τ` of `z ↦ K(τ,z)` crosses the contour `{it}` at the tangency point, so
the pointwise kernel is *unbounded* on the region (`‖Kaxis(τ,it)‖ ≍ 1/‖z₁ - iℝ‖` near `t = 1`)
and neither `kernelTransform_seminorm_on_compact` nor the flatness decomposition of
`paperLayer` (with its cut at `t = 1`) applies.  The signed contour integral stays bounded, and
this is captured by cutting the contour at `t = 1/2` and `t = 3/2`, so that the pole lies in the
*interior* of the middle window:

  `tangPhi = ∫_0^{1/2} K + ∫_{1/2}^{3/2} K + ∫_{3/2}^∞ (K - Aexp) - ∫_1^{3/2} Aexp`

(`tangLayerDefs.lean`).  Each piece is estimated separately:

* `tangLow`, `tangTail`, `tangA`: from the flatness `tangKaxisFlatLow`, the cusp expansion
  `tangTailExpansion` and the explicit form of `Aexp`;
* `tangSpike`: from Cauchy's residue theorem on the rectangle `[0,1/4] × [1/2,3/2]`
  (`Work.Asymptotics.residue_rectangle_of_bdd`), whose only enclosed pole is `z₁`
  (`tangOrbitRectCl`, `tangPoleGeom`), whose residue is uniformly bounded and whose remainder is
  locally bounded (`tangPrincipalPart`), the three other edges being bounded (`tangEdgeBound`).

The pieces are reassembled with `exists_seminorm_bound_of_iteratedDeriv_bound_poly`, and the
resulting layer is transferred to `kernelTransform` by
`kernelTransform_seminorm_of_layer_on_compact` (whose flatness/tail inputs are used only at the
single point `τ`).
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRect
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeom
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRectCl
import Submission.Work.Asymptotics.DomainD
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.Asymptotics.Compact.local_agreement
import Submission.Work.HFN.HalfFunnel.tangLayerSeminorm
import Submission.Work.HFN.HalfFunnel.tangLayerEqLayer

set_option linter.unusedSimpArgs false

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-- **The low-strip `r`-seminorm bound near the two tangency points `±1/2 + i/2 ∈ ∂𝒟`.** -/
theorem lowRegion_tangency (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im → τ.im ≤ 2 →
      (‖(τ : ℂ) - ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Complex.I)‖ < 1 / 8 ∨
        ‖(τ : ℂ) - ((-(1 / 2) : ℝ) + (1 / 2 : ℝ) * Complex.I)‖ < 1 / 8) →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ C := by
  intro k l
  have hsemi : ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ ctanRegion →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => tangLayer ℓ d τ s) r‖ ≤ C :=
    tangLayerSeminorm ℓ d hd
  obtain ⟨C, hC, hb⟩ := Work.HFN.kernelTransform_seminorm_of_layer_on_compact
    ℓ d (tangLayer ℓ d)
    (by
      intro τ hτ
      have h1 : tangLayer ℓ d τ 0 = 0 := by rw [tangLayer]; simp
      have h2 : Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0 = 0 := by
        simp [Work.Kernels.kernelTransform]
      rw [h1, h2])
    (by
      intro τ hτ r hr hInt
      rw [tangLayerEqLayer ℓ d hd τ r hτ hr, Work.Asymptotics.layer, if_neg hr]
      have hsub : ({τ} : Set ℍ) ⊆ Work.Asymptotics.DomainD := by rintro x rfl; exact hτ.1
      have hcpt : IsCompact ({τ} : Set ℍ) := isCompact_singleton
      refine Work.Asymptotics.Compact.local_agreement (K := ({τ} : Set ℍ)) ℓ d hd
        (Work.Asymptotics.Gcusp ℓ d) (fun i j => Work.HFN.Gcusp_moderate ℓ d i j) ?_
        (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd hcpt hsub)
        (Work.HFN.cusp_expansion_of_kernel ℓ d hd hcpt hsub) τ r (by simp) hr hInt
      intro h8 j
      rw [Work.Asymptotics.Gcusp, if_pos h8]
      funext x
      fin_cases j <;> simp [Work.Asymptotics.Gcusp8])
    hsemi k l
  exact ⟨C, hC, fun τ r hD h1 h2 hball => hb τ r ⟨hD, h1, h2, hball⟩⟩

end

end Work.HFN.HalfFunnel
