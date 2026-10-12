import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.SqrtKinDefs
import Submission.Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `p ↦ ‖p‖²‖kinFT g p‖²` for smooth compactly supported `g`

`Submission.BoseGases.kinFT g p = ∫_y e^{−i⟪p,y⟫}g y dy` is Mathlib's Fourier transform at the
rescaled frequency `(2π)⁻¹ • p` (`kinFT_eq_fourier`), so for smooth compactly supported `g` the
function `p ↦ ‖p‖²‖kinFT g p‖²` is, up to the change of variables `p ↦ (2π)⁻¹ • p` and the constant
`(2π)²`, the function `ξ ↦ ‖ξ‖²‖𝓕 g ξ‖²`, which is integrable because `𝓕 g` is Schwartz: the
weight `‖ξ‖²` is the sum `Σ_k ⟪ξ, e_k⟫²` over an orthonormal basis, and each summand times
`‖𝓕 g ξ‖²` is the squared norm of the Schwartz function `ξ ↦ ⟪ξ, e_k⟫ • 𝓕 g ξ`.

The Schwartz-map part is `Work.SmallBoxTBWord.integrable_norm_sq_fourier_schwartz` (proved for
complex-valued Schwartz functions, hence applicable verbatim to the complex `g` here).
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform Topology BigOperators

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem kinFT_weight2_integrable {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  let F : SchwartzMap ℝ³ ℂ := hgc.toSchwartzMap hg
  have hF_coe : (F : ℝ³ → ℂ) = g := rfl
  have hIntξ : Integrable (fun ξ : ℝ³ => ‖ξ‖ ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_norm_sq_fourier_schwartz F
  have hInt2 : Integrable (fun p : ℝ³ => ‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
      ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) :=
    hIntξ.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  have hkft : ∀ p : ℝ³, Submission.BoseGases.kinFT g p
      = (𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p) := by
    intro p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hF_coe,
      ← SchwartzMap.fourier_coe F]
  have hnorm : ∀ p : ℝ³, ‖p‖ ^ 2 * ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2
      = (2 * Real.pi) ^ 2 * (‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
          ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) := by
    intro p
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    field_simp
  refine (hInt2.const_mul ((2 * Real.pi) ^ 2)).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [hkft p, hnorm p]

end Work.BoseBoxFock.SqrtKin
