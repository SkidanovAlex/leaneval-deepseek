import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
import Submission.Work.SmallBoxBridge.Resolve.sum_integral_inner_sq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the kinetic energy of a compactly supported smooth function

For `u : ℝ³ → ℝ` smooth with compact support, the kinetic energy integrand
`p ↦ ‖p‖² · ‖kinFT u p‖²` is integrable on `ℝ³` (with respect to Lebesgue measure).

The argument is the standard Schwartz-space one: `u` is (the real part of) a Schwartz
function `F`, its Fourier transform `𝓕 F` is Schwartz again, and `ξ ↦ ‖ξ‖²‖𝓕 F ξ‖²` is
integrable because it is a finite sum of the integrable functions
`ξ ↦ ⟨ξ, e_k⟩² ‖𝓕 F ξ‖²` (each of which is the squared norm of the Schwartz function
`ξ ↦ ⟨ξ, e_k⟩ • 𝓕 F ξ`, hence `L²`).  Finally the `p`-convention `kinFT` differs from
Mathlib's `𝓕` by the rescaling `p ↦ (2π)⁻¹ • p`, which preserves integrability.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform Topology BigOperators

namespace Work.SmallBoxTBWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `ξ ↦ ‖ξ‖² ‖𝓕 g ξ‖²` is integrable for a Schwartz function `g`. -/
lemma integrable_norm_sq_fourier_schwartz (g : SchwartzMap ℝ³ ℂ) :
    Integrable (fun ξ : ℝ³ => ‖ξ‖ ^ 2 * ‖(𝓕 g) ξ‖ ^ 2) := by
  have hk : ∀ k : Fin 3, Integrable (fun ξ : ℝ³ =>
      (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2 * ‖(𝓕 g) ξ‖ ^ 2) :=
    fun k => Work.SmallBoxBridge.Resolve.integrable_inner_sq_mul_norm_sq (𝓕 g)
      (Submission.BoseGases.kcStdBasis k)
  have hsum : Integrable (fun ξ : ℝ³ => ∑ k : Fin 3,
      (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2 * ‖(𝓕 g) ξ‖ ^ 2) :=
    integrable_finsetSum (Finset.univ) (fun k _ => hk k)
  refine hsum.congr (Filter.Eventually.of_forall (fun ξ => ?_))
  change (∑ k : Fin 3, (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
      * ‖(𝓕 g) ξ‖ ^ 2) = ‖ξ‖ ^ 2 * ‖(𝓕 g) ξ‖ ^ 2
  rw [← Finset.sum_mul, Work.SmallBoxBridge.Resolve.sum_inner_kcStdBasis_sq_local]

theorem integrable_kinFT_energy_cspt (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiff ℝ (⊤ : ENat) u) (hcs : HasCompactSupport u) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p‖ ^ 2)
      MeasureTheory.volume := by
  have hucs : HasCompactSupport (fun z : ℝ³ => (u z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have husm : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (u z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hu
  let F : SchwartzMap ℝ³ ℂ := hucs.toSchwartzMap husm
  have hF_coe : (F : ℝ³ → ℂ) = fun z => (u z : ℂ) := rfl
  have hIntξ : Integrable (fun ξ : ℝ³ => ‖ξ‖ ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    integrable_norm_sq_fourier_schwartz F
  have hInt2 : Integrable (fun p : ℝ³ => ‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
      ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) :=
    hIntξ.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  have hkft : ∀ p : ℝ³, Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p
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
  simp only [Pi.mul_apply, hkft p, hnorm p]

end Work.SmallBoxTBWord
