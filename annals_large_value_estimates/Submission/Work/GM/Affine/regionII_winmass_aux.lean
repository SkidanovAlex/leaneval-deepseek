import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.region_II_resonant
import Submission.Work.GM.Affine.region_II_resonant_high
import Submission.Work.GM.Affine.gSum_fourier

/-!
# Auxiliary facts shared by the region-II reductions (`L¹`-form and `supf`-form)

`hcs_of_SuppHyp`, `continuous_ghat_of_SuppHyp` and `WinMass_nonneg` live here so that both
`regionII_to_winmass.lean` (and hence anything importing it, e.g. `regionII_to_winmass_sup.lean`)
and the copies in this file's siblings can use them without a circular import.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The support hypothesis of §9 gives compact support. -/
lemma hcs_of_SuppHyp {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) : HasCompactSupport f := by
  refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc ?_
  intro x hx
  by_contra hf0
  exact hx (h x hf0)

/-- `ĝ` is continuous (from the explicit finite-sum expansion `gSum_fourier`). -/
lemma continuous_ghat_of_SuppHyp {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Continuous (fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ) := by
  have hsum : Continuous (fun ξ : ℝ =>
      ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂,
        (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) *
          ∑ m₃ ∈ R3ext K M₃,
            ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))) := by
    refine continuous_finsetSum _ (fun m₁ _ => continuous_finsetSum _ (fun m₂ _ => ?_))
    refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
    · exact (continuous_fhat hf hcs).comp (by fun_prop)
    · refine continuous_finsetSum _ (fun m₃ _ => ?_)
      exact Continuous.mul continuous_const (by unfold efun; fun_prop)
  exact hsum.congr (fun ξ => ((gSum_fourier hK hM₁ hM₂ hM₃ hf hcs).2 ξ).symm)

/-- `WinMass` is non-negative. -/
lemma WinMass_nonneg (f : ℝ → ℝ) (M₂ M₃ : ℝ) : 0 ≤ WinMass f M₂ M₃ := by
  rw [WinMass]
  exact tsum_nonneg (fun ℓ => integral_nonneg (fun τ => sq_nonneg _))

end

end Work.GM.Affine
