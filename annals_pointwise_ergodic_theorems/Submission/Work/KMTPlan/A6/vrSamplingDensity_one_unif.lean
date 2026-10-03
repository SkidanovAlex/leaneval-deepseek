import Mathlib
import Submission.Work.KMTAreas.A7Hi.vrSamplingDensity_one

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-- **The uniform-in-`β` decimated sampling density comparison at the endpoint exponent `p = 1`.**

This is the *uniform* form of `Work.KMTAreas.A7Hi.vrSamplingDensity_one`: there is one constant `C`
depending only on `r`, that works for every band width `β ∈ (0, 1/2)`.  The point is that the
amplitude-form sampling comparison `Work.KMTAreas.A7Hi.vrsdSamplesLeIntegral_one` has a constant
independent of `β` (its sampling kernel is the *fixed* kernel of `Work.KMTAreas.A7Rep`, normalised
at the Nyquist rate `1/4`), and that the passage from the amplitude form to the decimated form uses
`β` only through the hypothesis `β q ≤ 1/4`. -/
theorem vrSamplingDensity_one_unif (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ), 0 < β → β < 1 / 2 → ∀ (F : ℕ → ℝ → ℂ)
      (hF : ∀ n : ℕ, Work.KMTAreas.A7Rep.HasRealFreqSupport (F n) (Set.Icc (-β) β))
      (q : ℕ) (hq : 0 < q) (hβq : β * (q : ℝ) ≤ 1 / 4) (a : ℤ),
      (∑' t : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * (t : ℝ))))
        ≤ ENNReal.ofReal C * (q : ENNReal)⁻¹ * ∫⁻ x : ℝ,
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.KMTAreas.A7Hi.vrsdSamplesLeIntegral_one r hr
  refine ⟨C₁, hC₁pos, ?_⟩
  intro β hβ hβ' F hF q hq hβq a
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [Work.KMTAreas.A7Rep.HasRealFreqSupport] at hF
  choose g hgint hgsupp hgF using hF
  set W : ℕ → ℝ → ℂ := fun n => Work.KMTAreas.A7Hi.rescAmp (q : ℝ) (a : ℝ) (g n) with hW
  have hWint : ∀ n : ℕ, MeasureTheory.Integrable (W n) := by
    intro n
    simp only [hW]
    exact Work.KMTAreas.A7Hi.integrable_rescAmp (hgint n) hqR
  have hWsupp : ∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → W n ξ = 0 := by
    intro n ξ hξ
    simp only [hW]
    exact Work.KMTAreas.A7Hi.rescAmp_eq_zero (hgsupp n) hqR hβq hξ
  have hWfourier : ∀ (n : ℕ) (u : ℝ),
      FourierTransformInv.fourierInv (W n) u = F n ((a : ℝ) + (q : ℝ) * u) := by
    intro n u
    simp only [hW]
    rw [Work.KMTAreas.A7Hi.fourierInv_rescAmp (g n) hqR u]
    exact (hgF n ((a : ℝ) + (q : ℝ) * u)).symm
  have hA : ∀ x : ℝ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * x)) := by
    intro x
    congr 1
    funext n
    exact hWfourier n x
  have hsample : ∀ t : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * (t : ℝ)))
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) ((t : ℤ) : ℝ)) :=
    fun t => (hA ((t : ℤ) : ℝ)).symm
  have hsub := Work.KMTAreas.A7Hi.lintegral_comp_add_mul
    (fun x : ℝ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x))
    ((a : ℤ) : ℝ) hqR
  calc (∑' t : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * (t : ℝ))))
      = ∑' t : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) ((t : ℤ) : ℝ)) :=
        tsum_congr hsample
    _ ≤ ENNReal.ofReal C₁ * ∫⁻ x : ℝ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) x) := hC₁ W hWint hWsupp
    _ = ENNReal.ofReal C₁ * ((ENNReal.ofReal ((q : ℕ) : ℝ))⁻¹ * ∫⁻ x : ℝ,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x)) := by
        congr 1
        rw [← hsub]
        apply lintegral_congr
        intro x
        rw [hA x]
    _ = ENNReal.ofReal C₁ * (q : ENNReal)⁻¹ * ∫⁻ x : ℝ,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x) := by
        rw [ENNReal.ofReal_natCast, mul_assoc]

end

end Work.KMTPlan.A6
