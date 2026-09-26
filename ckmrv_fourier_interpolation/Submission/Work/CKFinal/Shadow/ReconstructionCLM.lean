import Submission.Work.FunctionalEquations.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (SeminormGrowthOfRadialGrowth)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (coeffs_seminorm_decay_family)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (summable_sampleWeight_inv_sq)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-! ### The reconstruction series -/

/-- **The reconstruction series converges and is bounded by finitely many Schwartz
seminorms.**  This is the analytic content of the continuity of the reconstruction
functional. -/
theorem reconstruction_bound {n : ℕ} [NeZero n] (S : InterpolationSolution n) (x₀ : E n) :
    ∃ s : Finset (ℕ × ℕ), ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : 𝓢(E n, ℂ),
        Summable (fun i : SampleIdx 1 => coeffs n 1 f i * (S.basis i).1 x₀) ∧
        ‖∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀‖
          ≤ K * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
  classical
  obtain ⟨Cb, Nb, hCb, hb⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  obtain ⟨s, Cc, hCc, hdecay⟩ := coeffs_seminorm_decay_family n (Nb + 2)
  have hSigmann : 0 ≤ ∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2) :=
    tsum_nonneg (fun i => by positivity)
  refine ⟨s, Cc * Cb * (∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2)),
    mul_nonneg (mul_nonneg hCc hCb) hSigmann, fun f => ?_⟩
  set Sf : ℝ := (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f with hSf
  have hSf0 : 0 ≤ Sf := by rw [hSf]; exact apply_nonneg _ _
  have hbound : ∀ i : SampleIdx 1,
      ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖
        ≤ (Cc * Cb * Sf) * (1 / (((i.1.1 : ℝ) + 1) ^ 2)) := by
    intro i
    set D : ℝ := (i.1.1 : ℝ) + 1 with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hDpow : 0 < D ^ Nb := pow_pos hDpos _
    have h1 : D ^ (Nb + 2) * ‖coeffs n 1 f i‖ ≤ Cc * Sf := by
      rw [hD, hSf]; exact hdecay f i
    have h2 : ‖(S.basis i).1 x₀‖ ≤ Cb * D ^ Nb := by
      refine le_trans (SchwartzMap.norm_le_seminorm ℂ (S.basis i).1 x₀) ?_
      rw [hD]
      exact hb i.1 i.2
    have h3 : D ^ (Nb + 2) * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖)
        ≤ (Cc * Sf) * (Cb * D ^ Nb) := by
      calc D ^ (Nb + 2) * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖)
          = (D ^ (Nb + 2) * ‖coeffs n 1 f i‖) * ‖(S.basis i).1 x₀‖ := by ring
        _ ≤ (Cc * Sf) * ‖(S.basis i).1 x₀‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ (Cc * Sf) * (Cb * D ^ Nb) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : D ^ Nb * (D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖))
        ≤ D ^ Nb * (Cc * Cb * Sf) := by
      calc D ^ Nb * (D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖))
          = D ^ (Nb + 2) * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) := by
            rw [pow_add]; ring
        _ ≤ (Cc * Sf) * (Cb * D ^ Nb) := h3
        _ = D ^ Nb * (Cc * Cb * Sf) := by ring
    have h5 : D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) ≤ Cc * Cb * Sf :=
      (mul_le_mul_iff_of_pos_left hDpow).mp h4
    have h6 : ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖ ≤ (Cc * Cb * Sf) * (1 / D ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < D ^ 2)]
      calc (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) * D ^ 2
          = D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) := by ring
        _ ≤ Cc * Cb * Sf := h5
    rwa [hD] at h6
  have hsum_norm : Summable (fun i : SampleIdx 1 => ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
      (summable_sampleWeight_inv_sq.mul_left (Cc * Cb * Sf))
  have hsum_f : Summable (fun i : SampleIdx 1 => coeffs n 1 f i * (S.basis i).1 x₀) :=
    Summable.of_norm_bounded hsum_norm (fun i => le_of_eq (norm_mul _ _))
  refine ⟨hsum_f, ?_⟩
  calc ‖∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀‖
      ≤ ∑' i : SampleIdx 1, ‖coeffs n 1 f i * (S.basis i).1 x₀‖ :=
        norm_tsum_le_tsum_norm hsum_f.norm
    _ = ∑' i : SampleIdx 1, ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖ :=
        tsum_congr (fun i => norm_mul _ _)
    _ ≤ ∑' i : SampleIdx 1, (Cc * Cb * Sf) * (1 / (((i.1.1 : ℝ) + 1) ^ 2)) :=
        Summable.tsum_le_tsum hbound hsum_norm
          (summable_sampleWeight_inv_sq.mul_left (Cc * Cb * Sf))
    _ = (Cc * Cb * Sf) * ∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2) := tsum_mul_left
    _ = (Cc * Cb * (∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2)))
          * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by rw [hSf]; ring

/-- **The reconstruction functional is continuous.**  For a solution `S` of the functional
equations and a point `x₀`, the map `f ↦ ∑ i, (coeffs n 1 f i) * (basis i) x₀ - f x₀` is a
continuous linear functional on the complex Schwartz space. -/
theorem ReconstructionCLM {n : ℕ} [NeZero n] (S : InterpolationSolution n) (x₀ : E n) :
    ∃ Λ : 𝓢(E n, ℂ) →L[ℂ] ℂ, ∀ f : 𝓢(E n, ℂ),
      Λ f = (∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀) - f x₀ := by
  classical
  obtain ⟨C, hC⟩ := Work.Sampling.coeffs_continuous_linear n 1
  obtain ⟨s, K, hK, hb⟩ := reconstruction_bound S x₀
  have hcoeffs_add : ∀ f g : 𝓢(E n, ℂ),
      coeffs n 1 (f + g) = coeffs n 1 f + coeffs n 1 g := by
    intro f g; rw [← hC (f + g), ← hC f, ← hC g, map_add]
  have hcoeffs_smul : ∀ (a : ℂ) (f : 𝓢(E n, ℂ)),
      coeffs n 1 (a • f) = a • coeffs n 1 f := by
    intro a f; rw [← hC (a • f), ← hC f, map_smul]
  have hadd : ∀ f g : 𝓢(E n, ℂ),
      (∑' i : SampleIdx 1, coeffs n 1 (f + g) i * (S.basis i).1 x₀)
        = (∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀)
          + (∑' i : SampleIdx 1, coeffs n 1 g i * (S.basis i).1 x₀) := by
    intro f g
    rw [hcoeffs_add f g]
    simp only [Pi.add_apply, add_mul]
    exact Summable.tsum_add (hb f).1 (hb g).1
  have hsmul : ∀ (a : ℂ) (f : 𝓢(E n, ℂ)),
      (∑' i : SampleIdx 1, coeffs n 1 (a • f) i * (S.basis i).1 x₀)
        = a • (∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀) := by
    intro a f
    have hcf : ∀ i, coeffs n 1 (a • f) i = a * coeffs n 1 f i := by
      intro i
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun (hcoeffs_smul a f) i
    simp only [hcf, mul_assoc]
    rw [tsum_mul_left, smul_eq_mul]
  have hbnd : ∃ s' : Finset (ℕ × ℕ), ∃ C' : ℝ, 0 ≤ C' ∧ ∀ f : 𝓢(E n, ℂ),
      ‖∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀‖
        ≤ C' * s'.sup (schwartzSeminormFamily ℂ (E n) ℂ) f :=
    ⟨s, K, hK, fun f => (hb f).2⟩
  let A : 𝓢(E n, ℂ) →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (𝕜' := ℂ) (D := E n) (E := ℂ) (G := ℂ)
      (σ := RingHom.id ℂ)
      (fun f => ∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀) hadd hsmul hbnd
  refine ⟨A - Work.Sampling.evalAtCLM x₀, fun f => ?_⟩
  rw [sub_apply, Work.Sampling.evalAtCLM_apply]
  rfl

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
