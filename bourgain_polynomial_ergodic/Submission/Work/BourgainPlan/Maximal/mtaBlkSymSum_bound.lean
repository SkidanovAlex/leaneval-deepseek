import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs

namespace Work.BourgainPlan.Maximal

/-- The bump `dyadTheta` is bounded. -/
lemma dyadTheta_abs_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ η : ℝ, |dyadTheta η| ≤ B :=
  exists_bound_of_continuous_hasCompactSupport dyadTheta_spec.1.continuous
    dyadTheta_spec.2.1

/--
The partial sum of the block symbols `mtaBlkSym`, over the lacunary window `|s| ≤ S`, is bounded
uniformly in the number of terms `K`, the frequency `ξ`, the dyadic signs `ε` and the window width
`S`.

This is the telescoping identity `mtaBlkSymSum_eq` combined with the boundedness of the bump `θ`
(`dyadTheta_abs_bound`) and the summability `∑_k ‖μ_k(ξ)‖ ≤ C` of the dyadic increments
(`sum_norm_muSym_le`).
-/
theorem mtaBlkSymSum_bound (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (S : ℕ) (ξ : ℝ),
      ‖Work.BourgainPlan.Maximal.mtaBlkSymSum P K ε S ξ‖ ≤ C := by
  obtain ⟨Cm, hCmpos, hCm⟩ := sum_norm_muSym_le P hdeg hlc
  obtain ⟨D, hDnonneg, hD⟩ := dyadTheta_abs_bound
  refine ⟨Cm * (2 * D + 1), ?_, ?_⟩
  · have : (0:ℝ) < 2 * D + 1 := by positivity
    exact mul_pos hCmpos this
  intro K ε hε S ξ
  rw [mtaBlkSymSum_eq]
  have hterm : ∀ k ∈ Finset.range K,
      ‖ε k * muSym P k ξ *
        (((dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
          - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) : ℝ) : ℂ))‖
      ≤ ‖muSym P k ξ‖ * (2 * D + 1) := by
    intro k _
    have hz : ‖(((dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
          - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) : ℝ) : ℂ))‖
        ≤ 2 * D + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := abs_sub (dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ))
        (dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ))
      have h1 := hD ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
      have h2 := hD ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ)
      linarith
    calc ‖ε k * muSym P k ξ *
          (((dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
            - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) : ℝ) : ℂ))‖
        = (‖ε k‖ * ‖muSym P k ξ‖) *
          ‖(((dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
            - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) : ℝ) : ℂ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖muSym P k ξ‖ * (2 * D + 1) := by
          refine mul_le_mul ?_ hz (norm_nonneg _) (norm_nonneg _)
          have := mul_le_mul_of_nonneg_right (hε k) (norm_nonneg (muSym P k ξ))
          simpa using this
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hCm K ξ) (by positivity)

end Work.BourgainPlan.Maximal
