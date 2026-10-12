import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.LatFourierDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators

/-- For a weight `W` vanishing outside the ball of radius `R` and any `z` with `‖z‖ ≤ √3·ℓ`,
the periodisation `latPer ℓ W z` is the *finite* sum over the lattice points in `latFinSet ℓ R`.

This is `LatFourier.latPer_eq_sum_finset` with the hypothesis `z ∈ latBox ℓ` replaced by the
weaker norm bound `‖z‖ ≤ √3·ℓ`: the only place where the cube was used in that proof is the
estimate `‖z‖ ≤ √3·ℓ` (via `latBox_subset_closedBall`), together with the fact that the sum is
over the lattice points `m` with `‖ℓ • latVec m‖ - ‖z‖ ≤ R`, which is implied by
`‖latVec m‖ ≤ (R + √3 ℓ)/ℓ`. -/
lemma latPer_eq_sum_finset_of_norm_le {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWs : ∀ x, R < ‖x‖ → W x = 0) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ‖z‖ ≤ Real.sqrt 3 * ℓ) :
    LatFourier.latPer ℓ W z
      = ∑ m ∈ LatFourier.latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ) := by
  rw [LatFourier.latPer]
  refine tsum_eq_sum (s := LatFourier.latFinSet ℓ R) (fun m hm => ?_)
  have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
    rw [← not_le]
    intro hc
    exact hm ((LatFourier.mem_latFinSet).mpr hc)
  have h5 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := LatFourier.latVec_norm_smul ℓ hℓ.le m
  have hgt : R < ‖z + ℓ • latVec m‖ := by
    have h2 : ‖ℓ • latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      calc ‖ℓ • latVec m‖ = ‖(z + ℓ • latVec m) - z‖ := by
            congr 1; abel
        _ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := norm_sub_le _ _
    have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hnot
      linarith [hnot]
    linarith
  simp [hWs _ hgt]

theorem latPer_bdd_of_norm_le {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ Real.sqrt 3 * ℓ →
      ‖Work.BoseBoxFock.LatFourier.latPer ℓ W z‖ ≤ D := by
  obtain ⟨C, hC⟩ := hWb
  refine ⟨(LatFourier.latFinSet ℓ R).card * max C 0, by positivity, fun z hz => ?_⟩
  rw [latPer_eq_sum_finset_of_norm_le hℓ hWs hz]
  calc ‖∑ m ∈ LatFourier.latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ)‖
      ≤ ∑ m ∈ LatFourier.latFinSet ℓ R, ‖(W (z + ℓ • latVec m) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ LatFourier.latFinSet ℓ R, max C 0 := by
        refine Finset.sum_le_sum fun m _ => ?_
        have h := le_trans (hC (z + ℓ • latVec m)) (le_max_left C 0)
        simpa [RCLike.norm_ofReal, Real.norm_eq_abs] using h
    _ = (LatFourier.latFinSet ℓ R).card * max C 0 := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Work.BoseBoxFock
