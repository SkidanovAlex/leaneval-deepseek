import Mathlib
import Submission.Work.ThomBordism.LeadChapter.bdryAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.LeadChapter

open Work.ThomBordism.BCU

/-- The `ψ`-analogue of `Work.ThomBordism.bcuPhi_ne_zero`: the boundary collapse attached to an
arbitrary half-space chart `ψ` does not vanish away from the base point `y`. -/
theorem psiPhiNeZero (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    {y : W} (hyψ : y ∈ ψ.source)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ) {χ : W → ℝ}
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hout : ∀ z, z ∉ ψ.source → χ z = 0)
    {z : W} (hz : z ≠ y) : Work.ThomBordism.LeadChapter.psiPhi ψ y τ χ z ≠ 0 := by
  intro hcon
  by_cases hmem : z ∈ ψ.source
  · have hv0 : psiVa ψ y τ z ≠ 0 :=
      fun h0 => hz ((psiVa_eq_zero_iff ψ (ne_of_gt hτ) hyψ hmem).mp h0)
    have hv0' : 0 ≤ (psiVa ψ y τ z) 0 :=
      psiVa_coord_nonneg ψ hbd hyψ hy (le_of_lt hτ) hmem
    rw [psiPhi_apply] at hcon
    by_cases h1 : χ z ≤ 1 / 2
    · rw [BCU.profile2, if_pos h1] at hcon
      exact BCU.bcu_northPole_ne_zero n hcon
    · by_cases h2 : χ z ≤ 3 / 4
      · have hlt1 : 1 / 2 < χ z := lt_of_not_ge h1
        have hφ0 : 0 ≤ (3 / 4 - χ z) * 2 * Real.pi :=
          mul_nonneg (by linarith) (by positivity)
        have hφ1 : (3 / 4 - χ z) * 2 * Real.pi ≤ Real.pi / 2 := by
          have h4 : (3 / 4 - χ z) * 2 ≤ 1 / 2 := by linarith
          nlinarith [Real.pi_pos]
        have hcos : 0 ≤ Real.cos ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
        have hsin : 0 ≤ Real.sin ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.sin_nonneg_of_mem_Icc ⟨hφ0, by linarith [Real.pi_pos]⟩
        rw [BCU.profile2, if_neg h1, if_pos h2] at hcon
        have hnorm := BCU.bcu_sphPhase_norm_eq_one ((3 / 4 - χ z) * 2 * Real.pi)
          (psiVa ψ y τ z) hv0 hcos hsin hv0'
        rw [hcon] at hnorm
        simp at hnorm
      · have hlt : 3 / 4 < χ z := lt_of_not_ge h2
        have hp0 : 0 ≤ (1 - χ z) * 4 := mul_nonneg (by linarith [(hχ01 z).2]) (by norm_num)
        have hp1 : (1 - χ z) * 4 ≤ 1 := by linarith [(hχ01 z).2]
        have hcoef : 0 < (1 - χ z) * 4 / ‖psiVa ψ y τ z‖ + (1 - (1 - χ z) * 4) := by
          rcases eq_or_lt_of_le hp0 with hp | hp
          · rw [← hp]; simp
          · have h3 : 0 < (1 - χ z) * 4 / ‖psiVa ψ y τ z‖ :=
              div_pos hp (norm_pos_iff.mpr hv0)
            have h4 : 0 ≤ 1 - (1 - χ z) * 4 := by linarith
            linarith
        have harg : ((1 - χ z) * 4 / ‖psiVa ψ y τ z‖ + (1 - (1 - χ z) * 4)) •
            psiVa ψ y τ z ≠ 0 := smul_ne_zero (ne_of_gt hcoef) hv0
        rw [BCU.profile2, if_neg h1, if_neg h2, BCU.shiftPhase2] at hcon
        rw [smul_zero, add_zero] at hcon
        exact harg ((BCU.bcu_clampBall_eq_zero _).mp hcon)
  · rw [psiPhi_eq_northPole ψ y τ χ z (hout z hmem)] at hcon
    exact BCU.bcu_northPole_ne_zero n hcon

end Work.ThomBordism.LeadChapter
