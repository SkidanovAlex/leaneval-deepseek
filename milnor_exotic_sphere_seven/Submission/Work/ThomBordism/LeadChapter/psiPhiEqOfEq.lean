import Mathlib
import Submission.Work.ThomBordism.LeadChapter.bdryAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 3200000

namespace Work.ThomBordism.LeadChapter

noncomputable section

theorem psiPhiEqOfEq (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    {y x₀ : W} (hyψ : y ∈ ψ.source)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ)
    (hVpos : 0 < (Work.ThomBordism.LeadChapter.psiVa ψ y τ x₀) 0)
    (hVeq : ∀ z ∈ ψ.source,
      Work.ThomBordism.LeadChapter.psiVa ψ y τ z = Work.ThomBordism.LeadChapter.psiVa ψ y τ x₀ →
        z = x₀)
    {χ : W → ℝ} (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hout : ∀ z, z ∉ ψ.source → χ z = 0)
    (S : Set W) (hS : ∀ z ∈ S, χ z = 1) (hyS : y ∈ S)
    (hSray : ∀ z ∈ ψ.source,
      (∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
        Work.ThomBordism.LeadChapter.psiVa ψ y τ z =
          m • Work.ThomBordism.LeadChapter.psiVa ψ y τ x₀) → z ∈ S)
    (hVne : Work.ThomBordism.LeadChapter.psiVa ψ y τ x₀ ≠ 0)
    (hVnorm : ‖Work.ThomBordism.LeadChapter.psiVa ψ y τ x₀‖ ≤ 1 / 2)
    {z : W} (hz : Work.ThomBordism.LeadChapter.psiPhi ψ y τ χ z =
      Work.ThomBordism.LeadChapter.psiVa ψ y τ x₀) : z = x₀ := by
  by_cases hmem : z ∈ ψ.source
  · have hv0 : psiVa ψ y τ z ≠ 0 := by
      intro h0
      have hzy := (psiVa_eq_zero_iff ψ (ne_of_gt hτ) hyψ hmem).mp h0
      rw [psiPhi_apply, hzy, psiVa_self, hS y hyS, bcu_profile2_one_zero] at hz
      exact hVne hz.symm
    have hv0' : 0 ≤ (psiVa ψ y τ z) 0 :=
      psiVa_coord_nonneg ψ hbd hyψ hy (le_of_lt hτ) hmem
    rw [psiPhi_apply] at hz
    by_cases hχ : χ z ≤ 1 / 2
    · rw [BCU.profile2, if_pos hχ] at hz
      have hnorm := congrArg norm hz
      rw [BCU.bcu_northPole_norm] at hnorm
      linarith [norm_nonneg (psiVa ψ y τ x₀)]
    · by_cases hχ2 : χ z ≤ 3 / 4
      · have hlt1 : 1 / 2 < χ z := lt_of_not_ge hχ
        have hφ0 : 0 ≤ (3 / 4 - χ z) * 2 * Real.pi :=
          mul_nonneg (by linarith) (by positivity)
        have hφ1 : (3 / 4 - χ z) * 2 * Real.pi ≤ Real.pi / 2 := by
          have h4 : (3 / 4 - χ z) * 2 ≤ 1 / 2 := by linarith
          nlinarith [Real.pi_pos]
        have hcos : 0 ≤ Real.cos ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
        have hsin : 0 ≤ Real.sin ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.sin_nonneg_of_mem_Icc ⟨hφ0, by linarith [Real.pi_pos]⟩
        rw [BCU.profile2, if_neg hχ, if_pos hχ2] at hz
        have hnorm := BCU.bcu_sphPhase_norm_eq_one ((3 / 4 - χ z) * 2 * Real.pi)
          (psiVa ψ y τ z) hv0 hcos hsin hv0'
        rw [hz] at hnorm
        linarith [norm_nonneg (psiVa ψ y τ x₀)]
      · have hlt : 3 / 4 < χ z := lt_of_not_ge hχ2
        have hfib := (Work.ThomBordism.bcu_profile2_properties n).2.2.2.2.2
          0 (psiVa ψ y τ z) (psiVa ψ y τ x₀) (χ z) rfl hv0' hv0 hVpos hVnorm hz
        rw [smul_zero, add_zero] at hfib
        rcases hfib with hconj | halg
        · exact hVeq z hmem hconj.2
        · by_cases hχ1 : χ z = 1
          · have h := halg
            rw [hχ1] at h
            norm_num at h
            exact hVeq z hmem h
          · exfalso
            set p : ℝ := (1 - χ z) * 4 with hpdef
            have hp0 : 0 < p := by
              rw [hpdef]
              have hlt1 : χ z < 1 := lt_of_le_of_ne (hχ01 z).2 hχ1
              nlinarith
            have hp1 : p < 1 := by
              rw [hpdef]
              have : 0 < 1 - χ z := by linarith [(hχ01 z).2]
              linarith
            set lam : ℝ := p / ‖psiVa ψ y τ z‖ + (1 - p) with hldef
            have hlam : 0 < lam := by
              rw [hldef]
              have h3 : 0 < p / ‖psiVa ψ y τ z‖ := div_pos hp0 (norm_pos_iff.mpr hv0)
              have h4 : 0 < 1 - p := by linarith
              linarith
            have heq : lam • psiVa ψ y τ z = psiVa ψ y τ x₀ := by
              rw [← halg]
            have hmu : psiVa ψ y τ z = lam⁻¹ • psiVa ψ y τ x₀ := by
              rw [← heq, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt hlam), one_smul]
            have hmu0 : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
            have hmu1 : lam⁻¹ ≤ 1 := by
              have hnorm_v : lam * ‖psiVa ψ y τ z‖ = ‖psiVa ψ y τ x₀‖ := by
                have hh := congrArg norm heq
                rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hh
              have hexp : lam * ‖psiVa ψ y τ z‖ = p + (1 - p) * ‖psiVa ψ y τ z‖ := by
                rw [hldef]
                field_simp
              have hvle : ‖psiVa ψ y τ z‖ ≤ ‖psiVa ψ y τ x₀‖ := by
                nlinarith [hp0, hp1, hnorm_v, hexp, hVnorm]
              have hVp : 0 < ‖psiVa ψ y τ x₀‖ := norm_pos_iff.mpr hVne
              have hinv : lam⁻¹ = ‖psiVa ψ y τ z‖ / ‖psiVa ψ y τ x₀‖ := by
                field_simp
                linarith [hnorm_v]
              rw [hinv, div_le_one hVp]
              exact hvle
            have hzS : z ∈ S := hSray z hmem ⟨lam⁻¹, hmu0, hmu1, hmu⟩
            have h1 := hS z hzS
            rw [h1] at hpdef
            rw [hpdef] at hp0
            norm_num at hp0
  · rw [psiPhi_eq_northPole ψ y τ χ z (hout z hmem)] at hz
    have hnorm := congrArg norm hz
    rw [BCU.bcu_northPole_norm] at hnorm
    linarith [norm_nonneg (psiVa ψ y τ x₀)]

end

end Work.ThomBordism.LeadChapter
