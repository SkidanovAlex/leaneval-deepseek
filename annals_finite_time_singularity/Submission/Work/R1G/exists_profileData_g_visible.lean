import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.Defs
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.R1G.GTest
import Submission.Work.R1G.gTest_decayInZ
import Submission.Work.R1G.gTest_hkMem
import Submission.Work.R1G.gTest_holder_z
import Submission.Work.R1G.gTest_holder_theta
import Submission.Work.R1G.gTest_zpz
import Submission.Work.R1G.gTest_profile_deriv
import Submission.Work.R1G.gTest_meas
import Submission.Work.R1G.gTest_hvan
import Submission.Work.R1G.hkNorm_gTest_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **A `ProfileData` whose perturbation is visible on the open quadrant.**

The witness is the explicit analytic perturbation `g = ε·z²e^{-z}·sin(2θ)` of
`Work.R1G.GTest`, at the small amplitude `ε` that makes the `St5` smallness
`Cg ≤ p·Γ(p,π/4)/(4c(p))` hold (`ε` is chosen so that the `ℋ²`-norm of `g`, which is *linear*
in `ε` — `Work.R1G.hkNorm_gTest_le` — is small enough), with the standard modulation
`λ̄(t) = 1 - t/2` at `T = 2`.

The perturbation is nonzero at the visible point `(z,θ) = (1,π/4)`
(`Work.R1G.gTest_visible`), unlike the delivered inhabitant of `ProfileData`. -/
theorem exists_profileData_g_visible {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ P : Work.ConstructionInstance.ProfileData α,
      (∃ z θ : ℝ, 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ P.g z θ ≠ 0)
        ∧ P.lam = (fun t : ℝ => 1 - t / 2) := by
  have hp : 0 < Work.ConstructionInstance.profExp α := Work.ConstructionInstance.profExp_pos hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c (Work.ConstructionInstance.profExp α) :=
    (Work.Spaces.c_bounds (Work.ConstructionInstance.profExp α) hp hp1).1
  have hcpos : 0 < Work.Spaces.c (Work.ConstructionInstance.profExp α) := by linarith
  have hGampos : 0 < Work.Spaces.Gam (Work.ConstructionInstance.profExp α) (Real.pi / 4) := by
    rw [Work.Spaces.Gam]
    refine Real.rpow_pos_of_pos ?_ _
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    norm_num
  -- the smallness bound `p·Γ(p,π/4)/(4c(p))`
  set Bnd : ℝ := Work.ConstructionInstance.profExp α
      * Work.Spaces.Gam (Work.ConstructionInstance.profExp α) (Real.pi / 4)
      / (4 * Work.Spaces.c (Work.ConstructionInstance.profExp α)) with hBnddef
  have hBndpos : 0 < Bnd := by
    rw [hBnddef]
    exact div_pos (mul_pos hp hGampos) (by linarith)
  -- the `ℋ²`-size of the amplitude-one perturbation
  set K : ℝ := 100 / Real.sqrt (Work.Spaces.gam (Work.ConstructionInstance.profExp α) - 1)
      * Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 (gTest 1) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Work.Spaces.HkNorm_nonneg _ _ _)
  have hK1pos : 0 < K + 1 := by linarith
  -- the amplitude
  set ε : ℝ := min 1 (Bnd / (K + 1)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min one_pos (div_pos hBndpos hK1pos)
  have hεnn : 0 ≤ ε := hεpos.le
  have hεle : ε ≤ Bnd / (K + 1) := by rw [hεdef]; exact min_le_right _ _
  -- the `L^∞` constant of the perturbation
  set Cg : ℝ := 100 / Real.sqrt (Work.Spaces.gam (Work.ConstructionInstance.profExp α) - 1)
      * Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 (gTest ε) with hCgdef
  have hCgnn : 0 ≤ Cg := by
    rw [hCgdef]
    exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Work.Spaces.HkNorm_nonneg _ _ _)
  -- the `St5` smallness
  have hsmall : Cg ≤ Bnd := by
    have h1 : Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 (gTest ε)
        ≤ ε * Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 (gTest 1) :=
      hkNorm_gTest_le (Work.ConstructionInstance.profExp α) hεnn
    have h2 : (0 : ℝ) ≤ 100 / Real.sqrt
        (Work.Spaces.gam (Work.ConstructionInstance.profExp α) - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have h3 : Cg ≤ (100 / Real.sqrt
        (Work.Spaces.gam (Work.ConstructionInstance.profExp α) - 1))
          * (ε * Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 (gTest 1)) := by
      rw [hCgdef]
      exact mul_le_mul_of_nonneg_left h1 h2
    have h4 : (100 / Real.sqrt (Work.Spaces.gam (Work.ConstructionInstance.profExp α) - 1))
          * (ε * Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 (gTest 1))
        = ε * K := by
      rw [hKdef]; ring
    have h5 : ε * K ≤ Bnd := by
      have h6 : ε * K ≤ (Bnd / (K + 1)) * K := mul_le_mul_of_nonneg_right hεle hKnn
      have h7 : (Bnd / (K + 1)) * K = Bnd * (K / (K + 1)) := by ring
      have h8 : K / (K + 1) ≤ 1 := by
        rw [div_le_one hK1pos]; linarith
      have h9 : Bnd * (K / (K + 1)) ≤ Bnd := by
        calc Bnd * (K / (K + 1)) ≤ Bnd * 1 :=
              mul_le_mul_of_nonneg_left h8 hBndpos.le
          _ = Bnd := mul_one Bnd
      linarith [h6, h7, h9]
    linarith [h3, h4, h5]
  -- the data for the perturbation
  obtain ⟨Lg, hLg, hzk⟩ :=
    gTest_holder_z (β := (α : ℝ)) hα (by linarith [hα13]) ε
  obtain ⟨Lθ, hLθ, hzth⟩ :=
    gTest_holder_theta (β := (α : ℝ)) hα (by linarith [hα13]) ε
  obtain ⟨Cg', hCg'nn, hg2⟩ := gTest_zpz ε
  refine ⟨{ hα := hα
            g := gTest ε
            hvt := gTest_vanish_theta ε
            hsmooth := gTest_smoothNbhd ε
            hquad0 := gTest_zero_z ε
            hquad := pz_gTest_zero_z ε
            Cg := Cg
            hCg := hCgnn
            hdec := gTest_decayInZ ε
            hmem := gTest_hkMem hp hp1 ε
            hCgbig := le_refl _
            Cv := 4 * ε
            hCv := by linarith
            hvan := gTest_hvan hα.le hα13 ε hεnn
            Lg := Lg
            hLg := hLg
            hzk := hzk
            Lθ := Lθ
            hLθ := hLθ
            hzth := hzth
            Cg' := Cg'
            hg2 := hg2
            hgdiff := gTest_profile_deriv (Work.ConstructionInstance.profExp α) ε
            hsmall := hsmall
            hmeasP := gTest_meas hp.le ε
            hα13 := hα13
            T := 2
            hT := by norm_num
            lam := fun t : ℝ => 1 - t / 2
            hlam := fun t ht => by linarith [ht.2]
            hlam0 := by norm_num
            K := 1 / 2
            hK := by norm_num
            hK12 := by norm_num
            hlamdif := fun t _ => Work.ConstructionInstance.hasDerivAt_lamStd t
            hlamd := fun t _ => by
              rw [Work.ConstructionInstance.hderivval t]; norm_num
            hlam_le := fun t ht => by linarith [ht.2]
            hlam_low := fun t _ => le_of_eq (by ring)
            L := (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1
            hL := by
              have h4 : (0 : ℝ) < (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) :=
                Real.rpow_pos_of_pos (by norm_num) _
              linarith
            hLbig := by
              have h : (2 * (2 : ℝ)) = 4 := by norm_num
              rw [h]
              exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
            M := 20 * Work.ConstructionInstance.profExp α + Cg
            hM := by linarith [hp.le, hCgnn]
            hMprof := le_refl _
            M₁ := (1 / 2) * (20 * Work.ConstructionInstance.profExp α + Cg + Cg')
            hM₁ := by linarith [hp.le, hCgnn, hCg'nn]
            hM₁big := le_refl _
            R := 2 * ((4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1)
            hR := by
              have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) :=
                (Real.rpow_pos_of_pos (by norm_num) _).le
              linarith
            hRbig := le_refl _ },
        ⟨1, Real.pi / 4, by norm_num, by linarith [Real.pi_pos],
          by linarith [Real.pi_pos], gTest_visible (ne_of_gt hεpos)⟩,
        rfl⟩

end Work.R1G
