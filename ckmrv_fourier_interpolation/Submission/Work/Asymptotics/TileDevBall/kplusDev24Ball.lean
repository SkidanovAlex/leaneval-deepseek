import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.Tile.HalfDev24Aux
import Submission.Work.Asymptotics.Tile.HalfDev24TileFacts
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.Tile.halfDevClearOffAxis24Plus

namespace Work.Asymptotics.TileDevBall

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

set_option autoImplicit false in
theorem kplusDev24Ball (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          3 ≤ ζ.im →
          ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gplus 24 ((n : ℝ) +ᵥ w) ζ)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C0, N0, M0, hC0, hN0, hM0, hb⟩ :=
    Work.Asymptotics.Tile.halfDevClearOffAxis24Plus ℓ
  refine ⟨C0 * 4 ^ M0 * Real.exp (2 * Real.pi * (29 / 20)) + 1, N0 + M0,
    by positivity, by linarith, ?_⟩
  intro w hw n hn ζ hball him
  have hwD : w ∈ Work.Asymptotics.DomainD := (Work.Asymptotics.mem_KEpsilon.mp hw).1
  have hB : Ball w ζ := ⟨hw, hball, him⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := (Work.Kernels.scale_pos w).le
  have hSim : (ModularGroup.S • w).im ≤ Work.Kernels.scale w :=
    Work.Asymptotics.EtailE.E_im_S_le_scale w
  -- The ball hypothesis forces `|Re ζ| ≤ 3`, the off-axis hypothesis of the half-deviation bound.
  have hre : |(ζ : ℂ).re| ≤ 3 := by
    have hSD : ModularGroup.S • w ∈ Work.Asymptotics.DomainD :=
      Work.Asymptotics.S_smul_mem_DomainD hwD
    have hSre : |(ModularGroup.S • w).re| < 1 := by
      rw [abs_lt]; exact ⟨hSD.1, hSD.2.1⟩
    have hcoe : (((ModularGroup.S • w : ℍ)) : ℂ).re = (ModularGroup.S • w).re :=
      UpperHalfPlane.coe_re _
    have h1 : |(ζ : ℂ).re - (ModularGroup.S • w).re| ≤ 29 / 20 := by
      have h := Complex.abs_re_le_norm ((ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ))
      rw [Complex.sub_re, hcoe] at h
      exact le_trans h hball
    have h2 : |(ζ : ℂ).re|
        ≤ |(ζ : ℂ).re - (ModularGroup.S • w).re| + |(ModularGroup.S • w).re| := by
      have h := abs_add_le ((ζ : ℂ).re - (ModularGroup.S • w).re) ((ModularGroup.S • w).re)
      have heq : (ζ : ℂ).re - (ModularGroup.S • w).re + (ModularGroup.S • w).re
          = (ζ : ℂ).re := by ring
      rwa [heq] at h
    linarith
  have hmain := hb w n ζ hn hw him hre
  rw [norm_mul]
  refine le_trans hmain ?_
  have hζpos : (0 : ℝ) ≤ 1 + ζ.im := by linarith [hB.im_pos]
  have h1im : 1 + ζ.im ≤ 4 * Work.Kernels.scale w := by
    have h := hB.im_le
    linarith
  have hpow : (1 + ζ.im) ^ M0 ≤ 4 ^ M0 * (Work.Kernels.scale w) ^ M0 := by
    have h := Real.rpow_le_rpow hζpos h1im hM0
    rwa [Real.mul_rpow (by norm_num) hs0] at h
  have hexp : Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im))
      ≤ Real.exp (2 * Real.pi * (29 / 20)) := by
    apply Real.exp_le_exp.mpr
    have h := hB.im_ge
    have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    nlinarith
  have hstep1 : C0 * (Work.Kernels.scale w) ^ N0 * (1 + ζ.im) ^ M0
        * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im))
      ≤ C0 * (Work.Kernels.scale w) ^ N0 * (4 ^ M0 * (Work.Kernels.scale w) ^ M0)
        * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0.le (Real.rpow_nonneg hs0 _))
  have hstep2 : C0 * (Work.Kernels.scale w) ^ N0 * (4 ^ M0 * (Work.Kernels.scale w) ^ M0)
        * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - ζ.im))
      ≤ C0 * (Work.Kernels.scale w) ^ N0 * (4 ^ M0 * (Work.Kernels.scale w) ^ M0)
        * Real.exp (2 * Real.pi * (29 / 20)) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  refine le_trans (le_trans hstep1 hstep2) ?_
  have hEq : C0 * (Work.Kernels.scale w) ^ N0 * (4 ^ M0 * (Work.Kernels.scale w) ^ M0)
        * Real.exp (2 * Real.pi * (29 / 20))
      = C0 * 4 ^ M0 * Real.exp (2 * Real.pi * (29 / 20))
        * (Work.Kernels.scale w) ^ (N0 + M0) := by
    rw [Real.rpow_add (Work.Kernels.scale_pos w) N0 M0]; ring
  rw [hEq]
  have hp : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (N0 + M0) := Real.rpow_nonneg hs0 _
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hp

end Work.Asymptotics.TileDevBall
