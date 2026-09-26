/-
# The compact "spike region" inside the funnel

For `B ≥ 3` the set

  `spikeSet B = {p : ℍ × ℍ | |p.1.re| ≤ 1, 2 ≤ p.1.im ≤ B, ‖p.2 - p.1‖ = 29/20}`

is closed and bounded in `ℍ × ℍ`, hence compact (`isCompact_spikeSet`).  It contains every
pair `(τ,ζ)` with `τ` in the funnel, `τ.im ≤ B` and `ζ` on the spike circle of radius `29/20`
around `τ`.  Boundedness is measured with the hyperbolic distance from `I`
(`dist_I_le`), using that `ℍ` is a proper metric space.

This is the compactness input for the *strip* part of the spike-circle bound: on the strip
`2 ≤ Im τ ≤ 3` the kernel is bounded by a constant, by continuity of `AfunFun` on the compact
set together with the lower bound `sphereLowerStrip` for the divisor `j τ - j ζ`.

(The file formerly contained a stand-alone proof of the divisor lower bound on the spike
circle; that result is now `Work.Asymptotics.SpikeCircle.divisorLowerDisc`.)
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic

set_option maxHeartbeats 1600000
namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane

noncomputable section

def spikeSet (B : ℝ) : Set (UpperHalfPlane × UpperHalfPlane) :=
  {p | |p.1.re| ≤ 1} ∩ {p | 2 ≤ p.1.im} ∩ {p | p.1.im ≤ B} ∩
    {p | ‖(p.2 : ℂ) - (p.1 : ℂ)‖ = 29 / 20}

theorem mem_spikeSet (B : ℝ) (p : UpperHalfPlane × UpperHalfPlane) :
    p ∈ spikeSet B ↔ |p.1.re| ≤ 1 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ B ∧
      ‖(p.2 : ℂ) - (p.1 : ℂ)‖ = 29 / 20 := by
  rw [spikeSet]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]

theorem isClosed_spikeSet (B : ℝ) : IsClosed (spikeSet B) := by
  rw [spikeSet]
  have h1 : IsClosed {p : UpperHalfPlane × UpperHalfPlane | |p.1.re| ≤ 1} :=
    isClosed_Iic.preimage ((UpperHalfPlane.continuous_re.comp continuous_fst).abs)
  have h2 : IsClosed {p : UpperHalfPlane × UpperHalfPlane | 2 ≤ p.1.im} :=
    isClosed_Ici.preimage (UpperHalfPlane.continuous_im.comp continuous_fst)
  have h3 : IsClosed {p : UpperHalfPlane × UpperHalfPlane | p.1.im ≤ B} :=
    isClosed_Iic.preimage (UpperHalfPlane.continuous_im.comp continuous_fst)
  have h4 : IsClosed {p : UpperHalfPlane × UpperHalfPlane |
      ‖(p.2 : ℂ) - (p.1 : ℂ)‖ = 29 / 20} :=
    isClosed_eq ((UpperHalfPlane.continuous_coe.comp continuous_snd).sub
      (UpperHalfPlane.continuous_coe.comp continuous_fst)).norm continuous_const
  exact ((h1.inter h2).inter h3).inter h4

theorem dist_I_le (B : ℝ) (hB : 3 ≤ B) {z : UpperHalfPlane}
    (hr : |z.re| ≤ 3) (h1 : 1 / 2 ≤ z.im) (h2 : z.im ≤ B + 2) :
    dist z UpperHalfPlane.I ≤ 2 * Real.arsinh (B + 6) := by
  rw [UpperHalfPlane.dist_eq]
  have hIim : (UpperHalfPlane.I).im = 1 := by
    rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_I]; simp
  have hcoe : ((z : ℂ) - ((UpperHalfPlane.I : UpperHalfPlane) : ℂ))
      = ((z.re : ℂ) + ((z.im - 1 : ℝ) : ℂ) * Complex.I) := by
    rw [UpperHalfPlane.coe_I]
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
  have hnorm : ‖(z : ℂ) - ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ ≤ B + 4 := by
    rw [hcoe]
    have h3 : ‖((z.re : ℂ) + ((z.im - 1 : ℝ) : ℂ) * Complex.I)‖ ≤ |z.re| + |z.im - 1| := by
      have h := Complex.norm_le_abs_re_add_abs_im
        ((z.re : ℂ) + ((z.im - 1 : ℝ) : ℂ) * Complex.I)
      rwa [show ((z.re : ℂ) + ((z.im - 1 : ℝ) : ℂ) * Complex.I).re = z.re from by simp,
        show ((z.re : ℂ) + ((z.im - 1 : ℝ) : ℂ) * Complex.I).im = z.im - 1 from by simp] at h
    have h4 : |z.im - 1| ≤ B + 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hkey : dist (z : ℂ) ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)
      / (2 * Real.sqrt (z.im * (UpperHalfPlane.I).im)) ≤ B + 6 := by
    rw [hIim, mul_one, dist_eq_norm]
    have hs : (1 : ℝ) / 2 ≤ Real.sqrt z.im := by
      have h4 : ((1 / 2 : ℝ)) ^ 2 ≤ z.im := by norm_num; linarith
      have h5 : Real.sqrt (((1 / 2 : ℝ)) ^ 2) ≤ Real.sqrt z.im := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h5
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnorm, hs]
  calc 2 * Real.arsinh (dist (z : ℂ) ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)
        / (2 * Real.sqrt (z.im * (UpperHalfPlane.I).im)))
      ≤ 2 * Real.arsinh (B + 6) := by
        have := Real.arsinh_le_arsinh.mpr hkey
        linarith

theorem spikeSet_subset (B : ℝ) (hB : 3 ≤ B) :
    spikeSet B ⊆ Metric.closedBall UpperHalfPlane.I (2 * Real.arsinh (B + 6)) ×ˢ
      Metric.closedBall UpperHalfPlane.I (2 * Real.arsinh (B + 6)) := by
  intro p hp
  obtain ⟨hr, h2, h3, h4⟩ := (mem_spikeSet B p).mp hp
  have hAB : ∀ a b : UpperHalfPlane, ‖(a : ℂ) - (b : ℂ)‖ ≤ 29 / 20 →
      |a.im - b.im| ≤ 29 / 20 ∧ |a.re - b.re| ≤ 29 / 20 := by
    intro a b hab
    have h1 : ((a : ℂ) - (b : ℂ)).im = a.im - b.im := by simp
    have h2 : ((a : ℂ) - (b : ℂ)).re = a.re - b.re := by simp
    exact ⟨le_trans (by rw [← h1]; exact Complex.abs_im_le_norm _) hab,
      le_trans (by rw [← h2]; exact Complex.abs_re_le_norm _) hab⟩
  obtain ⟨him, hre⟩ := hAB p.2 p.1 (le_of_eq h4)
  have h2im : (1 : ℝ) / 2 ≤ p.2.im := by linarith [abs_le.mp him]
  have h2re : |p.2.re| ≤ 3 := by
    have h5 := abs_le.mp hre
    have h6 := abs_le.mp hr
    rw [abs_le]; constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]
  have h2B : p.2.im ≤ B + 2 := by
    have h5 := abs_le.mp him
    linarith [h5.2]
  rw [Set.mem_prod]
  refine ⟨dist_I_le B hB ?_ (by linarith) (by linarith), dist_I_le B hB h2re h2im h2B⟩
  rw [abs_le]
  have h6 := abs_le.mp hr
  exact ⟨by linarith [h6.1], by linarith [h6.2]⟩

theorem isCompact_spikeSet (B : ℝ) (hB : 3 ≤ B) : IsCompact (spikeSet B) :=
  (isCompact_closedBall UpperHalfPlane.I (2 * Real.arsinh (B + 6))).prod
    (isCompact_closedBall UpperHalfPlane.I (2 * Real.arsinh (B + 6)))
    |>.of_isClosed_subset (isClosed_spikeSet B) (spikeSet_subset B hB)

theorem continuous_jInvariantFun :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ) := by
  have h4 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ) :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hΔ : Continuous (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ) :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have h : Work.Kernels.jInvariantFun
      = fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := by
    funext τ; rfl
  rw [h]
  exact (h4.pow 3).div hΔ (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

end

end Work.Asymptotics.SpikeCircle
