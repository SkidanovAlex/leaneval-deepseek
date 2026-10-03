import Mathlib
import Submission.Work.Pert.pert2v2.HdiffRow.EfQpAux
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.Prelim

namespace Work.Pert.pert2v2.HdiffRow

open Complex Set Filter
open scoped Topology

noncomputable section

theorem seedP_germ_add_one_local {Φm Φp : ℂ → ℂ} {Q Qp : Set ℂ} {y : ℝ}
    (hQopen : IsOpen Q) (hQpopen : IsOpen Qp)
    (hΦm : DifferentiableOn ℂ Φm Q) (hder : ∀ z ∈ Q, deriv Φm z ≠ 0)
    (hInj : Set.InjOn Φm Q) (hΦp : DifferentiableOn ℂ Φp Qp)
    (hlvl : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1 ∈ Φm '' Q →
      Φp (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1))
        = Φp (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ))) + 1)
    {u : ℂ} (hu : u ∈ Φm '' Q) (hu1 : u + 1 ∈ Φm '' Q) (him : y ≤ u.im)
    (hre : u.re ∈ Set.Ico 0 1)
    (h0 : Work.Pert.invOn Φm Q u ∈ Qp) (h1 : Work.Pert.invOn Φm Q (u + 1) ∈ Qp) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℂ, ‖τ‖ < δ →
      Work.Pert.seedP Φp Φm Q (u + 1 + τ) = Work.Pert.seedP Φp Φm Q (u + τ) + 1 := by
  classical
  -- the ball around `u` on which both seed values are holomorphic
  obtain ⟨r, hrpos, hrQ, hrQ1, hrQp, hrQp1⟩ :=
    exists_ball_germ_data hQopen hΦm hInj hder hQpopen hu hu1 h0 h1
  set G : ℂ → ℂ :=
    fun z => Work.Pert.seedP Φp Φm Q (z + 1) - Work.Pert.seedP Φp Φm Q z - 1 with hG
  have hseed : DifferentiableOn ℂ (Work.Pert.seedP Φp Φm Q) (Metric.ball u r) := by
    intro z hz
    exact (seedP_differentiableAt_of_invOn_mem hQopen hΦm hInj hder (hrQ hz)
      (hΦp.differentiableAt (hQpopen.mem_nhds (hrQp z hz)))).differentiableWithinAt
  have hseed1 : DifferentiableOn ℂ (fun z : ℂ => Work.Pert.seedP Φp Φm Q (z + 1))
      (Metric.ball u r) := by
    intro z hz
    have h : DifferentiableAt ℂ (Work.Pert.seedP Φp Φm Q) (z + 1) :=
      seedP_differentiableAt_of_invOn_mem hQopen hΦm hInj hder (hrQ1 z hz)
        (hΦp.differentiableAt (hQpopen.mem_nhds (hrQp1 z hz)))
    exact (h.comp z (differentiableAt_id.add_const 1)).differentiableWithinAt
  have hGdiff : DifferentiableOn ℂ G (Metric.ball u r) := by
    rw [hG]
    exact (hseed1.sub hseed).sub_const 1
  -- the window form of the level-one structure
  have hzero : ∀ z : ℂ, z + 1 ∈ Φm '' Q → y ≤ z.im → z.re ∈ Set.Ico 0 1 → G z = 0 := by
    intro z hz1 hzim hzre
    have h := Work.Pert.pert2v2.EfFloorDiffV2.seedP_add_one_of_re_Ico hlvl hzim hzre hz1
    rw [hG]
    show Work.Pert.seedP Φp Φm Q (z + 1) - Work.Pert.seedP Φp Φm Q z - 1 = 0
    rw [h]; ring
  -- the north-east shift `z₀ = u + t + i t` into the open window `{0 < Re, y < Im}`
  set t : ℝ := min (r / 4) ((1 - u.re) / 2) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min (by linarith) (by linarith [hre.2])
  have ht4 : t ≤ r / 4 := by rw [ht]; exact min_le_left _ _
  have ht1 : u.re + t < 1 := by
    have h : min (r / 4) ((1 - u.re) / 2) ≤ (1 - u.re) / 2 := min_le_right _ _
    rw [← ht] at h; linarith
  have ht0 : 0 < u.re + t := by linarith [hre.1]
  have hty : y < u.im + t := by linarith [him]
  set z₀ : ℂ := u + (t : ℂ) + (t : ℂ) * I with hz0
  have hz0re : z₀.re = u.re + t := by rw [hz0]; simp
  have hz0im : z₀.im = u.im + t := by rw [hz0]; simp
  have hz0ball : z₀ ∈ Metric.ball u r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : z₀ - u = (t : ℂ) + (t : ℂ) * I := by rw [hz0]; ring
    rw [hsub]
    have h1 : ‖(t : ℂ) + (t : ℂ) * I‖ ≤ ‖(t : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    have h2 : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have h3 : ‖(t : ℂ) * I‖ = t := by rw [norm_mul, Complex.norm_I, mul_one, h2]
    rw [h2, h3] at h1
    linarith
  -- the open set on which `G` is known to vanish
  set W : Set ℂ := {z : ℂ | z.re ∈ Set.Ioo 0 1} ∩ {z : ℂ | y < z.im} ∩ Metric.ball u r with hW
  have hWopen : IsOpen W := by
    rw [hW]
    exact ((isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioi.preimage Complex.continuous_im)).inter Metric.isOpen_ball
  have hz0W : z₀ ∈ W := by
    rw [hW]
    refine ⟨⟨?_, ?_⟩, hz0ball⟩
    · change z₀.re ∈ Set.Ioo 0 1
      rw [hz0re]; exact ⟨ht0, ht1⟩
    · change y < z₀.im
      rw [hz0im]; exact hty
  have hev : G =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hWopen.mem_nhds hz0W] with z hz
    rw [hW] at hz
    obtain ⟨⟨hzre, hzim⟩, hzball⟩ := hz
    exact hzero z (hrQ1 z hzball) (le_of_lt hzim) ⟨le_of_lt hzre.1, hzre.2⟩
  -- identity theorem on the preconnected ball
  have hGan : AnalyticOnNhd ℂ G (Metric.ball u r) :=
    hGdiff.analyticOnNhd Metric.isOpen_ball
  have hball0 : ∀ z ∈ Metric.ball u r, G z = 0 :=
    hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero Metric.isPreconnected_ball hz0ball hev
  refine ⟨r, hrpos, fun τ hτ => ?_⟩
  have hmemτ : u + τ ∈ Metric.ball u r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : u + τ - u = τ := by ring
    rw [hsub]; exact hτ
  have hz := hball0 (u + τ) hmemτ
  rw [hG] at hz
  change Work.Pert.seedP Φp Φm Q (u + τ + 1) - Work.Pert.seedP Φp Φm Q (u + τ) - 1 = 0 at hz
  have harg : u + τ + 1 = u + 1 + τ := by ring
  rw [harg] at hz
  linear_combination hz

end

end Work.Pert.pert2v2.HdiffRow
