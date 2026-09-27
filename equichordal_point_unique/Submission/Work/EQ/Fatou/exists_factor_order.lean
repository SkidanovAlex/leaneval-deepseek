import Mathlib

namespace Work.EQ.Fatou

open Filter Metric
open scoped Topology

theorem exists_factor_order (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {c : ℂ}
    (hne : ∃ z ∈ Metric.ball (0:ℂ) 1, g z ≠ c) :
    ∃ (k : ℕ) (h : ℂ → ℂ), DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0:ℂ) 1, g z - c = z ^ k * h z) ∧ h 0 ≠ 0 := by
  set u : ℂ → ℂ := fun z => g z - c with hu
  have hu' : ∀ z, u z = g z - c := fun z => congrFun hu z
  have hud : DifferentiableOn ℂ u (Metric.ball 0 1) := hg.sub (differentiableOn_const c)
  have hua : AnalyticAt ℂ u 0 :=
    hud.analyticAt (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball]))
  have hnotz : ¬ ∀ᶠ z in 𝓝 (0:ℂ), u z = 0 := by
    intro hev
    obtain ⟨z, hzmem, hzg⟩ := hne
    have hana : AnalyticOnNhd ℂ u (Metric.ball 0 1) := hud.analyticOnNhd Metric.isOpen_ball
    have hconn : IsPreconnected (Metric.ball (0:ℂ) 1) :=
      (convex_ball (0:ℂ) 1).isPreconnected
    have h0 : (0:ℂ) ∈ Metric.ball 0 1 := by simp [Metric.mem_ball]
    have hev0 : u =ᶠ[𝓝 (0:ℂ)] 0 := by
      filter_upwards [hev] with w hw
      simpa using hw
    have huz0 : u z = 0 := by
      simpa using hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn h0 hev0 hzmem
    have huz : u z ≠ 0 := by
      rw [hu']
      exact sub_ne_zero.mpr hzg
    exact huz huz0
  obtain ⟨k, g₀, hg₀an, hg₀ne, hg₀eq⟩ :=
    (hua.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnotz
  refine ⟨k, (fun z => if z = 0 then g₀ 0 else u z / z ^ k), ?_, ?_, ?_⟩
  · intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]
      have hev : (fun z => if z = 0 then g₀ 0 else u z / z ^ k) =ᶠ[𝓝 (0:ℂ)] g₀ := by
        filter_upwards [hg₀eq] with w hw
        by_cases hw0 : w = 0
        · simp [hw0]
        · rw [ite_eq_right hw0]
          rw [hw, sub_zero, smul_eq_mul,
            mul_div_cancel_left₀ (g₀ w) (pow_ne_zero k hw0)]
      exact ((hg₀an.differentiableAt).congr_of_eventuallyEq hev).differentiableWithinAt
    · have hev : (fun z => if z = 0 then g₀ 0 else u z / z ^ k) =ᶠ[𝓝 z]
          (fun w => u w / w ^ k) := by
        filter_upwards [show ({0}ᶜ : Set ℂ) ∈ 𝓝 z from
          isOpen_compl_singleton.mem_nhds (by simpa using hz0)] with w hw
        have hw0 : w ≠ 0 := by simpa using hw
        rw [ite_eq_right hw0]
      exact (((hud.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).div
          (differentiableAt_id.pow k) (pow_ne_zero k hz0)).congr_of_eventuallyEq hev)
        |>.differentiableWithinAt
  · intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]
      show g 0 - c = 0 ^ k * (if (0:ℂ) = 0 then g₀ 0 else u 0 / 0 ^ k)
      rw [← hu' 0, ite_eq_left rfl]
      have hge : u =ᶠ[𝓝 (0:ℂ)] (fun z => (z - 0) ^ k • g₀ z) := hg₀eq
      simpa [sub_zero, smul_eq_mul] using hge.eq_of_nhds
    · show g z - c = z ^ k * (if z = 0 then g₀ 0 else u z / z ^ k)
      rw [← hu' z, ite_eq_right hz0, mul_div_cancel₀ (u z) (pow_ne_zero k hz0)]
  · simpa using hg₀ne

end Work.EQ.Fatou
