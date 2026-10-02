import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.w0_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

theorem mem_Dst_of_F_mem {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < r →
      Work.PARIMPL.Ft c₀ z ∈ Work.FlowerGlue2.Dst P R →
        z ∈ Work.FlowerGlue2.Dst P R ∧
        (Work.FlowerGlue2.w0 P z).re ≤ (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z)).re - 1 / 2 := by
  obtain ⟨r₀, hr₀, C, hC, hstep⟩ := w0_step P hτ
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hrr : (0 : ℝ) < 1 / (2 * (C + 1)) := by
    apply div_pos one_pos; linarith
  refine ⟨min r₀ (1 / (2 * (C + 1))), lt_min hr₀ hrr, ?_⟩
  intro R z hz hzd hFtDst
  rw [mem_Dst] at hFtDst
  obtain ⟨hFtne, hrelt, himlt⟩ := hFtDst
  have hzd' : ‖z - d.z₁‖ < r₀ := lt_of_lt_of_le hzd (min_le_left _ _)
  have hzsm : ‖z - d.z₁‖ < 1 / (2 * (C + 1)) := lt_of_lt_of_le hzd (min_le_right _ _)
  obtain ⟨hFtne', herr⟩ := hstep z hz hzd'
  set e : ℂ := w0 P (Work.PARIMPL.Ft c₀ z) - w0 P z - 1 with he
  have hebound : ‖e‖ ≤ C * ‖z - d.z₁‖ := herr
  have he12 : ‖e‖ ≤ 1 / 2 := by
    calc ‖e‖ ≤ C * ‖z - d.z₁‖ := hebound
      _ ≤ C * (1 / (2 * (C + 1))) := mul_le_mul_of_nonneg_left (le_of_lt hzsm) hC
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
          linarith
  have hw : w0 P z = w0 P (Work.PARIMPL.Ft c₀ z) - 1 - e := by
    rw [he]; ring
  have hre : (w0 P z).re = (w0 P (Work.PARIMPL.Ft c₀ z)).re - 1 - e.re := by
    rw [hw]; simp
  have him : (w0 P z).im = (w0 P (Work.PARIMPL.Ft c₀ z)).im - e.im := by
    rw [hw]; simp
  have hre_e : -‖e‖ ≤ e.re := (abs_le.mp (Complex.abs_re_le_norm e)).1
  have him_e : |e.im| ≤ ‖e‖ := Complex.abs_im_le_norm e
  refine ⟨?_, ?_⟩
  · rw [mem_Dst]
    refine ⟨hz, ?_, ?_⟩
    · rw [hre]; linarith
    · rw [him, hre]
      calc |(w0 P (Work.PARIMPL.Ft c₀ z)).im - e.im|
          ≤ |(w0 P (Work.PARIMPL.Ft c₀ z)).im| + |e.im| := abs_sub _ _
        _ ≤ |(w0 P (Work.PARIMPL.Ft c₀ z)).im| + ‖e‖ := by linarith
        _ < (-(w0 P (Work.PARIMPL.Ft c₀ z)).re + 1) + ‖e‖ := by linarith
        _ ≤ -((w0 P (Work.PARIMPL.Ft c₀ z)).re - 1 - e.re) + 1 := by linarith
  · rw [hre]; linarith

end Work.FlowerGlue2
