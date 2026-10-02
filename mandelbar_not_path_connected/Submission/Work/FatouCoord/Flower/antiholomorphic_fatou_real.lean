/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Anti.antiholomorphic_fatou

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The antiholomorphic Fatou coordinate, with `star a = a` as a hypothesis

This is `Work.FatouCoord.Anti.antiholomorphic_fatou` with the hypothesis
`f (star z) = star (f z)` replaced by the (strictly weaker, and in the Klein/antipolynomial
setting automatically true) hypothesis `star a = a`, where `a` is the Abel constant of the
germ.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Anti

noncomputable section

theorem antiholomorphic_fatou_real {f h g : ℂ → ℂ} {a : ℂ} {r A A' G : ℝ} (hb : ParabolicBounds f h a r A A') (ha : star a = a) (hg_anti : ∀ z ∈ ball 0 r, DifferentiableAt ℂ (fun z => star (g z)) z) (hgg : ∀ z ∈ ball 0 r, g (g z) = f z) (hg0 : g 0 = 0) (hg_lin : ∀ z ∈ ball 0 r, ‖g z - star z‖ ≤ G * ‖z‖ ^ 2) : ∃ (M : ℝ) (s : ℂ), 0 < M ∧ IsAntiholomorphicFatouOn g (fun z => fatouCoord f (1 - a) z + s) (Petal r M) ∧ Set.InjOn (fun z => fatouCoord f (1 - a) z + s) (Petal r M) := by
  have hr : 0 < r := hb.hr
  -- `h 0 = 1`
  have h00 : h 0 = 1 := by
    have hcl := hb.h_close 0 (mem_ball_zero_iff.mpr (show ‖(0:ℂ)‖ < r by simpa using hr))
    have h1 : ‖h 0 - 1‖ ≤ 0 := by simpa using hcl
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  have ha_real : star a = a := ha
  have hc : star (1 - a) = 1 - a := by rw [star_sub, star_one, ha_real]
  -- collect the pieces
  obtain ⟨N1, hN1pos, hrN1, hdiff⟩ := Exist.fatouCoordW_differentiable hb
  obtain ⟨N2, hN2pos, hrN2, habel⟩ := Exist.fatouCoordW_abel hb
  obtain ⟨N3, hN3pos, hrN3, hlim3⟩ := Work.FatouCoord.Anti.fatouCoordW_eq_lim hb
  obtain ⟨N4, hN4pos, hrN4, hinj⟩ := Exist.fatouCoordW_injOn hb
  obtain ⟨b, hb_tend⟩ := Work.FatouCoord.Anti.g_second_order_limit hr hg_anti hg0 hg_lin
  have hgW_tend : Tendsto (fun w : ℂ => gW g w - star w) (comap Complex.re atTop)
      (nhds (star b)) := gW_sub_tend hr hg_lin hb_tend
  have hlog_tend : Tendsto (fun w : ℂ => Complex.log (gW g w) - Complex.log (star w))
      (comap Complex.re atTop) (nhds 0) := gW_log_tend hr hg_lin hb_tend
  obtain ⟨M1, hM1pos, hgamma, hbb⟩ := gamma_eq hb hgg hg_lin hc hlim3 habel hgW_tend hlog_tend
  set s : ℂ := (1 / 2 - star b) / 2 with hsdef
  set MF : ℝ := max M1 (max N1 N4) + 1 with hMFdef
  have hM1MF : M1 < MF := by
    rw [hMFdef]; have := le_max_left M1 (max N1 N4); linarith
  have hN1MF : N1 < MF := by
    rw [hMFdef]; have h := le_max_left N1 N4
    have h2 := le_max_right M1 (max N1 N4); linarith
  have hN4MF : N4 < MF := by
    rw [hMFdef]; have h := le_max_right N1 N4
    have h2 := le_max_right M1 (max N1 N4); linarith
  have hMFpos : 0 < MF := by
    rw [hMFdef]; have := le_max_left M1 (max N1 N4); linarith
  refine ⟨MF, s, hMFpos, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (hg_anti z (Petal_subset_ball hz)).differentiableWithinAt
    · have hmaps : MapsTo chart (Petal r MF) {w : ℂ | N1 < w.re} := by
        intro z hz
        show N1 < (chart z).re
        have hz0 := ne_zero_of_mem_Petal hz
        have hns : 0 < Complex.normSq z := normSq_pos_of_mem_Petal hz
        rw [re_chart hz0, lt_div_iff₀ hns]
        nlinarith [hz.2, hns, hN1MF]
      have hchart : DifferentiableOn ℂ chart (Petal r MF) :=
        (differentiableOn_const (c := (-1 : ℂ))).div differentiableOn_id
          (fun z hz => ne_zero_of_mem_Petal hz)
      have hbase : DifferentiableOn ℂ (fun z => fatouCoord f (1 - a) z) (Petal r MF) :=
        hdiff.comp hchart hmaps
      exact hbase.add_const s
    · intro z hz
      have hz0 := ne_zero_of_mem_Petal hz
      have hns : 0 < Complex.normSq z := normSq_pos_of_mem_Petal hz
      have hzM1 : M1 < (chart z).re := by
        rw [re_chart hz0, lt_div_iff₀ hns]
        nlinarith [hz.2, hns, hM1MF]
      have hγ := hgamma (chart z) hzM1
      rw [gW_chart hz0] at hγ
      have h1 : fatouCoord f (1 - a) (g z) = star (fatouCoord f (1 - a) z) + star b := by
        rw [fatouCoord_eq, fatouCoord_eq]
        linear_combination hγ
      have hs : star b + s = star s + 1 / 2 := by
        have hs' : star s = (1 / 2 - b) / 2 := by
          rw [hsdef]
          simp only [star_div₀, star_sub, star_star]
          norm_num
        rw [hs', hsdef]
        linear_combination (1 / 2 : ℂ) * hbb
      show fatouCoord f (1 - a) (g z) + s = star (fatouCoord f (1 - a) z + s) + 1 / 2
      rw [h1, star_add]
      linear_combination hs
  · intro z1 hz1 z2 hz2 heq
    have hz10 := ne_zero_of_mem_Petal hz1
    have hz20 := ne_zero_of_mem_Petal hz2
    have hns1 : 0 < Complex.normSq z1 := normSq_pos_of_mem_Petal hz1
    have hns2 : 0 < Complex.normSq z2 := normSq_pos_of_mem_Petal hz2
    have hc1 : N4 < (chart z1).re := by
      rw [re_chart hz10, lt_div_iff₀ hns1]
      nlinarith [hz1.2, hns1, hN4MF]
    have hc2 : N4 < (chart z2).re := by
      rw [re_chart hz20, lt_div_iff₀ hns2]
      nlinarith [hz2.2, hns2, hN4MF]
    have heq' : fatouCoordW f (1 - a) (chart z1) = fatouCoordW f (1 - a) (chart z2) := by
      have h := heq
      simp only at h
      rw [fatouCoord_eq, fatouCoord_eq] at h
      exact add_right_cancel h
    exact chart_injective (hinj hc1 hc2 heq')


end

end Work.FatouCoord.Anti
