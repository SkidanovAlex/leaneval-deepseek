import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.box_lands_step
import Submission.Work.FlowerGlue2.incr_defs
import Submission.Work.FlowerGlue2.L0
import Submission.Work.FlowerGlue2.w0_step
import Submission.Work.FlowerGlue2.RepNormUncond
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Lavaurs.sum_inv_max_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal Ft gtc)


/-- The `c₀`-chart image of the flower's repelling coordinate: `u ↦ w₀ (Ψ u)`. -/
def psiW {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) (u : ℂ) : ℂ :=
  Work.PARIMPL2.w0 P (fl.Ψ u)

theorem psi_w0_re_le {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (H : ℝ) :
    ∃ R C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re < -R → |w.im| ≤ H →
      (Work.PARIMPL2.w0 P (fl.Ψ w)).re ≤ w.re + C * (1 + Real.log (2 + ‖w‖)) := by
  -- ## the local step estimate of the chart
  have hτ : P.h c₀ 0 = 1 := Work.FlowerGlue2.tau_c₀ P
  obtain ⟨r, hr, C, hC, hstep⟩ := Work.FlowerGlue2.w0_step P hτ
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hSpos : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs
  -- ## the smallness threshold for `Ψ`
  set ε : ℝ := min r (1 / (2 * (C + 1))) with hεdef
  have hεpos : 0 < ε := lt_min hr (by positivity)
  have hεr : ε ≤ r := min_le_left _ _
  have hCε : C * ε ≤ 1 / 2 := by
    have h1 : C * ε ≤ C * (1 / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    have h2 : C * (1 / (2 * (C + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))]
      linarith
    linarith
  obtain ⟨Rsm, hRsm⟩ := fl.Ψ_small ε hεpos
  set S : ℝ := ‖P.s c₀‖ with hSdef
  have hSpos' : 0 < S := hSpos
  set κ : ℝ := S / ε with hκdef
  have hκpos : 0 < κ := div_pos hSpos' hεpos
  -- ## the fixed reference depth
  set X : ℝ := max (Rsm + 2) 4 with hXdef
  have hXge : Rsm + 2 ≤ X := le_max_left _ _
  have hX4 : 4 ≤ X := le_max_right _ _
  -- ## pointwise facts about `psiW` on the far left
  have hfar_ne : ∀ u : ℂ, u.re < -Rsm → fl.Ψ u ≠ d.z₁ := fun u hu => (hRsm u hu).1
  have hfar_sm : ∀ u : ℂ, u.re < -Rsm → ‖fl.Ψ u - d.z₁‖ < ε := fun u hu => (hRsm u hu).2
  have hfar_pos : ∀ u : ℂ, u.re < -Rsm → 0 < ‖fl.Ψ u - d.z₁‖ :=
    fun u hu => norm_pos_iff.mpr (sub_ne_zero.mpr (hfar_ne u hu))
  have hWnorm_eq : ∀ u : ℂ, u.re < -Rsm → ‖psiW P fl u‖ = S / ‖fl.Ψ u - d.z₁‖ := by
    intro u _
    simp only [psiW, Work.PARIMPL2.w0, hSdef, norm_div, norm_neg]
  have hWge : ∀ u : ℂ, u.re < -Rsm → κ ≤ ‖psiW P fl u‖ := by
    intro u hu
    rw [hWnorm_eq u hu, hκdef]
    exact div_le_div_of_nonneg_left (le_of_lt hSpos') (hfar_pos u hu) (le_of_lt (hfar_sm u hu))
  have hΨ_norm : ∀ u : ℂ, u.re < -Rsm → ‖fl.Ψ u - d.z₁‖ = S / ‖psiW P fl u‖ := by
    intro u hu
    have h1 : S / ‖psiW P fl u‖ = ‖fl.Ψ u - d.z₁‖ := by
      rw [hWnorm_eq u hu]
      field_simp [ne_of_gt hSpos', ne_of_gt (hfar_pos u hu)]
    exact h1.symm
  -- ## the one-step error bounds
  have herr_norm : ∀ u : ℂ, u.re < -Rsm →
      ‖psiW P fl (u + 1) - psiW P fl u - 1‖ ≤ C * S / ‖psiW P fl u‖ := by
    intro u hu
    obtain ⟨-, herr⟩ := hstep (fl.Ψ u) (hfar_ne u hu) (lt_of_lt_of_le (hfar_sm u hu) hεr)
    have hshift : fl.Ψ (u + 1) = Ft c₀ (fl.Ψ u) := fl.Ψ_shift u
    have h2 : ‖psiW P fl (u + 1) - psiW P fl u - 1‖ ≤ C * ‖fl.Ψ u - d.z₁‖ := by
      simpa only [psiW, hshift, Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using herr
    rw [hΨ_norm u hu] at h2
    calc ‖psiW P fl (u + 1) - psiW P fl u - 1‖ ≤ C * (S / ‖psiW P fl u‖) := h2
      _ = C * S / ‖psiW P fl u‖ := by ring
  have hstep_max : ∀ u : ℂ, u.re < -Rsm →
      ‖psiW P fl (u + 1) - psiW P fl u - 1‖ ≤ (C * S) / max κ |(psiW P fl u).re| := by
    intro u hu
    refine le_trans (herr_norm u hu) ?_
    have hmaxpos : 0 < max κ |(psiW P fl u).re| := lt_of_lt_of_le hκpos (le_max_left _ _)
    have hmaxle : max κ |(psiW P fl u).re| ≤ ‖psiW P fl u‖ :=
      max_le (hWge u hu) (Complex.abs_re_le_norm _)
    exact div_le_div_of_nonneg_left (by positivity) hmaxpos hmaxle
  have hstep_half : ∀ u : ℂ, u.re < -Rsm →
      ‖psiW P fl (u + 1) - psiW P fl u - 1‖ ≤ 1 / 2 := by
    intro u hu
    refine le_trans (herr_norm u hu) ?_
    have h1 : C * S / ‖psiW P fl u‖ ≤ C * S / κ :=
      div_le_div_of_nonneg_left (by positivity) hκpos (hWge u hu)
    have h2 : C * S / κ = C * ε := by
      rw [hκdef]; field_simp
    linarith [hCε, h1, le_of_eq h2]
  -- ## the reference box and its bounds
  set Kbox : Set ℂ := {u : ℂ | u.re ∈ Set.Icc (-X) (-X + 1) ∧ u.im ∈ Set.Icc (-H) H} with hKbox
  have hKbox_compact : IsCompact Kbox := by
    have hclosed : IsClosed Kbox := by
      rw [hKbox]
      exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (|X| + |H| + 2)) hclosed ?_
    intro u hu
    rw [hKbox] at hu
    have hre : u.re ∈ Set.Icc (-X) (-X + 1) := hu.1
    have him : u.im ∈ Set.Icc (-H) H := hu.2
    rw [Set.mem_Icc] at hre him
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |u.re| ≤ |X| + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hre.1, le_abs_self X], by linarith [hre.2, neg_le_abs X]⟩
    have h2 : |u.im| ≤ |H| :=
      abs_le.mpr ⟨by linarith [him.1, le_abs_self H], by linarith [him.2, le_abs_self H]⟩
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ |X| + 1 + |H| := by linarith
      _ ≤ |X| + |H| + 2 := by linarith
  have hKbox_far : ∀ u ∈ Kbox, u.re < -Rsm := by
    intro u hu
    have h1 : u.re ≤ -X + 1 := hu.1.2
    have h2 : -X + 1 ≤ -Rsm - 1 := by linarith [hXge]
    linarith
  have hKbox_cont : ContinuousOn (fun u : ℂ => (psiW P fl u).re) Kbox := by
    have hΨc : Continuous (fun u : ℂ => fl.Ψ u) := fl.Ψ_diff.continuous
    have hw0c : ContinuousOn (fun v : ℂ => Work.PARIMPL2.w0 P v) {v : ℂ | v ≠ d.z₁} := by
      have h : ContinuousOn (fun v : ℂ => -P.s c₀ / (v - d.z₁)) {v : ℂ | v ≠ d.z₁} :=
        continuousOn_const.div (continuousOn_id.sub continuousOn_const)
          (fun v hv => sub_ne_zero.mpr hv)
      simpa only [Work.PARIMPL2.w0] using h
    have hmaps : MapsTo (fun u : ℂ => fl.Ψ u) Kbox {v : ℂ | v ≠ d.z₁} :=
      fun u hu => hfar_ne u (hKbox_far u hu)
    have hcomp : ContinuousOn (fun u : ℂ => Work.PARIMPL2.w0 P (fl.Ψ u)) Kbox :=
      hw0c.comp hΨc.continuousOn hmaps
    have hcont2 : ContinuousOn (fun u : ℂ => (Work.PARIMPL2.w0 P (fl.Ψ u)).re) Kbox :=
      Complex.continuous_re.comp_continuousOn hcomp
    exact hcont2
  obtain ⟨BUp, hBUp⟩ : ∃ B : ℝ, ∀ u ∈ Kbox, (psiW P fl u).re ≤ B := by
    obtain ⟨B, hB⟩ := (hKbox_compact.image_of_continuousOn hKbox_cont).bddAbove
    exact ⟨B, fun u hu => hB (Set.mem_image_of_mem _ hu)⟩
  obtain ⟨BLo, hBLo⟩ : ∃ B : ℝ, ∀ u ∈ Kbox, B ≤ (psiW P fl u).re := by
    obtain ⟨B, hB⟩ := (hKbox_compact.image_of_continuousOn hKbox_cont).bddBelow
    exact ⟨B, fun u hu => hB (Set.mem_image_of_mem _ hu)⟩
  set Babs : ℝ := max (max BUp (-BLo)) 0 with hBabsdef
  have hBabs : 0 ≤ Babs := le_max_right _ _
  -- ## the harmonic-sum input
  obtain ⟨K0, hK0nn, hK0⟩ := sum_inv_max_le (κ := κ) (Babs := Babs) hκpos hBabs
  have hX4pos : 0 < X + 4 := by linarith
  have hlogX4 : 0 ≤ Real.log (X + 4) := Real.log_nonneg (by linarith)
  -- ## the constants of the conclusion
  set Rf : ℝ := X + 1 with hRfdef
  set Cf : ℝ := max 0 (X + BUp) + (C * S) * K0 * (1 + Real.log (X + 4)) + 1 with hCfdef
  have hCf_nonneg : 0 ≤ Cf := by
    rw [hCfdef]
    have h1 : 0 ≤ max 0 (X + BUp) := le_max_left _ _
    have h2 : 0 ≤ (C * S) * K0 * (1 + Real.log (X + 4)) :=
      mul_nonneg (mul_nonneg (by positivity) hK0nn) (by linarith)
    linarith
  refine ⟨Rf, Cf, hCf_nonneg, ?_⟩
  intro w hw hwim
  -- ## the number of steps to the reference box
  set m : ℕ := Nat.ceil (-X - w.re) with hmdef
  have hwR : w.re < -X - 1 := by rw [hRfdef] at hw; linarith
  have hXR : 0 ≤ -X - w.re := by linarith
  have hm_ge : -X - w.re ≤ (m : ℝ) := Nat.le_ceil _
  have hm_lt : (m : ℝ) < -X - w.re + 1 := Nat.ceil_lt_add_one hXR
  have hcast_re : ∀ j : ℕ, (w + ((j : ℕ) : ℂ)).re = w.re + (j : ℝ) := fun j => by simp
  have hcast_im : ∀ j : ℕ, (w + ((j : ℕ) : ℂ)).im = w.im := fun j => by simp
  have hfar_j : ∀ j : ℕ, j ≤ m → (w + ((j : ℕ) : ℂ)).re < -Rsm := by
    intro j hj
    rw [hcast_re j]
    have h1 : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
    have h2 : w.re + (m : ℝ) < -X + 1 := by linarith [hm_lt]
    linarith [hXge]
  -- ## the sequence and its bounds
  set a : ℕ → ℝ := fun j => (psiW P fl (w + ((j : ℕ) : ℂ))).re with hadef
  have ha_eq : ∀ j : ℕ, a j = (psiW P fl (w + ((j : ℕ) : ℂ))).re := fun j => rfl
  set E : ℕ → ℂ :=
    fun j => psiW P fl ((w + ((j : ℕ) : ℂ)) + 1) - psiW P fl (w + ((j : ℕ) : ℂ)) - 1
    with hEdef
  have hE_re : ∀ j : ℕ, a (j + 1) - a j = 1 + (E j).re := by
    intro j
    have hcast1 : w + (((j + 1 : ℕ)) : ℂ) = (w + ((j : ℕ) : ℂ)) + 1 := by push_cast; ring
    have hsplit : psiW P fl ((w + ((j : ℕ) : ℂ)) + 1)
        = psiW P fl (w + ((j : ℕ) : ℂ)) + 1 + E j := by
      simp only [hEdef]; ring
    rw [ha_eq (j + 1), ha_eq j, hcast1, hsplit]
    simp only [Complex.add_re, Complex.one_re]
    ring
  have hmono : ∀ j, j < m → a (j + 1) - a j ≥ 1 / 2 := by
    intro j hj
    have hu : (w + ((j : ℕ) : ℂ)).re < -Rsm := hfar_j j (le_of_lt hj)
    have hh := hstep_half (w + ((j : ℕ) : ℂ)) hu
    have hre : -(1 / 2 : ℝ) ≤ (E j).re := by
      have h1 : |(E j).re| ≤ ‖E j‖ := Complex.abs_re_le_norm (E j)
      have h2 := abs_le.mp (le_trans h1 hh)
      linarith [h2.1]
    rw [hE_re j]
    linarith
  have hmem_box : w + ((m : ℕ) : ℂ) ∈ Kbox := by
    rw [hKbox]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hcast_re m]; linarith [hm_ge]
    · rw [hcast_re m]; linarith [hm_lt]
    · rw [hcast_im m]; exact abs_le.mp hwim
  have ham_up : a m ≤ BUp := by
    have h := hBUp (w + ((m : ℕ) : ℂ)) hmem_box
    exact h
  have ham_lo : BLo ≤ a m := by
    have h := hBLo (w + ((m : ℕ) : ℂ)) hmem_box
    exact h
  have ham : |a m| ≤ Babs := by
    have h1 : a m ≤ Babs := le_trans ham_up (le_trans (le_max_left _ _) (le_max_left _ _))
    have h2 : -a m ≤ Babs :=
      le_trans (neg_le_neg ham_lo) (le_trans (le_max_right _ _) (le_max_left _ _))
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  -- ## the harmonic sum
  have hsum := hK0 a m hmono ham
  -- ## the error sum
  have herr_sum : ∑ j ∈ Finset.range m, ‖E j‖ ≤ (C * S) * (K0 * (1 + Real.log (2 + (m : ℝ)))) := by
    have h1 : ∀ j ∈ Finset.range m, ‖E j‖ ≤ (C * S) * (max κ |a j|)⁻¹ := by
      intro j hj
      have hjlt : j < m := Finset.mem_range.mp hj
      have hu : (w + ((j : ℕ) : ℂ)).re < -Rsm := hfar_j j (le_of_lt hjlt)
      have h := hstep_max (w + ((j : ℕ) : ℂ)) hu
      have hrej : (psiW P fl (w + ((j : ℕ) : ℂ))).re = a j := (ha_eq j).symm
      rw [hrej, div_eq_mul_inv] at h
      exact h
    calc ∑ j ∈ Finset.range m, ‖E j‖
        ≤ ∑ j ∈ Finset.range m, (C * S) * (max κ |a j|)⁻¹ := Finset.sum_le_sum h1
      _ = (C * S) * ∑ j ∈ Finset.range m, (max κ |a j|)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (C * S) * (K0 * (1 + Real.log (2 + (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  -- ## telescoping
  have hterm : ∀ j, j < m → 1 - ‖E j‖ ≤ a (j + 1) - a j := by
    intro j hj
    rw [hE_re j]
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (E j))).1
    linarith
  have htel : ∑ j ∈ Finset.range m, (a (j + 1) - a j) = a m - a 0 :=
    Finset.sum_range_sub a m
  have hsplit_sum : ∑ j ∈ Finset.range m, (1 - ‖E j‖)
      = (m : ℝ) - ∑ j ∈ Finset.range m, ‖E j‖ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    norm_num
  have htel_lower : (m : ℝ) - ∑ j ∈ Finset.range m, ‖E j‖ ≤ a m - a 0 := by
    rw [← htel, ← hsplit_sum]
    exact Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
  have ha0 : a 0 ≤ w.re + X + BUp + (C * S) * (K0 * (1 + Real.log (2 + (m : ℝ)))) := by
    have h1 : -(m : ℝ) ≤ w.re + X := by linarith [hm_ge]
    linarith [htel_lower, ham_up, h1, herr_sum]
  -- ## the logarithmic comparison
  have hlogcmp : Real.log (2 + (m : ℝ)) ≤ Real.log (X + 4) + Real.log (2 + ‖w‖) := by
    have hnorm : -w.re ≤ ‖w‖ := le_trans (neg_le_abs w.re) (Complex.abs_re_le_norm w)
    have hl : 2 + (m : ℝ) ≤ 3 - X + ‖w‖ := by linarith [hm_lt, hnorm]
    have hmul : 3 - X + ‖w‖ ≤ (X + 4) * (2 + ‖w‖) := by
      have h1 : 0 ≤ ‖w‖ := norm_nonneg w
      nlinarith [hX4, h1]
    have hp1 : 0 < 2 + (m : ℝ) := by positivity
    have hp2 : 0 < X + 4 := hX4pos
    have hp3 : 0 < 2 + ‖w‖ := by positivity
    calc Real.log (2 + (m : ℝ)) ≤ Real.log ((X + 4) * (2 + ‖w‖)) :=
          Real.log_le_log hp1 (le_trans hl hmul)
      _ = Real.log (X + 4) + Real.log (2 + ‖w‖) := Real.log_mul (ne_of_gt hp2) (ne_of_gt hp3)
  -- ## the final assembly
  have hgoal : a 0 ≤ w.re + Cf * (1 + Real.log (2 + ‖w‖)) := by
    have hCSK : (0 : ℝ) ≤ (C * S) * K0 := mul_nonneg (by positivity) hK0nn
    have hlogw : (0 : ℝ) ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
    have h1 : (C * S) * (K0 * (1 + Real.log (2 + (m : ℝ))))
        ≤ (C * S) * K0 * (1 + Real.log (X + 4)) + (C * S) * K0 * Real.log (2 + ‖w‖) := by
      have h2 : (C * S) * (K0 * (1 + Real.log (2 + (m : ℝ))))
          = (C * S) * K0 * (1 + Real.log (2 + (m : ℝ))) := by ring
      rw [h2]
      have h3 : (1 + Real.log (2 + (m : ℝ)))
          ≤ 1 + Real.log (X + 4) + Real.log (2 + ‖w‖) := by linarith [hlogcmp]
      have h4 : (C * S) * K0 * (1 + Real.log (2 + (m : ℝ)))
          ≤ (C * S) * K0 * (1 + Real.log (X + 4) + Real.log (2 + ‖w‖)) :=
        mul_le_mul_of_nonneg_left h3 hCSK
      have h5 : (C * S) * K0 * (1 + Real.log (X + 4) + Real.log (2 + ‖w‖))
          = (C * S) * K0 * (1 + Real.log (X + 4)) + (C * S) * K0 * Real.log (2 + ‖w‖) := by
        ring
      linarith [h4, h5]
    have h2 : X + BUp + (C * S) * K0 * (1 + Real.log (X + 4)) ≤ Cf := by
      have h3 : X + BUp ≤ max 0 (X + BUp) := le_max_right _ _
      have h4 : (0 : ℝ) ≤ (C * S) * K0 * (1 + Real.log (X + 4)) :=
        mul_nonneg (mul_nonneg (by positivity) hK0nn) (by linarith)
      linarith [hCfdef]
    have h3 : (C * S) * K0 ≤ Cf := by
      have h4 : (C * S) * K0 ≤ (C * S) * K0 * (1 + Real.log (X + 4)) := by
        nlinarith [hCSK, hlogX4]
      have h5 : (C * S) * K0 * (1 + Real.log (X + 4)) ≤ Cf := by
        have h6 : (0 : ℝ) ≤ max 0 (X + BUp) := le_max_left _ _
        linarith [hCfdef]
      linarith
    have h4 : (C * S) * K0 * Real.log (2 + ‖w‖) ≤ Cf * Real.log (2 + ‖w‖) :=
      mul_le_mul_of_nonneg_right h3 hlogw
    have h5 : a 0 ≤ w.re + (X + BUp) + (C * S) * K0 * (1 + Real.log (X + 4))
        + (C * S) * K0 * Real.log (2 + ‖w‖) := by linarith [ha0, h1]
    linarith [h5, h2, h4]
  have ha0w : a 0 = (Work.PARIMPL2.w0 P (fl.Ψ w)).re := by
    simp only [ha_eq, psiW, Nat.cast_zero, add_zero]
  rwa [ha0w] at hgoal

end Work.PARIMPL2.Lavaurs
