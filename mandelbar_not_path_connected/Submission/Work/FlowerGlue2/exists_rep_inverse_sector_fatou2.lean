import Mathlib
import Submission.Work.FatouCoordFix.Repelling.ZDecay
import Submission.Work.FlowerGlue2.exists_conjugacy_Z_fine
import Submission.Work.FlowerGlue2.norm_Lambda_sub_Lambda_shift_le
import Submission.Work.FlowerGlue2.exists_preimage_of_lipschitz
import Submission.Work.FatouCoord.Repelling.norm_Lambda_sub_le
import Submission.Work.FatouCoord.Repelling.defect_lipschitz
import Submission.Work.FatouCoord.Flower.exists_threshold_log_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inverse of the repelling coordinate, with quantitative control

`Work.FlowerGlue2.exists_rep_inverse_sector_fatou2`.  On the far left half-plane
`{Re w < -R}` the repelling coordinate of the parabolic germ `f z = z + z^2 h z` is
`V w = w + (1 - a) Λ w + Z w` (`Λ w = log (-w) + π i`), a conjugacy between the shift
`w ↦ w + 1` and the chart dynamics `wMap f`; the correction `Z` decays like
`(1 + log ‖w‖)/‖w‖` (`Work.FlowerGlue2.exists_conjugacy_Z_fine`).  The new content of this file
is that `V` is *onto* the half-plane, with a quantitatively controlled inverse: every `w` with
`Re w < -R` has a preimage `v` with `Re v < -R` which is within `K (1 + log ‖w‖)/‖w‖` of the
formal inverse `w - (1 - a) Λ w`.

The hypothesis `a.re < 1` is exactly what makes the formal inverse work: writing `c = 1 - a` we
have `Re c > 0`, so `Re (w - c Λ w) ≤ Re w - (Re c) log ‖w‖ + O(1) < Re w` and the candidate
point stays on the far left.  The preimage is then produced by the contraction
`u ↦ u - (V (v₀ + u) - w)` (`Work.FlowerGlue2.exists_preimage_of_lipschitz`) on the ball of
radius `K (1 + log ‖w‖)/‖w‖` around `0`, whose Lipschitz constant is `‖c‖/R + 1/(R - R₀) < 1`
(from `norm_Z_sub_le` and `norm_Lambda_sub_le`); the radius is chosen so that the missing
`log`-order error `V v₀ - w = (1 - a)(Λ v₀ - Λ w) + Z v₀` fits inside it.
-/

open Filter Set Metric
open scoped Topology

set_option maxHeartbeats 1600000

namespace Work.FlowerGlue2

open Work.FatouCoord (Petal)
open Work.FatouCoord.Petal

/-! ## Elementary bounds for the branch `Λ w = log (-w) + π i` -/

lemma Lambda_re_im (w : ℂ) :
    (Petal.Lambda w).re = Real.log ‖w‖ ∧ 0 ≤ (Petal.Lambda w).im ∧
      (Petal.Lambda w).im ≤ 2 * Real.pi := by
  have hfun : Petal.Lambda w = Complex.log (-w) + (Real.pi : ℂ) * Complex.I := rfl
  have him : (Complex.log (-w) + (Real.pi : ℂ) * Complex.I).im = (-w).arg + Real.pi := by
    simp [Complex.log_im]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; simp [Complex.log_re, norm_neg]
  · rw [hfun, him]; linarith [Complex.neg_pi_lt_arg (-w)]
  · rw [hfun, him]; linarith [Complex.arg_le_pi (-w)]

lemma norm_Lambda_le' {w : ℂ} (h1 : 1 ≤ ‖w‖) :
    ‖Petal.Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := by
  have hbase : ‖Petal.Lambda w‖ ≤ ‖Complex.log (-w)‖ + Real.pi := by
    rw [show Petal.Lambda w = Complex.log (-w) + (Real.pi : ℂ) * Complex.I from rfl]
    calc ‖Complex.log (-w) + (Real.pi : ℂ) * Complex.I‖
        ≤ ‖Complex.log (-w)‖ + ‖(Real.pi : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = ‖Complex.log (-w)‖ + Real.pi := by rw [norm_mul, Complex.norm_I, mul_one]; simp
  have hlog : ‖Complex.log (-w)‖ ≤ Real.log ‖w‖ + Real.pi := by
    have h := Work.FatouCoord.Repelling.norm_log_le_abs_log_norm_add_abs_arg (-w)
    rw [norm_neg] at h
    have harg : |(-w).arg| ≤ Real.pi := Complex.abs_arg_le_pi _
    have hlogw : |Real.log ‖w‖| = Real.log ‖w‖ := abs_of_nonneg (Real.log_nonneg h1)
    linarith
  linarith

theorem exists_rep_inverse_sector_fatou2 {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (ha : a.re < 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ Z V : ℂ → ℂ,
      (∀ w : ℂ, w.re < -R → V w = w + (1 - a) * Work.FatouCoord.Petal.Lambda w + Z w) ∧
      (∀ w : ℂ, w.re < -R → V (w + 1) = Work.FatouCoord.wMap f (V w)) ∧
      Set.InjOn V {w : ℂ | w.re < -R} ∧
      (∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖) ∧
      (∀ w : ℂ, w.re < -R → V w ≠ 0) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, w.re < -R →
        ∃ v : ℂ, v.re < -R ∧ V v = w ∧
          ‖v - (w - (1 - a) * Work.FatouCoord.Petal.Lambda w)‖
            ≤ K * (1 + Real.log ‖w‖) / ‖w‖ := by
  obtain ⟨R₁, hR₁pos, hR₁r, Z, V, hZdiff, hZbd, hZfix, hVdiff, hVdef, hVconj, hVnorm, hVne,
    hVinj, hZdec⟩ := exists_conjugacy_Z_fine hb
  obtain ⟨K_Z, hK_Zpos, hK_Z⟩ := hZdec
  set c : ℝ := ‖(1 : ℂ) - a‖ with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; exact norm_nonneg _
  set d : ℝ := (1 - a).re with hddef
  have hdpos : 0 < d := by
    rw [hddef]; simp only [Complex.sub_re, Complex.one_re]; linarith
  set E : ℝ := |(1 - a).im| with hEdef
  have hEnn : 0 ≤ E := by rw [hEdef]; exact abs_nonneg _
  have hlog2pos : 0 < 1 + Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
  set Kb : ℝ := 16 * c ^ 2 + 4 * K_Z * (1 + Real.log 2) + 1 with hKbdef
  have hKbpos : 0 < Kb := by
    rw [hKbdef]
    have h1 : 0 ≤ 16 * c ^ 2 := by positivity
    have h2 : 0 ≤ 4 * K_Z * (1 + Real.log 2) := by nlinarith [hK_Zpos.le, hlog2pos]
    linarith
  obtain ⟨T₁, hT₁pos, hT₁⟩ := Work.FatouCoord.Flower.exists_threshold_log_div c
  obtain ⟨T₂, hT₂pos, hT₂⟩ := Work.FatouCoord.Flower.exists_threshold_log_div (2 * Kb)
  obtain ⟨T₄, hT₄pos, hT₄⟩ := norm_Lambda_sub_Lambda_shift_le ha
  set T₃ : ℝ := Real.exp ((2 * Real.pi * E + 1) / d + 1) with hT₃def
  have hT₃pos : 0 < T₃ := by rw [hT₃def]; exact Real.exp_pos _
  have hT₃key : 2 * Real.pi * E + 1 ≤ d * Real.log T₃ := by
    rw [hT₃def, Real.log_exp]
    have h : d * ((2 * Real.pi * E + 1) / d + 1) = 2 * Real.pi * E + 1 + d := by field_simp
    rw [h]; linarith
  let s : Finset ℝ := {R₁ + 4, T₁, T₂, T₃, T₄, 4 * c + 4, 4}
  have hsne : s.Nonempty := ⟨4, by simp [s]⟩
  set T : ℝ := s.max' hsne with hTdef
  have hle : ∀ x ∈ s, x ≤ T := fun x hx => by rw [hTdef]; exact Finset.le_max' s x hx
  have hR₁4 : R₁ + 4 ≤ T := hle (R₁ + 4) (by simp [s])
  have hT₁T : T₁ ≤ T := hle T₁ (by simp [s])
  have hT₂T : T₂ ≤ T := hle T₂ (by simp [s])
  have hT₃T : T₃ ≤ T := hle T₃ (by simp [s])
  have hT₄T : T₄ ≤ T := hle T₄ (by simp [s])
  have h4cT : 4 * c + 4 ≤ T := hle (4 * c + 4) (by simp [s])
  have h4T : (4 : ℝ) ≤ T := hle 4 (by simp [s])
  have hTpos : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hR₁T : R₁ < T := by linarith
  have hTlog : 2 * Real.pi * E + 1 ≤ d * Real.log T := by
    have h1 : Real.log T₃ ≤ Real.log T := Real.log_le_log hT₃pos hT₃T
    nlinarith [hT₃key, hdpos]
  have hKbT : Kb * (1 + Real.log T) ≤ T / 2 := by
    have h2 := hT₂ T hT₂T
    have h3 : Kb * (1 + Real.log T) ≤ Kb * (Real.log T + 2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hKbpos.le
    have h4 : Kb * (Real.log T + 2 * Real.pi) ≤ T / 4 := by linarith
    linarith
  refine ⟨T, hTpos, Z, V, ?_, ?_, ?_, ?_, ?_, ⟨Kb, hKbpos, ?_⟩⟩
  · intro w hw
    exact hVdef w (by rw [Petal.mem_LeftHalfPlane]; linarith)
  · intro w hw
    exact hVconj w (by rw [Petal.mem_LeftHalfPlane]; linarith)
  · refine hVinj.mono (fun w hw => ?_)
    rw [Petal.mem_LeftHalfPlane]
    simp only [Set.mem_ofPred_eq] at hw
    linarith
  · intro w hw
    exact hVnorm w (by rw [Petal.mem_LeftHalfPlane]; linarith)
  · intro w hw
    exact hVne w (by rw [Petal.mem_LeftHalfPlane]; linarith)
  · intro w hw
    have hwneg : w.re < 0 := by linarith
    have hwT : T < ‖w‖ := by
      have h := Complex.abs_re_le_norm w
      rw [abs_of_neg hwneg] at h
      linarith
    have hw1 : 1 ≤ ‖w‖ := by linarith
    have hlogw_nn : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw1
    have hwpos : 0 < ‖w‖ := by linarith
    have hLre := (Lambda_re_im w).1
    have hLim0 := (Lambda_re_im w).2.1
    have hLim2 := (Lambda_re_im w).2.2
    have hLnorm : ‖Petal.Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := norm_Lambda_le' hw1
    set v₀ : ℂ := w - (1 - a) * Petal.Lambda w with hv₀def
    have hv₀sub : v₀ - w = -((1 - a) * Petal.Lambda w) := by rw [hv₀def]; ring
    have hnorm_sub : ‖v₀ - w‖ ≤ c * (Real.log ‖w‖ + 2 * Real.pi) := by
      rw [hv₀sub, norm_neg, norm_mul, ← hcdef]
      exact mul_le_mul_of_nonneg_left hLnorm (norm_nonneg _)
    have hsmall : c * (Real.log ‖w‖ + 2 * Real.pi) ≤ ‖w‖ / 2 := by
      have h := hT₁ ‖w‖ (by linarith : T₁ ≤ ‖w‖)
      linarith
    have habs := abs_norm_sub_norm_le v₀ w
    rw [abs_le] at habs
    have hv₀ge : ‖w‖ / 2 ≤ ‖v₀‖ := by linarith [habs.1, hnorm_sub, hsmall]
    have hv₀le : ‖v₀‖ ≤ 2 * ‖w‖ := by linarith [habs.2, hnorm_sub, hsmall]
    have hRev₀ : v₀.re ≤ -T - 1 := by
      have h1 : v₀.re = w.re - ((1 - a) * Petal.Lambda w).re := by
        rw [hv₀def]; simp
      have h2 : ((1 - a) * Petal.Lambda w).re =
          d * Real.log ‖w‖ - (1 - a).im * (Petal.Lambda w).im := by
        rw [Complex.mul_re, hLre, ← hddef]
      have h3 : d * Real.log T ≤ d * Real.log ‖w‖ := by
        have h := Real.log_le_log hTpos hwT.le
        nlinarith [hdpos]
      have h4 : (1 - a).im * (Petal.Lambda w).im ≤ E * (2 * Real.pi) := by
        by_cases h : 0 ≤ (1 - a).im
        · have hE : (1 - a).im ≤ E := by rw [hEdef]; exact le_abs_self _
          nlinarith [hLim0, hLim2, hEnn, hE, Real.pi_pos.le]
        · have h' : (1 - a).im < 0 := not_le.mp h
          have h5 : (1 - a).im * (Petal.Lambda w).im ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h'.le hLim0
          nlinarith [hEnn, Real.pi_pos.le]
      have hv₀re : v₀.re = w.re - d * Real.log ‖w‖ + (1 - a).im * (Petal.Lambda w).im := by
        rw [h1, h2]; ring
      rw [hv₀re]
      linarith
    have hv₀memR₁ : v₀ ∈ Petal.LeftHalfPlane R₁ := by
      rw [Petal.mem_LeftHalfPlane]; linarith
    have hVv₀ : V v₀ = v₀ + (1 - a) * Petal.Lambda v₀ + Z v₀ := hVdef v₀ hv₀memR₁
    have hdiff : V v₀ - w = (1 - a) * (Petal.Lambda v₀ - Petal.Lambda w) + Z v₀ := by
      rw [hVv₀, hv₀def]; ring
    have hterm1 : ‖(1 - a) * (Petal.Lambda v₀ - Petal.Lambda w)‖ ≤
        8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ := by
      rw [norm_mul, ← hcdef]
      have h := hT₄ w (by linarith : w.re < -T₄)
      have h2 : c * (8 * c * (1 + Real.log ‖w‖) / ‖w‖) =
          8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ := by ring
      calc c * ‖Petal.Lambda v₀ - Petal.Lambda w‖
          ≤ c * (8 * c * (1 + Real.log ‖w‖) / ‖w‖) := mul_le_mul_of_nonneg_left h hcnn
        _ = 8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ := h2
    have hterm2 : ‖Z v₀‖ ≤ 2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖ := by
      have hZ := hK_Z v₀ hv₀memR₁
      have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hv₀pos : 0 < ‖v₀‖ := by linarith
      have h1 : 1 + Real.log ‖v₀‖ ≤ (1 + Real.log 2) * (1 + Real.log ‖w‖) := by
        have h2 : Real.log ‖v₀‖ ≤ Real.log 2 + Real.log ‖w‖ := by
          have h3 := Real.log_le_log hv₀pos hv₀le
          rw [Real.log_mul (by norm_num) (ne_of_gt hwpos)] at h3
          linarith
        have h4 : 0 ≤ Real.log 2 * Real.log ‖w‖ := mul_nonneg hlog2nn hlogw_nn
        nlinarith
      have h4 : 1 / ‖v₀‖ ≤ 2 / ‖w‖ := by
        have h5 := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < ‖w‖ / 2) hv₀ge
        have h6 : 1 / (‖w‖ / 2) = 2 / ‖w‖ := by
          rw [one_div, inv_div]
        linarith [h5, h6]
      have h5 : (1 + Real.log ‖v₀‖) / ‖v₀‖ ≤
          (1 + Real.log 2) * (1 + Real.log ‖w‖) * (2 / ‖w‖) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul h1 h4 (by positivity) (by positivity)
      calc ‖Z v₀‖ ≤ K_Z * (1 + Real.log ‖v₀‖) / ‖v₀‖ := hZ
        _ = K_Z * ((1 + Real.log ‖v₀‖) / ‖v₀‖) := by ring
        _ ≤ K_Z * ((1 + Real.log 2) * (1 + Real.log ‖w‖) * (2 / ‖w‖)) :=
            mul_le_mul_of_nonneg_left h5 hK_Zpos.le
        _ = 2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖ := by ring
    have hclose : ‖V v₀ - w‖ ≤ Kb * (1 + Real.log ‖w‖) / (2 * ‖w‖) := by
      have hsum : ‖(1 - a) * (Petal.Lambda v₀ - Petal.Lambda w) + Z v₀‖ ≤
          8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ +
            2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖ :=
        le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)
      have hfac : 8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ +
            2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖
          = (8 * c ^ 2 + 2 * K_Z * (1 + Real.log 2)) * ((1 + Real.log ‖w‖) / ‖w‖) := by
        ring
      have hKb2 : (8 * c ^ 2 + 2 * K_Z * (1 + Real.log 2)) * ((1 + Real.log ‖w‖) / ‖w‖)
          ≤ (Kb / 2) * ((1 + Real.log ‖w‖) / ‖w‖) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hKbdef]; linarith
      have hfin : (Kb / 2) * ((1 + Real.log ‖w‖) / ‖w‖) =
          Kb * (1 + Real.log ‖w‖) / (2 * ‖w‖) := by ring
      rw [hdiff]
      linarith [hsum, hfac, hKb2, hfin]
    set ρ : ℝ := Kb * (1 + Real.log ‖w‖) / ‖w‖ with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact div_pos (mul_pos hKbpos (by linarith)) hwpos
    have hρhalf : ρ ≤ 1 / 2 := by
      rw [hρdef]
      have h1 : (1 + Real.log ‖w‖) / ‖w‖ ≤ (1 + Real.log T) / T :=
        log_ratio_antitone hT1 hwT.le
      have h2 : Kb * ((1 + Real.log ‖w‖) / ‖w‖) ≤ Kb * ((1 + Real.log T) / T) :=
        mul_le_mul_of_nonneg_left h1 hKbpos.le
      have h3 : Kb * ((1 + Real.log T) / T) = Kb * (1 + Real.log T) / T := by ring
      have h4 : Kb * (1 + Real.log ‖w‖) / ‖w‖ = Kb * ((1 + Real.log ‖w‖) / ‖w‖) := by ring
      have h5 : Kb * ((1 + Real.log T) / T) ≤ 1 / 2 := by
        rw [h3, div_le_iff₀ hTpos]
        linarith [hKbT]
      rw [h4]
      linarith [h2]
    set κ : ℝ := c / T + 1 / (T - R₁) with hκdef
    have hκ0 : 0 ≤ κ := by
      rw [hκdef]
      have h1 : 0 ≤ c / T := div_nonneg hcnn hTpos.le
      have h2 : 0 ≤ 1 / (T - R₁) := div_nonneg (by norm_num) (by linarith)
      linarith
    have hκ1 : κ ≤ 1 / 2 := by
      rw [hκdef]
      have h1 : c / T ≤ 1 / 4 := by
        rw [div_le_iff₀ hTpos]; linarith
      have h2 : 1 / (T - R₁) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < T - R₁)]; linarith
      linarith
    have hκlt : κ < 1 := by linarith
    have hlip : ∀ x y : ℂ, dist x v₀ ≤ ρ → dist y v₀ ≤ ρ →
        ‖(V x - x) - (V y - y)‖ ≤ κ * ‖x - y‖ := by
      intro x y hx hy
      have hxT : x ∈ Petal.LeftHalfPlane T := by
        rw [Petal.mem_LeftHalfPlane]
        have h1 : x.re - v₀.re ≤ ‖x - v₀‖ := by
          have := Complex.re_le_norm (x - v₀); simpa [Complex.sub_re] using this
        have h2 : ‖x - v₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hx
        linarith [hRev₀, hρhalf]
      have hyT : y ∈ Petal.LeftHalfPlane T := by
        rw [Petal.mem_LeftHalfPlane]
        have h1 : y.re - v₀.re ≤ ‖y - v₀‖ := by
          have := Complex.re_le_norm (y - v₀); simpa [Complex.sub_re] using this
        have h2 : ‖y - v₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hy
        linarith [hRev₀, hρhalf]
      have hxR₁ : x ∈ Petal.LeftHalfPlane R₁ := by
        rw [Petal.mem_LeftHalfPlane] at hxT ⊢; linarith
      have hyR₁ : y ∈ Petal.LeftHalfPlane R₁ := by
        rw [Petal.mem_LeftHalfPlane] at hyT ⊢; linarith
      have hΛ := Work.FatouCoord.Repelling.norm_Lambda_sub_le hTpos hxT hyT
      have hZ := Work.FatouCoordFix.Repelling.norm_Z_sub_le hR₁pos hZdiff hZbd hR₁T hxT hyT
      rw [hVdef x hxR₁, hVdef y hyR₁]
      have h1 : ‖(1 - a) * (Petal.Lambda x - Petal.Lambda y)‖ ≤ c * (‖x - y‖ / T) := by
        rw [norm_mul, ← hcdef]
        exact mul_le_mul_of_nonneg_left hΛ (norm_nonneg _)
      have heq : (x + (1 - a) * Petal.Lambda x + Z x - x) -
            (y + (1 - a) * Petal.Lambda y + Z y - y)
          = (1 - a) * (Petal.Lambda x - Petal.Lambda y) + (Z x - Z y) := by ring
      calc ‖(x + (1 - a) * Petal.Lambda x + Z x - x) -
              (y + (1 - a) * Petal.Lambda y + Z y - y)‖
          = ‖(1 - a) * (Petal.Lambda x - Petal.Lambda y) + (Z x - Z y)‖ := by rw [heq]
        _ ≤ ‖(1 - a) * (Petal.Lambda x - Petal.Lambda y)‖ + ‖Z x - Z y‖ := norm_add_le _ _
        _ ≤ c * (‖x - y‖ / T) + (1 / (T - R₁)) * ‖x - y‖ := add_le_add h1 hZ
        _ = κ * ‖x - y‖ := by rw [hκdef]; ring
    have hclose' : ‖V v₀ - w‖ ≤ (1 - κ) * ρ := by
      have h1 : (1 / 2) * ρ ≤ (1 - κ) * ρ :=
        mul_le_mul_of_nonneg_right (by linarith) hρpos.le
      have h2 : ρ / 2 = Kb * (1 + Real.log ‖w‖) / (2 * ‖w‖) := by rw [hρdef]; ring
      have h3 : ‖V v₀ - w‖ ≤ ρ / 2 := by rw [h2]; exact hclose
      linarith
    obtain ⟨v, hvρ, hvV⟩ := exists_preimage_of_lipschitz hρpos hκ0 hκlt hlip hclose'
    refine ⟨v, ?_, hvV, ?_⟩
    · have h1 : v.re - v₀.re ≤ ‖v - v₀‖ := by
        have := Complex.re_le_norm (v - v₀); simpa [Complex.sub_re] using this
      have h2 : ‖v - v₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hvρ
      linarith [hRev₀, hρhalf]
    · calc ‖v - (w - (1 - a) * Petal.Lambda w)‖ = ‖v - v₀‖ := by rw [hv₀def]
        _ = dist v v₀ := by rw [dist_eq_norm]
        _ ≤ ρ := hvρ
        _ = Kb * (1 + Real.log ‖w‖) / ‖w‖ := hρdef

end Work.FlowerGlue2
