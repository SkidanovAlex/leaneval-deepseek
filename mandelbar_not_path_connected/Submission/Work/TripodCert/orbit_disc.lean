import Mathlib
import Submission.Work.TripodCert.UniqueDefs
import Submission.Work.TripodCert.norm_Tsq_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

/-!
# `orbit_disc` — the three orbit points of the uniqueness disc stay in the disc `E`

This module collects the elementary Lipschitz/parameter-variation estimates that show that the
first three points of the `Tsq`-orbit of any `z` in the uniqueness disc `D` (`‖z - z₀‖ ≤ uRUr`)
of any parameter `c` of the certified box `Xb` again lie in the disc `E` of radius `UREq = 1/20`
about `z₀`, together with the two corresponding statements for the centre `c₀` of the box.

The ingredients are

* `norm_Tsq_sub_le` (a colleague's lemma): `Tsq` is Lipschitz with the explicit factor
  `‖z - w‖ * (‖z‖ + ‖w‖) * (‖z‖² + ‖w‖² + 2‖c‖)`;
* `norm_Tsq_sub_le_param`: the variation of `Tsq` in the parameter at fixed `z`,
  `Tsq c z - Tsq d z = (c̄ - d̄)(2z² + c̄ + d̄) + (c - d)`;
* the numerical data of `UniqueDefs.lean` (`UMq`, `UCmq`, `Ur1q`, `Ur0q`, `hUr1`, `hUr1E`, ...).
-/

/-- **Parameter variation of `Tsq` at fixed `z`.**  Since `Tsq c z = (z² + c̄)² + c`, the
difference in the parameter factors through `c̄ - d̄`. -/
theorem norm_Tsq_sub_le_param (c d z : ℂ) :
    ‖Work.Landing.Tsq c z - Work.Landing.Tsq d z‖
      ≤ ‖c - d‖ * (2 * ‖z‖ ^ 2 + ‖c‖ + ‖d‖ + 1) := by
  have hid : Work.Landing.Tsq c z - Work.Landing.Tsq d z
      = (star c - star d) * ((2 : ℂ) * z ^ 2 + star c + star d) + (c - d) := by
    unfold Work.Landing.Tsq; ring
  rw [hid]
  have hnorm : ‖star c - star d‖ = ‖c - d‖ := by rw [← star_sub, norm_star]
  have h2 : ‖(2 : ℂ) * z ^ 2 + star c + star d‖ ≤ 2 * ‖z‖ ^ 2 + ‖c‖ + ‖d‖ := by
    calc ‖(2 : ℂ) * z ^ 2 + star c + star d‖
        ≤ ‖(2 : ℂ) * z ^ 2 + star c‖ + ‖star d‖ := norm_add_le _ _
      _ ≤ (‖(2 : ℂ) * z ^ 2‖ + ‖star c‖) + ‖star d‖ := by
          gcongr; exact norm_add_le _ _
      _ = 2 * ‖z‖ ^ 2 + ‖c‖ + ‖d‖ := by
          rw [norm_mul, norm_star, norm_star]; norm_num
  calc ‖(star c - star d) * ((2 : ℂ) * z ^ 2 + star c + star d) + (c - d)‖
      ≤ ‖(star c - star d) * ((2 : ℂ) * z ^ 2 + star c + star d)‖ + ‖c - d‖ :=
        norm_add_le _ _
    _ = ‖star c - star d‖ * ‖(2 : ℂ) * z ^ 2 + star c + star d‖ + ‖c - d‖ := by rw [norm_mul]
    _ ≤ ‖c - d‖ * (2 * ‖z‖ ^ 2 + ‖c‖ + ‖d‖) + ‖c - d‖ := by
        rw [hnorm]
        gcongr
    _ = ‖c - d‖ * (2 * ‖z‖ ^ 2 + ‖c‖ + ‖d‖ + 1) := by ring

/-- **`Tsq` is Lipschitz on the ambient disc** `‖z‖, ‖w‖ ≤ UMq`, with constant
`UN0q * UN1q = 2·UMq·(2·UMq² + 2·UCmq)`: this is `norm_Tsq_sub_le` with the numerical
bounds `‖z‖ + ‖w‖ ≤ UN0q` and `‖z‖² + ‖w‖² + 2‖c‖ ≤ UN1q`. -/
theorem Tsq_sub_le_UMq {c z w : ℂ} (hc : ‖c‖ ≤ (UCmq : ℝ))
    (hz : ‖z‖ ≤ (UMq : ℝ)) (hw : ‖w‖ ≤ (UMq : ℝ)) :
    ‖Work.Landing.Tsq c z - Work.Landing.Tsq c w‖
      ≤ ‖z - w‖ * (UN0q : ℝ) * (UN1q : ℝ) := by
  have h := norm_Tsq_sub_le c z w
  have h1 : ‖z‖ + ‖w‖ ≤ (UN0q : ℝ) := by
    have : (UN0q : ℚ) = 2 * UMq := rfl
    rw [this]; push_cast; linarith
  have h2 : ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * ‖c‖ ≤ (UN1q : ℝ) := by
    have : (UN1q : ℚ) = 2 * UMq * UMq + 2 * UCmq := rfl
    rw [this]; push_cast
    have hzU : (0 : ℝ) ≤ (UMq : ℝ) := by norm_num [UMq]
    have hz0 := norm_nonneg z
    have hw0 := norm_nonneg w
    nlinarith [sq_nonneg (‖z‖ - (UMq : ℝ)), sq_nonneg (‖w‖ - (UMq : ℝ)), hz, hw, hc]
  have hUN0 : (0 : ℝ) ≤ (UN0q : ℝ) := by norm_num [UN0q, UMq]
  calc ‖Work.Landing.Tsq c z - Work.Landing.Tsq c w‖
      ≤ ‖z - w‖ * (‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * ‖c‖) := h
    _ ≤ ‖z - w‖ * (UN0q : ℝ) * (UN1q : ℝ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        · exact h2
        · positivity
        · exact mul_nonneg (norm_nonneg _) hUN0

/-- The radius comparison `uRUr ≤ UREq = 1/20`. -/
theorem uRUr_le_UREq : uRUr ≤ (UREq : ℝ) := by
  norm_num [uRUr, uRUq, UREq, Q, MS, URmU]

/-- The drift comparison `Ud0q = 1/20000 ≤ UREq = 1/20`. -/
theorem Ud0q_le_UREq : (Ud0q : ℝ) ≤ (UREq : ℝ) := by norm_num [Ud0q, UREq]

/-- `‖z₀‖ ≤ UMq`. -/
theorem hUMz0 : ‖uZ0‖ ≤ (UMq : ℝ) := by
  have h := hUM0
  have : (0 : ℝ) ≤ (UREq : ℝ) := by norm_num [UREq]
  push_cast at h ⊢
  linarith

/-- `‖c₀‖ ≤ UCmq`. -/
theorem hUc0T : ‖c0T‖ ≤ (UCmq : ℝ) := by
  have h := hUc0
  have hUD : (0 : ℝ) ≤ (UDcq : ℝ) := by norm_num [UDcq, Q, MS, RADM]
  linarith

/-- `Tsq` at any parameter of the box displaces `z₀` by at most `Ur0q`. -/
theorem Tsq_c_uZ0_sub_le {c : ℂ} (hc : Xb.mem c) :
    ‖Work.Landing.Tsq c uZ0 - uZ0‖ ≤ (Ur0q : ℝ) := by
  have hpar := norm_Tsq_sub_le_param c c0T uZ0
  have hcd := hDc hc
  have hcU := hUCm hc
  have hc0U := hUc0T
  have hzU := hUMz0
  have hf : 2 * ‖uZ0‖ ^ 2 + ‖c‖ + ‖c0T‖ + 1
      ≤ ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) := by
    push_cast
    nlinarith [norm_nonneg uZ0]
  have hUD : (0 : ℝ) ≤ (UDcq : ℝ) := by norm_num [UDcq, Q, MS, RADM]
  have hmain : ‖Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0‖
      ≤ ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) * (UDcq : ℝ) := by
    calc ‖Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0‖
        ≤ ‖c - c0T‖ * (2 * ‖uZ0‖ ^ 2 + ‖c‖ + ‖c0T‖ + 1) := hpar
      _ ≤ (UDcq : ℝ) * ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) := by
          apply mul_le_mul hcd hf
          · push_cast; positivity
          · exact hUD
      _ = ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) * (UDcq : ℝ) := by ring
  calc ‖Work.Landing.Tsq c uZ0 - uZ0‖
      ≤ ‖Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0‖
          + ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ := by
        rw [show Work.Landing.Tsq c uZ0 - uZ0
            = (Work.Landing.Tsq c uZ0 - Work.Landing.Tsq c0T uZ0)
              + (Work.Landing.Tsq c0T uZ0 - uZ0) by ring]
        exact norm_add_le _ _
    _ ≤ ((2 * UMq * UMq + 2 * UCmq + 1 : ℚ) : ℝ) * (UDcq : ℝ) + (Ud0q : ℝ) :=
        add_le_add hmain hUd0
    _ = (Ur0q : ℝ) := by simp only [Ur0q]; push_cast; ring

/-- **One `Tsq`-step at a parameter `c ∈ Xb`.**  For `‖z‖ ≤ UMq`,
`‖Tsq c z - z₀‖ ≤ ‖z - z₀‖ · UN0q · UN1q + Ur0q`. -/
theorem Tsq_step_le {c z : ℂ} (hc : Xb.mem c) (hz : ‖z‖ ≤ (UMq : ℝ)) :
    ‖Work.Landing.Tsq c z - uZ0‖
      ≤ ‖z - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ) + (Ur0q : ℝ) := by
  have hlip := Tsq_sub_le_UMq (hUCm hc) hz hUMz0
  have hsub := Tsq_c_uZ0_sub_le hc
  calc ‖Work.Landing.Tsq c z - uZ0‖
      ≤ ‖Work.Landing.Tsq c z - Work.Landing.Tsq c uZ0‖
          + ‖Work.Landing.Tsq c uZ0 - uZ0‖ := by
        rw [show Work.Landing.Tsq c z - uZ0
            = (Work.Landing.Tsq c z - Work.Landing.Tsq c uZ0)
              + (Work.Landing.Tsq c uZ0 - uZ0) by ring]
        exact norm_add_le _ _
    _ ≤ ‖z - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ) + (Ur0q : ℝ) := add_le_add hlip hsub

/-- **One `Tsq`-step at the centre `c₀` of the box.**  Here the parameter does not vary, so the
displacement of `z₀` itself is bounded by the numerical drift `Ud0q = 1/20000`. -/
theorem Tsq_step_c0T_le {z : ℂ} (hz : ‖z‖ ≤ (UMq : ℝ)) :
    ‖Work.Landing.Tsq c0T z - uZ0‖
      ≤ ‖z - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ) + (Ud0q : ℝ) := by
  have hlip := Tsq_sub_le_UMq hUc0T hz hUMz0
  calc ‖Work.Landing.Tsq c0T z - uZ0‖
      ≤ ‖Work.Landing.Tsq c0T z - Work.Landing.Tsq c0T uZ0‖
          + ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ := by
        rw [show Work.Landing.Tsq c0T z - uZ0
            = (Work.Landing.Tsq c0T z - Work.Landing.Tsq c0T uZ0)
              + (Work.Landing.Tsq c0T uZ0 - uZ0) by ring]
        exact norm_add_le _ _
    _ ≤ ‖z - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ) + (Ud0q : ℝ) := add_le_add hlip hUd0

theorem orbit_disc {c : ℂ} (hc : Work.SeedCertRay.Xb.mem c) {z : ℂ}
    (hz : ‖z - Work.TripodCert.uZ0‖ ≤ Work.TripodCert.uRUr) :
    (‖z - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) ∧
    (‖Work.Landing.Tsq c z - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) ∧
    (‖Work.Landing.Tsq c (Work.Landing.Tsq c z) - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) ∧
    (‖Work.Landing.Tsq Work.TripodCert.c0T Work.TripodCert.uZ0 - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) ∧
    (‖Work.Landing.Tsq Work.TripodCert.c0T (Work.Landing.Tsq Work.TripodCert.c0T Work.TripodCert.uZ0) - Work.TripodCert.uZ0‖ ≤ (Work.TripodCert.UREq : ℝ)) := by
  have hUN0 : (0 : ℝ) ≤ (UN0q : ℝ) := by norm_num [UN0q, UMq]
  have hUN1 : (0 : ℝ) ≤ (UN1q : ℝ) := by norm_num [UN1q, UMq, UCmq]
  have hsum : (Ur1q : ℝ) + (Ur0q : ℝ) ≤ (UREq : ℝ) := by
    have h : ((Ur1q + Ur0q : ℚ) : ℝ) ≤ ((UREq : ℚ) : ℝ) := by exact_mod_cast hUr1
    simpa using h
  have hsumE : ((Ur1q : ℝ) + (Ur0q : ℝ)) * (UN0q : ℝ) * (UN1q : ℝ) + (Ur0q : ℝ)
      ≤ (UREq : ℝ) := by
    have h : (((Ur1q + Ur0q) * UN0q * UN1q + Ur0q : ℚ) : ℝ) ≤ ((UREq : ℚ) : ℝ) := by
      exact_mod_cast hUr1E
    simpa using h
  have hUr1R : (Ur1q : ℝ) = uRUr * (UN0q : ℝ) * (UN1q : ℝ) := by
    simp only [Ur1q, uRUr, uRUq]; push_cast; ring
  have hzU : ‖z‖ ≤ (UMq : ℝ) := by
    have h := hUMz
    have h2 : ‖z‖ ≤ ‖uZ0‖ + ‖z - uZ0‖ := by
      calc ‖z‖ = ‖uZ0 + (z - uZ0)‖ := by ring_nf
        _ ≤ ‖uZ0‖ + ‖z - uZ0‖ := norm_add_le _ _
    have hz' : ‖z - uZ0‖ ≤ (uRUq : ℝ) := hz
    push_cast at h
    linarith
  have hstep1 : ‖Work.Landing.Tsq c z - uZ0‖ ≤ (Ur1q : ℝ) + (Ur0q : ℝ) := by
    have h := Tsq_step_le hc hzU
    have hmul : ‖z - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ)
        ≤ uRUr * (UN0q : ℝ) * (UN1q : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz hUN0) hUN1
    rw [← hUr1R] at hmul
    linarith
  have hwU : ‖Work.Landing.Tsq c z‖ ≤ (UMq : ℝ) := by
    have h := hUM0
    have h2 : ‖Work.Landing.Tsq c z‖
        ≤ ‖uZ0‖ + ‖Work.Landing.Tsq c z - uZ0‖ := by
      calc ‖Work.Landing.Tsq c z‖ = ‖uZ0 + (Work.Landing.Tsq c z - uZ0)‖ := by ring_nf
        _ ≤ ‖uZ0‖ + ‖Work.Landing.Tsq c z - uZ0‖ := norm_add_le _ _
    push_cast at h
    linarith
  have hstep2 : ‖Work.Landing.Tsq c (Work.Landing.Tsq c z) - uZ0‖ ≤ (UREq : ℝ) := by
    have h := Tsq_step_le hc hwU
    have hmul : ‖Work.Landing.Tsq c z - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ)
        ≤ ((Ur1q : ℝ) + (Ur0q : ℝ)) * (UN0q : ℝ) * (UN1q : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep1 hUN0) hUN1
    linarith
  have hc0a : ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ ≤ (UREq : ℝ) :=
    le_trans hUd0 Ud0q_le_UREq
  have hz'U : ‖Work.Landing.Tsq c0T uZ0‖ ≤ (UMq : ℝ) := by
    have h := hUM0
    have h2 : ‖Work.Landing.Tsq c0T uZ0‖
        ≤ ‖uZ0‖ + ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ := by
      calc ‖Work.Landing.Tsq c0T uZ0‖
          = ‖uZ0 + (Work.Landing.Tsq c0T uZ0 - uZ0)‖ := by ring_nf
        _ ≤ ‖uZ0‖ + ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ := norm_add_le _ _
    have h3 : ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ ≤ (UREq : ℝ) := hc0a
    push_cast at h
    linarith
  have hc0b : ‖Work.Landing.Tsq c0T (Work.Landing.Tsq c0T uZ0) - uZ0‖ ≤ (UREq : ℝ) := by
    have h := Tsq_step_c0T_le hz'U
    have hnum : (Ud0q : ℝ) * (UN0q : ℝ) * (UN1q : ℝ) + (Ud0q : ℝ) ≤ (UREq : ℝ) := by
      norm_num [Ud0q, UN0q, UN1q, UMq, UCmq, UREq]
    have hmul : ‖Work.Landing.Tsq c0T uZ0 - uZ0‖ * (UN0q : ℝ) * (UN1q : ℝ)
        ≤ (Ud0q : ℝ) * (UN0q : ℝ) * (UN1q : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUd0 hUN0) hUN1
    linarith
  exact ⟨le_trans hz uRUr_le_UREq, le_trans hstep1 hsum, hstep2, hc0a, hc0b⟩

end Work.TripodCert
