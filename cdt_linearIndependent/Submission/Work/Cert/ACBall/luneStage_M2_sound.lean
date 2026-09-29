import Mathlib
import Submission.Work.Cert.ACBall.LuneShadow
import Submission.Work.Cert.ACBall.LuneChain
import Submission.Work.Cert.ACBall.LuneAnalytic
import Submission.Work.Cert.ball_ops
import Submission.Work.Cert.ACBall.luneR_disc_bounds
import Submission.Work.Cert.ACBall.lune_deriv2_cauchy_le

namespace Work.Cert.ACBall
open Work.Cert Complex Submission.CDTPlan

/-! # Soundness of the `M2` second-derivative bound of the lune stage

`lM2 st w = min lM2e lM2c` is the second-derivative mantissa of the lune stage of the
Theorem-A arc certificate (`Work.Cert.Defs.luneStage`).  This file proves that on the input
disc of the stage the second derivative of `lune (36/5)` is bounded by `lM2 st w / S`:

`‖lune''(u)‖ ≤ lM2/S` for `‖u + c‖ ≤ ρ/S`,

which is the hypothesis needed for the quadratic term of the Taylor output-radius estimate.

The proof assembles three ingredients:
* `Work.Cert.ACBall.lune_deriv2_cauchy_le` (child lemma): the `M2c` (Cauchy) branch;
* `lune_deriv2_explicit_le` below: the `M2e` (explicit) branch, whose analytic input is
  `Work.Cert.ACBall.lune_deriv2_le_explicit` and whose geometric input is the disc bound
  `Work.Cert.ACBall.luneR_disc_bounds` (child lemma) for `R`, `R'`;
* `lune_deriv2_crude`: a crude `INF`-level bound so that a branch equal to `INF` needs nothing.
-/

namespace M2

/-! ## Reading off `lokM` -/

lemma lokM_spec (st : St) (w : LuneW) (h : lokM st w = true) :
    (0 ≤ w.D) ∧ ((lvp st w).x * (lvp st w).x + (lvp st w).y * (lvp st w).y ≤ w.D * w.D) ∧
    (0 ≤ w.zU) ∧ (st.cr * st.cr + st.ci * st.ci ≤ w.zU * w.zU) ∧
    (0 ≤ w.RU) ∧ ((lR st).x * (lR st).x + (lR st).y * (lR st).y ≤ w.RU * w.RU) ∧
    (0 ≤ w.RL) ∧ (w.RL * w.RL ≤ (lR st).x * (lR st).x + (lR st).y * (lR st).y) ∧
    (0 ≤ w.rpU) ∧ ((lRp st).x * (lRp st).x + (lRp st).y * (lRp st).y ≤ w.rpU * w.rpU) := by
  have h' := h
  simp only [lokM, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h'
  exact h'

lemma cIn_norm_le (st : St) (w : LuneW) (h : lokM st w = true) :
    ‖cIn st‖ ≤ (w.zU : ℝ) / S := by
  obtain ⟨-, -, hz0, hz1, -, -, -, -, -, -⟩ := lokM_spec st w h
  exact norm_cx_le_of_sq_le st.cr st.ci w.zU hz0 hz1

lemma lR_center_le (st : St) (w : LuneW) (h : lokM st w = true) :
    ‖cx (lR st).x (lR st).y‖ ≤ (w.RU : ℝ) / S := by
  obtain ⟨-, -, -, -, hR0, hR1, -, -, -, -⟩ := lokM_spec st w h
  exact norm_cx_le_of_sq_le (lR st).x (lR st).y w.RU hR0 hR1

lemma lRp_center_le (st : St) (w : LuneW) (h : lokM st w = true) :
    ‖cx (lRp st).x (lRp st).y‖ ≤ (w.rpU : ℝ) / S := by
  obtain ⟨-, -, -, -, -, -, -, -, hp0, hp1⟩ := lokM_spec st w h
  exact norm_cx_le_of_sq_le (lRp st).x (lRp st).y w.rpU hp0 hp1

lemma lR_center_ge (st : St) (w : LuneW) (h : lokM st w = true) :
    (w.RL : ℝ) / S ≤ ‖cx (lR st).x (lR st).y‖ := by
  obtain ⟨-, -, -, -, -, -, hL0, hL1, -, -⟩ := lokM_spec st w h
  have hS := S_posR
  have hRLR : (0 : ℝ) ≤ (w.RL : ℝ) := by exact_mod_cast hL0
  have hsq := norm_cx_sq (lR st).x (lR st).y
  have hle : ((w.RL : ℝ) / S) ^ 2 ≤ ‖cx (lR st).x (lR st).y‖ ^ 2 := by
    rw [hsq, div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (S : ℝ))
    have h' : (((w.RL * w.RL : ℤ)) : ℝ)
        ≤ (((lR st).x * (lR st).x + (lR st).y * (lR st).y : ℤ) : ℝ) := by exact_mod_cast hL1
    push_cast at h' ⊢
    linarith
  calc (w.RL : ℝ) / S = Real.sqrt (((w.RL : ℝ) / S) ^ 2) :=
        (Real.sqrt_sq (div_nonneg hRLR hS.le)).symm
    _ ≤ Real.sqrt (‖cx (lR st).x (lR st).y‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖cx (lR st).x (lR st).y‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## `mu` of nonnegative arguments -/

lemma mu_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mu a b := by
  have h := mu_ge a b
  have : (0:ℝ) ≤ (a:ℝ) * (b:ℝ) / (S:ℝ) :=
    div_nonneg (mul_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb)) S_posR.le
  exact_mod_cast (le_trans this h)

/-! ## The input disc lies in the open unit disc -/

lemma norm_lt_one_of_disc (st : St) (w : LuneW) (hokM : lokM st w = true)
    (hzU : w.zU + st.rho + 1 < S) {u : ℂ} (hu : ‖u - (-(cIn st))‖ ≤ (st.rho : ℝ) / S) :
    ‖u‖ < 1 := by
  have h1 : ‖u‖ ≤ ‖u - (-(cIn st))‖ + ‖-(cIn st)‖ := by
    calc ‖u‖ = ‖(u - (-(cIn st))) + (-(cIn st))‖ := by ring_nf
      _ ≤ ‖u - (-(cIn st))‖ + ‖-(cIn st)‖ := norm_add_le _ _
  rw [norm_neg] at h1
  have h2 := cIn_norm_le st w hokM
  have h4 : (((st.rho + w.zU : ℤ)) : ℝ) / S < 1 := by
    rw [div_lt_one S_posR]
    have : (st.rho + w.zU : ℤ) < S := by omega
    exact_mod_cast this
  have h5 : (((st.rho + w.zU : ℤ)) : ℝ) / S = (st.rho : ℝ) / S + (w.zU : ℝ) / S := by
    push_cast; ring
  linarith [h1, hu, h2, h4]

/-! ## The crude (Cauchy) bound with `INF` -/

lemma lune_deriv2_crude (st : St) (w : LuneW) (hokM : lokM st w = true)
    (hzU : w.zU + st.rho + 1 < S) {u : ℂ} (hu : ‖u - (-(cIn st))‖ ≤ (st.rho : ℝ) / S) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) u‖ ≤ ((INF : ℤ) : ℝ) / S := by
  have hS := S_posR
  have hSne : (S : ℝ) ≠ 0 := ne_of_gt hS
  have hlt1 := norm_lt_one_of_disc st w hokM hzU hu
  have hld1 : (1 : ℤ) ≤ ld st w := by rw [ld]; omega
  have hldR : (1 : ℝ) ≤ (ld st w : ℝ) := by exact_mod_cast hld1
  have hd : (0 : ℝ) < (ld st w : ℝ) / S := by
    apply div_pos _ S_posR; linarith
  have hdle : (ld st w : ℝ) / S ≤ 1 - ‖u‖ := by
    have h1 : ‖u‖ ≤ (st.rho : ℝ) / S + (w.zU : ℝ) / S := by
      calc ‖u‖ ≤ ‖u - (-(cIn st))‖ + ‖cIn st‖ := by
            calc ‖u‖ = ‖(u - (-(cIn st))) + (-(cIn st))‖ := by ring_nf
              _ ≤ ‖u - (-(cIn st))‖ + ‖-(cIn st)‖ := norm_add_le _ _
              _ = ‖u - (-(cIn st))‖ + ‖cIn st‖ := by rw [norm_neg]
        _ ≤ (st.rho : ℝ) / S + (w.zU : ℝ) / S :=
            add_le_add hu (cIn_norm_le st w hokM)
    have h2 : 1 - ((st.rho : ℝ) / S + (w.zU : ℝ) / S) = ((ld st w : ℝ) + 1) / S := by
      rw [ld]; push_cast
      field_simp
      ring
    have h3 : (ld st w : ℝ) / S ≤ ((ld st w : ℝ) + 1) / S := by
      apply div_le_div_of_nonneg_right _ hS.le
      linarith
    linarith [h2, h3]
  have h := lune_deriv2_le_cauchy hlt1 hd hdle
  refine h.trans ?_
  have hl2 : (1 : ℝ) ≤ (ld st w : ℝ) ^ 2 := by nlinarith [hldR]
  have hINF : (2 : ℝ) * (S : ℝ) ^ 3 ≤ ((INF : ℤ) : ℝ) := by
    have hZ : (2 : ℤ) * S ^ 3 ≤ INF := by norm_num [S, INF]
    exact_mod_cast hZ
  have h1 : 2 / ((ld st w : ℝ) / S) ^ 2 = 2 * (S : ℝ) ^ 2 / (ld st w : ℝ) ^ 2 := by
    field_simp
  rw [h1]
  have h2 : 2 * (S : ℝ) ^ 2 / (ld st w : ℝ) ^ 2 ≤ 2 * (S : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hl2]
  have h3 : 2 * (S : ℝ) ^ 2 ≤ ((INF : ℤ) : ℝ) / S := by
    rw [le_div_iff₀ hS]
    nlinarith [hINF]
  linarith

/-! ## RADII OF THE BALL CHAIN ARE NONNEGATIVE -/

lemma bmul_radius_nonneg (a b : Bl) (ha : 0 ≤ a.r) (hb : 0 ≤ b.r) : 0 ≤ (bmul a b).r := by
  have h1 : 0 ≤ bmod a := bmod_nonneg a
  have h2 : 0 ≤ bmod b := bmod_nonneg b
  have hm1 := mu_nonneg h1 hb
  have hm2 := mu_nonneg h2 ha
  have hm3 := mu_nonneg ha hb
  simp only [bmul]
  linarith

lemma lZ_radius (st : St) : (lZ st).r = 0 := rfl
lemma bK_radius (k : ℤ) : (bK k).r = 0 := rfl

lemma lopz_radius_nonneg (st : St) : 0 ≤ (lopz st).r := by
  simp only [lopz, badd, bK, lZ]; norm_num

lemma lo2_radius_nonneg (st : St) : 0 ≤ (lo2 st).r :=
  bmul_radius_nonneg _ _ (lopz_radius_nonneg st) (lopz_radius_nonneg st)

lemma lR_radius_nonneg (st : St) : 0 ≤ (lR st).r := by
  have h1 := bmul_radius_nonneg (bK LB2) (lo2 st) (le_refl 0) (lo2_radius_nonneg st)
  have h2 := bmul_radius_nonneg (bK K16) (lZ st) (le_refl 0) (le_refl 0)
  simp only [lR, bsub]
  linarith

lemma lRp_radius_nonneg (st : St) : 0 ≤ (lRp st).r := by
  have h1 := bmul_radius_nonneg (bK (2 * LB2)) (lopz st) (le_refl 0) (lopz_radius_nonneg st)
  have h2 : (bK K16).r = 0 := rfl
  simp only [lRp, bsub]
  linarith

lemma lRpp_nonneg : (0 : ℤ) ≤ lRpp := by norm_num [lRpp, LB2]

lemma lRpD_nonneg (st : St) (w : LuneW) (hokM : lokM st w = true) (hrho : 0 ≤ st.rho) :
    (0 : ℤ) ≤ lRpD st w := by
  obtain ⟨-, -, -, -, -, -, -, -, hrpU, -⟩ := lokM_spec st w hokM
  have h1 := mu_nonneg hrho lRpp_nonneg
  have h2 := lRp_radius_nonneg st
  simp only [lRpD]
  linarith

lemma lRhi_nonneg (st : St) (w : LuneW) (hokM : lokM st w = true) (hrho : 0 ≤ st.rho) :
    (0 : ℤ) ≤ lRhi st w := by
  obtain ⟨-, -, -, -, hRU, -, -, -, -, -⟩ := lokM_spec st w hokM
  have h1 := mu_nonneg hrho (lRpD_nonneg st w hokM hrho)
  have h2 := lR_radius_nonneg st
  simp only [lRhi]
  linarith

/-! ## The explicit-branch rounding comparison -/

theorem lM2e_rounding (st : St) (w : LuneW) (hf : 0 < lRlo st w) (hsL : 0 < w.sL)
    (hldd : 0 < ldd st w) (hA0 : (0 : ℤ) ≤ lRhi st w) :
    (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
        + ((lRpD st w : ℝ) / S) ^ 2)
      / (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S))
    ≤ (dvu (lnum st w) (ldd st w) : ℝ) / S := by
  have hS := S_posR
  have hSne : (S : ℝ) ≠ 0 := ne_of_gt hS
  have hA0' : (0 : ℝ) ≤ (lRhi st w : ℝ) := by exact_mod_cast hA0
  have hFpos : (0 : ℝ) < (lRlo st w : ℝ) := by exact_mod_cast hf
  have hMpos : (0 : ℝ) < (w.sL : ℝ) := by exact_mod_cast hsL
  have hlRpp : ((lRpp : ℤ) : ℝ) = (S : ℝ) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2) := by
    have h : ((2 * LB2 : ℤ) : ℝ) / (S : ℝ) = 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by
      simpa only [mS_mk] using mS_twoLB2
    rw [div_eq_iff hSne] at h
    simp only [lRpp]
    linarith
  have hL8' : ((L8 : ℤ) : ℝ) = (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1)) := by
    have h := mS_L8
    simp only [mS_mk] at h
    rw [div_eq_iff hSne] at h
    linarith
  have hnum : (S : ℝ) * (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
        + ((lRpD st w : ℝ) / S) ^ 2) ≤ (lnum st w : ℝ) := by
    have h1 := mu_ge (2 * lRhi st w) lRpp
    have h2 := mu_ge (lRpD st w) (lRpD st w)
    have e1 : (S : ℝ) * (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2))
        = ((2 * lRhi st w : ℤ) : ℝ) * ((lRpp : ℤ) : ℝ) / (S : ℝ) := by
      rw [hlRpp]
      push_cast
      field_simp <;> try ring_nf
    have e2 : (S : ℝ) * (((lRpD st w : ℝ) / S) ^ 2)
        = ((lRpD st w : ℤ) : ℝ) * ((lRpD st w : ℤ) : ℝ) / (S : ℝ) := by
      push_cast
      field_simp <;> try ring_nf
    rw [show lnum st w = mu (2 * lRhi st w) lRpp + mu (lRpD st w) (lRpD st w) from rfl]
    rw [Int.cast_add, mul_add, e1, e2]
    linarith
  have hden : (ldd st w : ℝ)
      ≤ (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S)) := by
    have h1 := md_le L8 (lRlo st w)
    have h2 := md_le (md L8 (lRlo st w)) (w.sL)
    have h3 : ((md L8 (lRlo st w) : ℤ) : ℝ)
        ≤ (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S)) := by
      calc ((md L8 (lRlo st w) : ℤ) : ℝ)
          ≤ ((L8 : ℤ) : ℝ) * ((lRlo st w : ℤ) : ℝ) / S := h1
        _ = (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S)) := by
              rw [hL8']; ring_nf
    have h4 : ((md (md L8 (lRlo st w)) (w.sL) : ℤ) : ℝ)
        ≤ (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S)) := by
      refine h2.trans ?_
      have h3' : ((md L8 (lRlo st w) : ℤ) : ℝ) * ((w.sL : ℤ) : ℝ) / S
          ≤ ((S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S))) * ((w.sL : ℝ) / S) := by
        calc ((md L8 (lRlo st w) : ℤ) : ℝ) * ((w.sL : ℤ) : ℝ) / S
            = ((md L8 (lRlo st w) : ℤ) : ℝ) * (((w.sL : ℤ) : ℝ) / S) := by ring
          _ ≤ ((S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S))) * (((w.sL : ℤ) : ℝ) / S) :=
              mul_le_mul_of_nonneg_right h3 (div_nonneg hMpos.le hS.le)
      calc ((md L8 (lRlo st w) : ℤ) : ℝ) * ((w.sL : ℤ) : ℝ) / S
          ≤ ((S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S))) * (((w.sL : ℤ) : ℝ) / S) := h3'
        _ = (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S)) := by
              ring_nf
    rw [show ldd st w = md (md L8 (lRlo st w)) (w.sL) from rfl]
    exact h4
  have hNnn : (0 : ℝ) ≤ 2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
      + ((lRpD st w : ℝ) / S) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (lRhi st w : ℝ) / S := div_nonneg hA0' hS.le
    have h2 : (0 : ℝ) ≤ 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by norm_num
    nlinarith [h1, h2, sq_nonneg ((lRpD st w : ℝ) / S)]
  have hnum_nn : (0 : ℝ) ≤ (lnum st w : ℝ) := le_trans (mul_nonneg hS.le hNnn) hnum
  have hlddR : (0 : ℝ) < (ldd st w : ℝ) := by exact_mod_cast hldd
  have hDpos : (0 : ℝ) < 8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S) := by
    have h1 : (0 : ℝ) < 8 * ((36 / 5 : ℝ) ^ 2 - 1) := by norm_num
    have h2 : (0 : ℝ) < (lRlo st w : ℝ) / S := div_pos hFpos hS
    have h3 : (0 : ℝ) < (w.sL : ℝ) / S := div_pos hMpos hS
    positivity
  have hgle : (S : ℝ) * (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
        + ((lRpD st w : ℝ) / S) ^ 2)
      / ((S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S)))
      ≤ (lnum st w : ℝ) / (ldd st w : ℝ) :=
    div_le_div₀ hnum_nn hnum hlddR hden
  have hstep : (lnum st w : ℝ) / (ldd st w : ℝ) ≤ (dvu (lnum st w) (ldd st w) : ℝ) / S := by
    rw [div_le_div_iff₀ hlddR hS]
    have hh := dvu_ge (a := lnum st w) (b := ldd st w) hldd
    rw [div_le_iff₀ hlddR] at hh
    exact hh
  calc (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
        + ((lRpD st w : ℝ) / S) ^ 2)
      / (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S))
      = (S : ℝ) * (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
          + ((lRpD st w : ℝ) / S) ^ 2)
        / ((S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S))) := by
        field_simp <;> try ring_nf
    _ ≤ (lnum st w : ℝ) / (ldd st w : ℝ) := hgle
    _ ≤ (dvu (lnum st w) (ldd st w) : ℝ) / S := hstep

/-! ## The explicit branch -/

theorem lune_deriv2_explicit_le (st : St) (w : LuneW) (hokM : lokM st w = true)
    (hokW : lokW st w = true) (hzU : w.zU + st.rho + 1 < S) (hrho : 0 ≤ st.rho)
    (hE : lM2e st w ≠ INF) {u : ℂ} (hu : ‖u - (-(cIn st))‖ ≤ (st.rho : ℝ) / S) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) u‖ ≤ (lM2e st w : ℝ) / S := by
  have hS := S_posR
  have hcond : (luseE st w && decide (0 < ldd st w)) = true := by
    by_contra hc
    exact hE (by rw [lM2e]; exact if_neg hc)
  rw [Bool.and_eq_true] at hcond
  obtain ⟨huse, hldd'⟩ := hcond
  have hldd : 0 < ldd st w := by simpa using hldd'
  have hRlopos : 0 < lRlo st w := by
    have h := huse; rw [luseE] at h; simpa using h
  have hEeq : lM2e st w = dvu (lnum st w) (ldd st w) := by
    rw [lM2e]; exact if_pos (by rw [Bool.and_eq_true]; exact ⟨huse, hldd'⟩)
  have hW : (decide (0 < w.sL) && decide (w.sL * w.sL ≤ lRlo st w * S)) = true := by
    have h := hokW
    rw [lokW, show luseE st w = true from huse] at h
    simpa using h
  rw [Bool.and_eq_true] at hW
  obtain ⟨hsL', hsL2'⟩ := hW
  have hsL : 0 < w.sL := by simpa using hsL'
  have hsL2 : w.sL * w.sL ≤ lRlo st w * S := by simpa using hsL2'
  obtain ⟨hhi, hp, hlo⟩ := luneR_disc_bounds st w hokM hrho hu
  have hlt1 := norm_lt_one_of_disc st w hokM hzU hu
  have hRlo' : (0 : ℝ) < (lRlo st w : ℝ) / S := div_pos (by exact_mod_cast hRlopos) hS
  have hsLpos : (0 : ℝ) < (w.sL : ℝ) / S := div_pos (by exact_mod_cast hsL) hS
  have hsL2'' : ((w.sL : ℝ) / S) ^ 2 ≤ (lRlo st w : ℝ) / S := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hS]
    have h' : (w.sL : ℝ) ^ 2 ≤ (lRlo st w : ℝ) * (S : ℝ) := by
      have h2 : ((w.sL * w.sL : ℤ) : ℝ) ≤ ((lRlo st w * S : ℤ) : ℝ) := by exact_mod_cast hsL2
      push_cast at h2
      simpa [sq] using h2
    nlinarith [h', hS]
  have hb : ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) u‖ ≤
      (2 * ((lRhi st w : ℝ) / S) * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
          + ((lRpD st w : ℝ) / S) ^ 2)
        / (8 * ((36 / 5 : ℝ) ^ 2 - 1) * ((lRlo st w : ℝ) / S) * ((w.sL : ℝ) / S)) :=
    lune_deriv2_le_explicit (z := u) hlt1 (Rlo := (lRlo st w : ℝ) / S)
      (Rhi := (lRhi st w : ℝ) / S) (Rp := (lRpD st w : ℝ) / S) (sL := (w.sL : ℝ) / S)
      hRlo' hsLpos hlo hhi hp hsL2''
  rw [hEeq]
  exact hb.trans (lM2e_rounding st w hRlopos hsL hldd (lRhi_nonneg st w hokM hrho))

/-! ## `lM2` is the minimum of its two branches -/

lemma lM2_eq_min (st : St) (w : LuneW) :
    (lM2 st w : ℝ) / S = min ((lM2e st w : ℝ) / S) ((lM2c st w : ℝ) / S) := by
  have hcast : ((imin (lM2e st w) (lM2c st w) : ℤ) : ℝ)
      = min ((lM2e st w : ℤ) : ℝ) ((lM2c st w : ℤ) : ℝ) := by
    rw [imin]
    split_ifs with h
    · rw [min_eq_left (by exact_mod_cast h)]
    · rw [min_eq_right (by exact_mod_cast (le_of_lt (lt_of_not_ge h)))]
  rw [lM2, hcast]
  rcases le_total ((lM2e st w : ℤ) : ℝ) ((lM2c st w : ℤ) : ℝ) with h | h
  · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h S_posR.le)]
  · rw [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h S_posR.le)]

end M2

/-! ## The main theorem -/

theorem luneStage_M2_sound (st : St) (w : LuneW) (hokM : lokM st w = true) (hokW : lokW st w = true) (hzU : w.zU + st.rho + 1 < S) (hINF : lM2 st w < INF) (hrho : 0 ≤ st.rho) {u : ℂ} (hu : ‖u - (-(cIn st))‖ ≤ (st.rho : ℝ) / S) : ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) u‖ ≤ (lM2 st w : ℝ) / S := by
  rw [M2.lM2_eq_min]
  refine le_min ?_ ?_
  · by_cases hE : lM2e st w = INF
    · rw [hE]; exact M2.lune_deriv2_crude st w hokM hzU hu
    · exact M2.lune_deriv2_explicit_le st w hokM hokW hzU hrho hE hu
  · by_cases hC : lM2c st w = INF
    · rw [hC]; exact M2.lune_deriv2_crude st w hokM hzU hu
    · exact lune_deriv2_cauchy_le st w hokM hrho hzU hC hu

end Work.Cert.ACBall
