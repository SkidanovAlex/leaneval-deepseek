import Mathlib
import Submission.Work.Cert.ACBall.Basic
import Submission.Work.Cert.ACBall.LuneShadow
import Submission.Work.Cert.ball_ops
import Submission.Work.ANum2.lune_second_deriv_bound
import Submission.Work.APsi.lune_branch

/-! # Ball semantics of the `luneStage` chain

For each named ball of `Work.Cert.ACBall.LuneShadow` we record the exact mathematical value it
contains: `lR` contains `R(−c)`, `ls` its square root, `lv` contains `lune (36/5)(−c)`, `lRp`
contains `R'(−c)`, `linvs` contains `1/√R(−c)` and `lvp` contains `lune' (−c)`.

The only external input is `Work.Cert.ball_ops` (soundness of `bmul`, `binv`, `bsqrt`). -/

namespace Work.Cert.ACBall
open Work.Cert Complex Submission.CDTPlan

/-- the input centre `c = (cr + ci i)/S`. -/
noncomputable def cIn (st : St) : ℂ := cx st.cr st.ci

/-! ## Adapters for the dispatched `ball_ops` -/

lemma bmul_mem {a b : Bl} {u v : ℂ} (ha : BallMem a u) (hb : BallMem b v) :
    BallMem (bmul a b) (u * v) := (ball_ops.1 a b u v ha hb).2.2

lemma binv_mem {a : Bl} {L : ℤ} {u : ℂ} (h : binvOK a L = true) (ha : BallMem a u) :
    BallMem (binv a L) u⁻¹ := (ball_ops.2.1 a L u h ha).2

lemma bsqrt_mem {a : Bl} {sr si : ℤ} {u : ℂ} (h : bsqrtOK a sr = true) (ha : BallMem a u) :
    BallMem (bsqrt a sr si) (u ^ (1 / 2 : ℂ)) := ball_ops.2.2 a sr si u h ha

/-! ## The exact values of the stage constants -/

lemma LB2_cast : ((LB2 : ℤ) : ℝ) = (S : ℝ) * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2) := by
  norm_num [S, LB2]
lemma K16_cast : ((K16 : ℤ) : ℝ) = (S : ℝ) * (16 * (36 / 5 : ℝ) ^ 2) := by
  norm_num [S, K16]
lemma LB_cast : ((LB : ℤ) : ℝ) = (S : ℝ) * (1 + (36 / 5 : ℝ) ^ 2) := by norm_num [S, LB]
lemma LD_cast : ((LD : ℤ) : ℝ) = (S : ℝ) * (2 * ((36 / 5 : ℝ) ^ 2 - 1)) := by norm_num [S, LD]
lemma L8_cast : ((L8 : ℤ) : ℝ) = (S : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1)) := by norm_num [S, L8]

lemma LD_pos : (0 : ℤ) < LD := by norm_num [LD]

/-- the real value `a/S` of a mantissa `a`. -/
noncomputable def mS (a : ℤ) : ℝ := (a : ℝ) / (S : ℝ)

lemma mS_mk (a : ℤ) : mS a = (a : ℝ) / (S : ℝ) := rfl
lemma mS_LB2 : mS LB2 = (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by
  rw [mS_mk, div_eq_iff (ne_of_gt S_posR)]; linarith [LB2_cast]
lemma mS_K16 : mS K16 = 16 * (36 / 5 : ℝ) ^ 2 := by
  rw [mS_mk, div_eq_iff (ne_of_gt S_posR)]; linarith [K16_cast]
lemma mS_LB : mS LB = 1 + (36 / 5 : ℝ) ^ 2 := by
  rw [mS_mk, div_eq_iff (ne_of_gt S_posR)]; linarith [LB_cast]
lemma mS_LD : mS LD = 2 * ((36 / 5 : ℝ) ^ 2 - 1) := by
  rw [mS_mk, div_eq_iff (ne_of_gt S_posR)]; linarith [LD_cast]
lemma mS_L8 : mS L8 = 8 * ((36 / 5 : ℝ) ^ 2 - 1) := by
  rw [mS_mk, div_eq_iff (ne_of_gt S_posR)]; linarith [L8_cast]
lemma mS_S : mS S = 1 := by rw [mS_mk, div_self (ne_of_gt S_posR)]
lemma mS_twoLB2 : mS (2 * LB2) = 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by
  rw [mS_mk, show ((2 * LB2 : ℤ) : ℝ) = 2 * (LB2 : ℝ) by push_cast; ring,
    div_eq_iff (ne_of_gt S_posR)]
  linarith [LB2_cast]

/-- `(fdiv S 2)/S = 1/2` exactly. -/
lemma mS_fdiv_S_two : mS (fdiv S 2) = 1 / 2 := by
  have h : fdiv S 2 = 54975581388800000000 := by decide
  rw [mS_mk, h]; norm_num [S]

/-- `bK` membership, phrased with `mS`. -/
lemma ballMem_bK_mS (k : ℤ) : BallMem (bK k) ((mS k : ℝ) : ℂ) := ballMem_bK k

/-! ## The chain -/

lemma ballMem_cIn_neg (st : St) : BallMem (lZ st) (-(cIn st)) := by
  rw [BallMem]
  show ‖(-(cx st.cr st.ci)) - cx (-st.cr) (-st.ci)‖ ≤ ((0 : ℤ) : ℝ) / (S : ℝ)
  rw [cx_neg, sub_self, norm_zero, Int.cast_zero, zero_div]

lemma ballMem_lopz (st : St) : BallMem (lopz st) (1 - cIn st) := by
  have h1 : BallMem (bK S) ((1 : ℝ) : ℂ) := by
    have h := ballMem_bK S
    rw [div_self (ne_of_gt S_posR)] at h
    simpa using h
  have h3 := ballMem_badd h1 (ballMem_cIn_neg st)
  have hv : (((1 : ℝ) : ℂ) + -(cIn st)) = 1 - cIn st := by push_cast; ring
  rwa [hv] at h3

lemma ballMem_lo2 (st : St) : BallMem (lo2 st) ((1 - cIn st) ^ 2) := by
  have h := bmul_mem (ballMem_lopz st) (ballMem_lopz st)
  simpa [pow_two, lo2] using h

lemma ballMem_lINVLD : BallMem lINVLD ((1 / (2 * ((36 / 5 : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
  have hx : fdiv (S * S) LD = 1081345031250983477 := by decide
  rw [BallMem]
  show ‖((1 / (2 * ((36 / 5 : ℝ) ^ 2 - 1)) : ℝ) : ℂ) - cx (fdiv (S * S) LD) 0‖
      ≤ ((1 : ℤ) : ℝ) / (S : ℝ)
  rw [hx, cx_zero_y, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  norm_num [S]

lemma ballMem_lR (st : St) : BallMem (lR st) (Work.APsi.luneR (36 / 5) (-(cIn st))) := by
  have h1 : BallMem (bmul (bK LB2) (lo2 st)) (((mS LB2 : ℝ) : ℂ) * ((1 - cIn st) ^ 2)) :=
    bmul_mem (ballMem_bK_mS LB2) (ballMem_lo2 st)
  have h2 : BallMem (bmul (bK K16) (lZ st)) (((mS K16 : ℝ) : ℂ) * (-(cIn st))) :=
    bmul_mem (ballMem_bK_mS K16) (ballMem_cIn_neg st)
  have h3 := ballMem_bsub h1 h2
  have hv : ((mS LB2 : ℝ) : ℂ) * ((1 - cIn st) ^ 2) - ((mS K16 : ℝ) : ℂ) * (-(cIn st))
      = Work.APsi.luneR (36 / 5) (-(cIn st)) := by
    rw [mS_LB2, mS_K16]
    simp only [Work.APsi.luneR]
    push_cast
    ring
  rwa [hv] at h3

lemma ballMem_ls (st : St) (w : LuneW) (h : bsqrtOK (lR st) w.sr = true) :
    BallMem (ls st w) ((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ)) :=
  bsqrt_mem h (ballMem_lR st)

lemma ballMem_lv (st : St) (w : LuneW)
    (hs : BallMem (ls st w) ((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ))) :
    BallMem (lv st w) (lune (36 / 5) (-(cIn st))) := by
  have h1 : BallMem (bmul (bK LB) (lZ st)) (((mS LB : ℝ) : ℂ) * (-(cIn st))) :=
    bmul_mem (ballMem_bK_mS LB) (ballMem_cIn_neg st)
  have h2 := ballMem_bsub h1 (ballMem_bK_mS LB)
  have h3 := ballMem_badd h2 hs
  have h4 := bmul_mem h3 ballMem_lINVLD
  have hv : ((((mS LB : ℝ) : ℂ) * (-(cIn st)) - ((mS LB : ℝ) : ℂ)
        + ((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ)))
      * ((1 / (2 * ((36 / 5 : ℝ) ^ 2 - 1)) : ℝ) : ℂ)) = lune (36 / 5) (-(cIn st)) := by
    rw [mS_LB, Work.APsi.lune_eq]
    simp only [Work.APsi.luneB, Work.APsi.luneC, Work.APsi.luneBr, Work.APsi.luneCr]
    push_cast
    rw [div_eq_mul_one_div]
    ring
  rwa [hv] at h4

lemma ballMem_lRp (st : St) : BallMem (lRp st) (Work.ANum2.luneRd (36 / 5) (-(cIn st))) := by
  have h1 : BallMem (bmul (bK (2 * LB2)) (lopz st)) (((mS (2 * LB2) : ℝ) : ℂ) * (1 - cIn st)) :=
    bmul_mem (ballMem_bK_mS (2 * LB2)) (ballMem_lopz st)
  have h3 := ballMem_bsub h1 (ballMem_bK_mS K16)
  have hv : ((mS (2 * LB2) : ℝ) : ℂ) * (1 - cIn st) - ((mS K16 : ℝ) : ℂ)
      = Work.ANum2.luneRd (36 / 5) (-(cIn st)) := by
    rw [mS_twoLB2, mS_K16]
    simp only [Work.ANum2.luneRd]
    push_cast
    ring
  rwa [hv] at h3

lemma ballMem_linvs (st : St) (w : LuneW) (h : binvOK (ls st w) w.Ls = true)
    (hs : BallMem (ls st w) ((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ))) :
    BallMem (linvs st w) (((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ))⁻¹) :=
  binv_mem h hs

lemma ballMem_lvp (st : St) (w : LuneW) (hz : ‖cIn st‖ < 1)
    (hRp : BallMem (lRp st) (Work.ANum2.luneRd (36 / 5) (-(cIn st))))
    (hinv : BallMem (linvs st w) (((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ))⁻¹)) :
    BallMem (lvp st w) (deriv (lune (36 / 5)) (-(cIn st))) := by
  have hhalf : BallMem (bK (fdiv S 2)) ((1 / 2 : ℝ) : ℂ) := by
    have h := ballMem_bK_mS (fdiv S 2)
    rw [mS_fdiv_S_two] at h
    exact h
  have h1 := bmul_mem hRp hinv
  have h2 := bmul_mem h1 hhalf
  have hRp_e : (Work.ANum2.luneRd (36 / 5) (-(cIn st)))
        * (((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (1 / 2 : ℂ))⁻¹) * ((1 / 2 : ℝ) : ℂ)
      = (1 / 2 : ℂ) * ((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (-(1 / 2) : ℂ))
        * (Work.ANum2.luneRd (36 / 5) (-(cIn st))) := by
    rw [Complex.cpow_neg]; push_cast; ring
  rw [hRp_e] at h2
  have h3 := ballMem_badd (ballMem_bK_mS LB) h2
  have h4 := bmul_mem h3 ballMem_lINVLD
  have hv : ((((mS LB : ℝ) : ℂ) + (1 / 2 : ℂ)
        * ((Work.APsi.luneR (36 / 5) (-(cIn st))) ^ (-(1 / 2) : ℂ))
        * (Work.ANum2.luneRd (36 / 5) (-(cIn st))))
      * ((1 / (2 * ((36 / 5 : ℝ) ^ 2 - 1)) : ℝ) : ℂ)) = deriv (lune (36 / 5)) (-(cIn st)) := by
    rw [mS_LB, Work.ANum2.deriv_lune_eq (36 / 5) (by norm_num) (-(cIn st))
      (by simpa [norm_neg] using hz)]
    simp only [Work.APsi.luneB, Work.APsi.luneC, Work.APsi.luneBr, Work.APsi.luneCr]
    push_cast
    rw [div_eq_mul_one_div]
    ring
  rwa [hv] at h4

end Work.Cert.ACBall
