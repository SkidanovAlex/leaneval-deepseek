import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ACBall.Basic
import Submission.Work.Cert.ACBall.binv_sound
import Submission.Work.Cert.ACBall.bsqrt_sound

/-! Guidance from the project lead (the requester):

Context (lead, v2 of the Theorem-A certificate, 2026-09-28 ~18:30). v1 `SlitStageSound` was refuted
(H1761, `Work.Cert.not_slitStageSound`): the sqrt-witness tolerance was S times too loose and all other rounding
was hidden in a blanket SLACK. v2 (`Submission/Work/Cert/Defs.lean`) evaluates the stage centre value f(c)
and derivative f'(c) by RIGOROUS BALL ARITHMETIC at the point c: `Bl` = (x, y, r) = ball centre (x+yi)/S radius
r/S; `badd`, `bsub`, `bmul` (+3 ulps for the centre floors, radius uses |x|+|y| ≥ S|centre|), `binv` (side
condition `binvOK a L`: 0 ≤ r < L, L² ≤ x²+y²), `bsqrt` (side condition `bsqrtOK`: sr > 0; radius
(r + E)/sr with E ≥ S·|c − s²| from the exact integer residual; uses Re √w ≥ 0 and |√w + s| ≥ Re s).
Their soundness is ONE lemma `Work.Cert.ball_ops` (dispatched separately — take it as given / wait for it).
No SLACK anywhere: every ulp is accounted by an explicit term; no sr ≥ S/32 hypothesis (removed with srOK/SrCheck).

Pure rounding lemmas at scale S (`S = 2^40·10^8`, `cx x y = x/S + (y/S) i`, `md a b = ⌊ab/S⌋`,
`mu a b = ⌈ab/S⌉` (as −⌊−ab/S⌋), `dvu a b = ⌈aS/b⌉`, `fdiv = Int.ediv` = floor for positive divisor).
bmul: |zw − a_c b_c| ≤ |a_c||w−b_c| + |b_c||z−a_c| + |z−a_c||w−b_c|, |a_c| ≤ (|x|+|y|)/S; centre floors: real part
error ∈ (−1,1) ulp, imaginary ∈ (−2,0] ⇒ |err| < √5 < 3. binv: |z| ≥ |a_c| − r/S ≥ (L−r)/S > 0,
|1/z − 1/a_c| = |z − a_c|/(|z||a_c|) ≤ r S/((L−r)L) (real), centre S²·conj(c)/n floored (< 1 ulp per coordinate).
bsqrt: (√z − s)(√z + s) = z − s² (`cpow_half_sq` in APsi/defs), Re √z ≥ 0 (principal branch:
arg ∈ (−π, π] ⇒ cos(arg/2) ≥ 0), so |√z + s| ≥ Re s = sr/S; |z − s²| ≤ r/S + E/S where
E = ⌊(|er| + |ei|)/S⌋ + 1 ≥ (|er|+|ei|)/S and er, ei are the exact S²-scaled residuals. Prove a few helper
lemmas (md/mu/dvu/fdiv bounds as real inequalities) first, then each part.
-/

namespace Work.Cert
open Complex
open Work.Cert.ACBall


lemma md_err (a b : ℤ) :
    (0 : ℝ) ≤ (a : ℝ) * (b : ℝ) / (S : ℝ) - ((md a b : ℤ) : ℝ) ∧
      (a : ℝ) * (b : ℝ) / (S : ℝ) - ((md a b : ℤ) : ℝ) < 1 :=
  ⟨by linarith [md_le a b], by linarith [md_gt a b]⟩

set_option maxHeartbeats 1000000 in
lemma bmul_center_le (a b : Bl) :
    ‖cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y‖ ≤ 3 / (S : ℝ) := by
  have hre : (cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y).re
      = (((a.x : ℝ) * (b.x : ℝ) / (S : ℝ) - ((md a.x b.x : ℤ) : ℝ)) -
          ((a.y : ℝ) * (b.y : ℝ) / (S : ℝ) - ((md a.y b.y : ℤ) : ℝ))) / (S : ℝ) := by
    simp only [bmul, Complex.sub_re, Complex.mul_re, cx_re, cx_im]
    push_cast
    ring
  have him : (cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y).im
      = (((a.x : ℝ) * (b.y : ℝ) / (S : ℝ) - ((md a.x b.y : ℤ) : ℝ)) +
          ((a.y : ℝ) * (b.x : ℝ) / (S : ℝ) - ((md a.y b.x : ℤ) : ℝ))) / (S : ℝ) := by
    simp only [bmul, Complex.sub_im, Complex.mul_im, cx_re, cx_im]
    push_cast
    ring
  have hb1 := md_err a.x b.x
  have hb2 := md_err a.y b.y
  have hb3 := md_err a.x b.y
  have hb4 := md_err a.y b.x
  have h1 : |((a.x : ℝ) * (b.x : ℝ) / (S : ℝ) - ((md a.x b.x : ℤ) : ℝ)) -
      ((a.y : ℝ) * (b.y : ℝ) / (S : ℝ) - ((md a.y b.y : ℤ) : ℝ))| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  have h2 : |((a.x : ℝ) * (b.y : ℝ) / (S : ℝ) - ((md a.x b.y : ℤ) : ℝ)) +
      ((a.y : ℝ) * (b.x : ℝ) / (S : ℝ) - ((md a.y b.x : ℤ) : ℝ))| < 2 := by
    rw [abs_lt]
    constructor <;> linarith [hb3.1, hb3.2, hb4.1, hb4.2]
  calc ‖cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y‖
      ≤ |(cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y).re| +
        |(cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = (|((a.x : ℝ) * (b.x : ℝ) / (S : ℝ) - ((md a.x b.x : ℤ) : ℝ)) -
          ((a.y : ℝ) * (b.y : ℝ) / (S : ℝ) - ((md a.y b.y : ℤ) : ℝ))| +
          |((a.x : ℝ) * (b.y : ℝ) / (S : ℝ) - ((md a.x b.y : ℤ) : ℝ)) +
          ((a.y : ℝ) * (b.x : ℝ) / (S : ℝ) - ((md a.y b.x : ℤ) : ℝ))|) / (S : ℝ) := by
        rw [hre, him, abs_div, abs_div, abs_of_pos S_posR]
        ring
    _ ≤ 3 / (S : ℝ) := by
        apply div_le_div_of_nonneg_right _ S_posR.le
        linarith

set_option maxHeartbeats 1000000 in
theorem bmul_sound {a b : Bl} {u v : ℂ} (ha : BallMem a u) (hb : BallMem b v) :
    BallMem (bmul a b) (u * v) := by
  rw [BallMem] at ha hb ⊢
  have hra : (0 : ℝ) ≤ (a.r : ℝ) / (S : ℝ) := le_trans (norm_nonneg _) ha
  have hrb : (0 : ℝ) ≤ (b.r : ℝ) / (S : ℝ) := le_trans (norm_nonneg _) hb
  have hna : ‖cx a.x a.y‖ ≤ ((bmod a : ℤ) : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ S_posR, mul_comm]; exact le_bmod a
  have hnb : ‖cx b.x b.y‖ ≤ ((bmod b : ℤ) : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ S_posR, mul_comm]; exact le_bmod b
  have hna0 : (0 : ℝ) ≤ ((bmod a : ℤ) : ℝ) / (S : ℝ) :=
    div_nonneg (by exact_mod_cast bmod_nonneg a) S_posR.le
  have hnb0 : (0 : ℝ) ≤ ((bmod b : ℤ) : ℝ) / (S : ℝ) :=
    div_nonneg (by exact_mod_cast bmod_nonneg b) S_posR.le
  have htri : ‖u * v - cx a.x a.y * cx b.x b.y‖
      ≤ ‖cx a.x a.y‖ * ‖v - cx b.x b.y‖ + ‖u - cx a.x a.y‖ * ‖cx b.x b.y‖
        + ‖u - cx a.x a.y‖ * ‖v - cx b.x b.y‖ := by
    have he : u * v - cx a.x a.y * cx b.x b.y
        = cx a.x a.y * (v - cx b.x b.y) + (u - cx a.x a.y) * cx b.x b.y
          + (u - cx a.x a.y) * (v - cx b.x b.y) := by ring
    rw [he]
    calc ‖cx a.x a.y * (v - cx b.x b.y) + (u - cx a.x a.y) * cx b.x b.y
            + (u - cx a.x a.y) * (v - cx b.x b.y)‖
        ≤ ‖cx a.x a.y * (v - cx b.x b.y) + (u - cx a.x a.y) * cx b.x b.y‖
          + ‖(u - cx a.x a.y) * (v - cx b.x b.y)‖ := norm_add_le _ _
      _ ≤ (‖cx a.x a.y * (v - cx b.x b.y)‖ + ‖(u - cx a.x a.y) * cx b.x b.y‖)
          + ‖(u - cx a.x a.y) * (v - cx b.x b.y)‖ := by
          linarith [norm_add_le (cx a.x a.y * (v - cx b.x b.y))
            ((u - cx a.x a.y) * cx b.x b.y)]
      _ = ‖cx a.x a.y‖ * ‖v - cx b.x b.y‖ + ‖u - cx a.x a.y‖ * ‖cx b.x b.y‖
          + ‖u - cx a.x a.y‖ * ‖v - cx b.x b.y‖ := by rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖cx a.x a.y‖ * ‖v - cx b.x b.y‖ ≤ (((bmod a : ℤ) : ℝ) / (S : ℝ)) * ((b.r : ℝ) / (S : ℝ)) :=
    mul_le_mul hna hb (norm_nonneg _) hna0
  have h2 : ‖u - cx a.x a.y‖ * ‖cx b.x b.y‖ ≤ ((a.r : ℝ) / (S : ℝ)) * (((bmod b : ℤ) : ℝ) / (S : ℝ)) :=
    mul_le_mul ha hnb (norm_nonneg _) hra
  have h3 : ‖u - cx a.x a.y‖ * ‖v - cx b.x b.y‖ ≤ ((a.r : ℝ) / (S : ℝ)) * ((b.r : ℝ) / (S : ℝ)) :=
    mul_le_mul ha hb (norm_nonneg _) hra
  have hm1 : (((bmod a : ℤ) : ℝ) / (S : ℝ)) * ((b.r : ℝ) / (S : ℝ))
      ≤ ((mu (bmod a) b.r : ℤ) : ℝ) / (S : ℝ) := by
    have h := mu_ge (bmod a) b.r
    calc (((bmod a : ℤ) : ℝ) / (S : ℝ)) * ((b.r : ℝ) / (S : ℝ))
        = (((bmod a : ℤ) : ℝ) * (b.r : ℝ) / (S : ℝ)) / (S : ℝ) := by ring
      _ ≤ ((mu (bmod a) b.r : ℤ) : ℝ) / (S : ℝ) := div_le_div_of_nonneg_right h S_posR.le
  have hm2 : ((a.r : ℝ) / (S : ℝ)) * (((bmod b : ℤ) : ℝ) / (S : ℝ))
      ≤ ((mu (bmod b) a.r : ℤ) : ℝ) / (S : ℝ) := by
    have h := mu_ge (bmod b) a.r
    calc ((a.r : ℝ) / (S : ℝ)) * (((bmod b : ℤ) : ℝ) / (S : ℝ))
        = (((bmod b : ℤ) : ℝ) * (a.r : ℝ) / (S : ℝ)) / (S : ℝ) := by ring
      _ ≤ ((mu (bmod b) a.r : ℤ) : ℝ) / (S : ℝ) := div_le_div_of_nonneg_right h S_posR.le
  have hm3 : ((a.r : ℝ) / (S : ℝ)) * ((b.r : ℝ) / (S : ℝ))
      ≤ ((mu a.r b.r : ℤ) : ℝ) / (S : ℝ) := by
    have h := mu_ge a.r b.r
    calc ((a.r : ℝ) / (S : ℝ)) * ((b.r : ℝ) / (S : ℝ))
        = ((a.r : ℝ) * (b.r : ℝ) / (S : ℝ)) / (S : ℝ) := by ring
      _ ≤ ((mu a.r b.r : ℤ) : ℝ) / (S : ℝ) := div_le_div_of_nonneg_right h S_posR.le
  have hsum : ‖u * v - cx a.x a.y * cx b.x b.y‖
      ≤ (((mu (bmod a) b.r + mu (bmod b) a.r + mu a.r b.r : ℤ) : ℝ)) / (S : ℝ) := by
    calc ‖u * v - cx a.x a.y * cx b.x b.y‖
        ≤ (‖cx a.x a.y‖ * ‖v - cx b.x b.y‖) + (‖u - cx a.x a.y‖ * ‖cx b.x b.y‖)
          + (‖u - cx a.x a.y‖ * ‖v - cx b.x b.y‖) := htri
      _ ≤ (((mu (bmod a) b.r : ℤ) : ℝ) / (S : ℝ)) + (((mu (bmod b) a.r : ℤ) : ℝ) / (S : ℝ))
          + (((mu a.r b.r : ℤ) : ℝ) / (S : ℝ)) := by linarith
      _ = (((mu (bmod a) b.r + mu (bmod b) a.r + mu a.r b.r : ℤ) : ℝ)) / (S : ℝ) := by
          push_cast; ring
  have hcenter := bmul_center_le a b
  calc ‖u * v - cx (bmul a b).x (bmul a b).y‖
      ≤ ‖u * v - cx a.x a.y * cx b.x b.y‖
        + ‖cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y‖ := by
        have := norm_add_le (u * v - cx a.x a.y * cx b.x b.y)
          (cx a.x a.y * cx b.x b.y - cx (bmul a b).x (bmul a b).y)
        rwa [sub_add_sub_cancel] at this
    _ ≤ (((mu (bmod a) b.r + mu (bmod b) a.r + mu a.r b.r : ℤ) : ℝ)) / (S : ℝ) + 3 / (S : ℝ) :=
        add_le_add hsum hcenter
    _ = ((bmul a b).r : ℝ) / (S : ℝ) := by
        push_cast [bmul]; ring



theorem ball_ops :
    (∀ (a b : Bl) (z w : ℂ), ‖z - cx a.x a.y‖ ≤ (a.r : ℝ) / S → ‖w - cx b.x b.y‖ ≤ (b.r : ℝ) / S →
      ‖(z + w) - cx (badd a b).x (badd a b).y‖ ≤ ((badd a b).r : ℝ) / S ∧
      ‖(z - w) - cx (bsub a b).x (bsub a b).y‖ ≤ ((bsub a b).r : ℝ) / S ∧
      ‖z * w - cx (bmul a b).x (bmul a b).y‖ ≤ ((bmul a b).r : ℝ) / S) ∧
    (∀ (a : Bl) (L : ℤ) (z : ℂ), binvOK a L = true → ‖z - cx a.x a.y‖ ≤ (a.r : ℝ) / S →
      z ≠ 0 ∧ ‖z⁻¹ - cx (binv a L).x (binv a L).y‖ ≤ ((binv a L).r : ℝ) / S) ∧
    (∀ (a : Bl) (sr si : ℤ) (z : ℂ), bsqrtOK a sr = true → ‖z - cx a.x a.y‖ ≤ (a.r : ℝ) / S →
      ‖z ^ (1 / 2 : ℂ) - cx (bsqrt a sr si).x (bsqrt a sr si).y‖ ≤ ((bsqrt a sr si).r : ℝ) / S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b z w hz hw
    exact ⟨ballMem_badd hz hw, ballMem_bsub hz hw, bmul_sound hz hw⟩
  · intro a L z h hz
    exact binv_sound h hz
  · intro a sr si z h hz
    exact bsqrt_sound h hz

end Work.Cert
