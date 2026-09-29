import Mathlib
import Submission.Work.Cert.WL.Defs

/-! # The disc of `q · X^8`

`prod_disc` bounds a product of two disc memberships, and `prod256_sound` scales it by `256` with
the `ETOL` slack used by `gDisc`'s `grg`.
-/
set_option maxRecDepth 100000
namespace Work.Cert
namespace WL

open Complex

/-- The disc of a product of two disc memberships. -/
theorem prod_disc (qr qi rq y1 y2 r8 : ℤ) (q x : ℂ)
    (hq : ‖q - cx qr qi‖ ≤ ((rq : ℤ) : ℝ) / (S : ℝ))
    (hx : ‖x - cx y1 y2‖ ≤ ((r8 : ℤ) : ℝ) / (S : ℝ)) :
    ‖q * x - cx (cmr qr qi y1 y2) (cmi qr qi y1 y2)‖ ≤
      ((mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8 + 4 : ℤ) : ℝ)
        / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  set A : ℂ := cx qr qi with hAd
  set B : ℂ := cx y1 y2 with hBd
  set C : ℂ := cx (cmr qr qi y1 y2) (cmi qr qi y1 y2) with hCd
  have hA : ‖A‖ ≤ (((iabs qr + iabs qi : ℤ)) : ℝ) / (S : ℝ) := by
    rw [hAd]
    calc ‖cx qr qi‖ ≤ (|(qr : ℝ)| + |(qi : ℝ)|) / (S : ℝ) := norm_cx_le_abs _ _
      _ = (((iabs qr + iabs qi : ℤ)) : ℝ) / (S : ℝ) := by
          push_cast
          simp only [iabs_abs]
  have hB : ‖B‖ ≤ (((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ) := by
    rw [hBd]
    calc ‖cx y1 y2‖ ≤ (|(y1 : ℝ)| + |(y2 : ℝ)|) / (S : ℝ) := norm_cx_le_abs _ _
      _ = (((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ) := by
          push_cast
          simp only [iabs_abs]
  have hrq0 : (0 : ℝ) ≤ ((rq : ℤ) : ℝ) / (S : ℝ) := le_trans (norm_nonneg _) hq
  have hpq : ‖q - A‖ ≤ ((rq : ℤ) : ℝ) / (S : ℝ) := hq
  have hpx : ‖x - B‖ ≤ ((r8 : ℤ) : ℝ) / (S : ℝ) := hx
  have hAB : ‖A * B - C‖ ≤ 4 / (S : ℝ) := by
    rw [hAd, hBd, hCd, norm_sub_rev]
    exact cx_mul_le' qr qi y1 y2
  have hsplit : q * x - C = ((q - A) * (x - B) + A * (x - B)) + ((q - A) * B + (A * B - C)) := by
    ring
  have t1 : ‖(q - A) * (x - B)‖ ≤ (((rq : ℤ) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul hpq hpx (norm_nonneg _) hrq0
  have t2 : ‖A * (x - B)‖ ≤ ((((iabs qr + iabs qi : ℤ)) : ℝ) / (S : ℝ)) *
      (((r8 : ℤ) : ℝ) / (S : ℝ)) := by
    rw [norm_mul]
    have hA0 : (0 : ℝ) ≤ (((iabs qr + iabs qi : ℤ)) : ℝ) := by
      have h : (0 : ℤ) ≤ iabs qr + iabs qi := by
        have h1 := iabs_nonneg qr
        have h2 := iabs_nonneg qi
        omega
      exact_mod_cast h
    exact mul_le_mul hA hpx (norm_nonneg _) (div_nonneg hA0 (le_of_lt hS))
  have t3 : ‖(q - A) * B‖ ≤ (((rq : ℤ) : ℝ) / (S : ℝ)) *
      ((((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul hpq hB (norm_nonneg _) hrq0
  have hsum : ‖q * x - C‖ ≤ (((rq : ℤ) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) +
      ((((iabs qr + iabs qi : ℤ)) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) +
      (((rq : ℤ) : ℝ) / (S : ℝ)) * ((((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ)) + 4 / (S : ℝ) := by
    calc ‖q * x - C‖
        = ‖((q - A) * (x - B) + A * (x - B)) + ((q - A) * B + (A * B - C))‖ := by rw [hsplit]
      _ ≤ ‖(q - A) * (x - B) + A * (x - B)‖ + ‖(q - A) * B + (A * B - C)‖ := norm_add_le _ _
      _ ≤ (‖(q - A) * (x - B)‖ + ‖A * (x - B)‖) + (‖(q - A) * B‖ + ‖A * B - C‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ _ := by linarith [t1, t2, t3, hAB]
  have hkey : (((rq : ℤ) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) +
      ((((iabs qr + iabs qi : ℤ)) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) +
      (((rq : ℤ) : ℝ) / (S : ℝ)) * ((((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ)) + 4 / (S : ℝ)
      ≤ ((mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8 + 4 : ℤ) : ℝ)
        / (S : ℝ) := by
    have m1 := mu_ge (iabs qr + iabs qi) r8
    have m2 := mu_ge (iabs y1 + iabs y2) rq
    have m3 := mu_ge rq r8
    have e1 : (((rq : ℤ) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) =
        (((rq : ℤ) : ℝ) * ((r8 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ) := by ring
    have e2 : ((((iabs qr + iabs qi : ℤ)) : ℝ) / (S : ℝ)) * (((r8 : ℤ) : ℝ) / (S : ℝ)) =
        ((((iabs qr + iabs qi : ℤ)) : ℝ) * ((r8 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ) := by ring
    have e3 : (((rq : ℤ) : ℝ) / (S : ℝ)) * ((((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ)) =
        (((rq : ℤ) : ℝ) * (((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ)) / (S : ℝ) := by ring
    have e4 : ((mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8 + 4 : ℤ) : ℝ)
        / (S : ℝ) = ((mu (iabs qr + iabs qi) r8 : ℤ) : ℝ) / (S : ℝ) +
          ((mu (iabs y1 + iabs y2) rq : ℤ) : ℝ) / (S : ℝ) +
          ((mu rq r8 : ℤ) : ℝ) / (S : ℝ) + 4 / (S : ℝ) := by push_cast; ring
    rw [e1, e2, e3, e4]
    have h1 : (((rq : ℤ) : ℝ) * ((r8 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ) ≤
        ((mu rq r8 : ℤ) : ℝ) / (S : ℝ) := div_le_div_of_nonneg_right m3 (le_of_lt hS)
    have h2 : ((((iabs qr + iabs qi : ℤ)) : ℝ) * ((r8 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ) ≤
        ((mu (iabs qr + iabs qi) r8 : ℤ) : ℝ) / (S : ℝ) :=
      div_le_div_of_nonneg_right m1 (le_of_lt hS)
    have h3 : (((rq : ℤ) : ℝ) * (((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ)) / (S : ℝ) ≤
        ((mu (iabs y1 + iabs y2) rq : ℤ) : ℝ) / (S : ℝ) :=
      div_le_div_of_nonneg_right (by
        calc ((rq : ℝ) * (((iabs y1 + iabs y2 : ℤ)) : ℝ) / (S : ℝ))
            = ((((iabs y1 + iabs y2 : ℤ)) : ℝ) * (rq : ℝ) / (S : ℝ)) := by ring
          _ ≤ ((mu (iabs y1 + iabs y2) rq : ℤ) : ℝ) := m2) (le_of_lt hS)
    linarith
  linarith [hsum, hkey]

/-- The `256`-scaled product disc of `q · X^8`, with the `ETOL` slack of `grg`. -/
theorem prod256_sound (qr qi rq y1 y2 r8 : ℤ) (q x : ℂ)
    (hq : ‖q - cx qr qi‖ ≤ ((rq : ℤ) : ℝ) / (S : ℝ))
    (hx : ‖x - cx y1 y2‖ ≤ ((r8 : ℤ) : ℝ) / (S : ℝ)) :
    ‖(256 : ℂ) * (q * x) - cx (256 * cmr qr qi y1 y2) (256 * cmi qr qi y1 y2)‖ ≤
      ((256 * (mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8) + ETOL : ℤ) : ℝ)
        / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  have hpd := prod_disc qr qi rq y1 y2 r8 q x hq hx
  have hc : cx (256 * cmr qr qi y1 y2) (256 * cmi qr qi y1 y2) =
      256 * cx (cmr qr qi y1 y2) (cmi qr qi y1 y2) := by
    simp only [cx]
    push_cast
    ring
  have hmul : ‖(256 : ℂ) * (q * x) - cx (256 * cmr qr qi y1 y2) (256 * cmi qr qi y1 y2)‖ =
      256 * ‖q * x - cx (cmr qr qi y1 y2) (cmi qr qi y1 y2)‖ := by
    rw [hc, ← mul_sub, norm_mul]
    norm_num
  rw [hmul]
  have hstep : 256 * (((mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8 + 4 : ℤ) : ℝ)
        / (S : ℝ)) ≤
      ((256 * (mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8) + ETOL : ℤ) : ℝ)
        / (S : ℝ) := by
    have e : 256 * (((mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8 + 4 : ℤ) : ℝ)
        / (S : ℝ)) =
        (256 * ((mu (iabs qr + iabs qi) r8 + mu (iabs y1 + iabs y2) rq + mu rq r8 + 4 : ℤ) : ℝ))
          / (S : ℝ) := by ring
    rw [e, div_le_div_iff_of_pos_right hS]
    push_cast
    have hET : (1024 : ℝ) ≤ (ETOL : ℝ) := by norm_num [ETOL]
    linarith
  linarith [hpd, hstep]

end WL
end Work.Cert
