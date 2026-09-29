import Mathlib
import Submission.Work.Cert.LeafAux

/-! # Membership of `(491/500)·z` in the stage-0 disc

The `leafOK` soundness proof starts by replacing the exact input disc of a leaf, centred at
`leafC L = cx (leafCx L) (leafCy L)` with radius `leafRz L / S`, by the rounded disc `stage0 L`.
This file proves exactly that membership step: for `z` in the input disc,
`(491/500)·z` lies in the disc `(md K491 (leafCx L), md K491 (leafCy L))`, radius
`mu (leafRz L) K491 + 2` (at scale `S`).
-/

namespace Work.Cert
open Complex

/-- `‖(r : ℂ)‖ = |r|`. -/
lemma norm_ofReal_cx (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  rw [← Real.sqrt_sq_eq_abs, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- the floor `md K491 a` lies within `1` ulp of `(491/500)·a`. -/
lemma md_K491_close (a : ℤ) :
    |((md K491 a : ℤ) : ℝ) - (491 / 500 : ℝ) * (a : ℝ)| ≤ 1 := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  have h1 : (S : ℝ) * (491 / 500) * (a : ℝ) / (S : ℝ) = (491 / 500 : ℝ) * (a : ℝ) := by
    field_simp
  have hle : ((md K491 a : ℤ) : ℝ) ≤ (491 / 500 : ℝ) * (a : ℝ) := by
    have h := md_le K491 a
    rw [K491_eq] at h
    linarith [h, h1]
  have hgt : (491 / 500 : ℝ) * (a : ℝ) - 1 < ((md K491 a : ℤ) : ℝ) := by
    have h := md_gt K491 a
    rw [K491_eq] at h
    linarith [h, h1]
  rw [abs_le]
  constructor <;> linarith

/-- the complex difference `(t:ℂ)·cx x y − cx m n` written as a scaled `cx`. -/
lemma smul_cx_sub_eq (x y m n : ℤ) (t : ℝ) :
    (t : ℂ) * cx x y - cx m n
      = (((t * (x : ℝ) - (m : ℝ)) / (S : ℝ) : ℝ) : ℂ)
        + (((t * (y : ℝ) - (n : ℝ)) / (S : ℝ) : ℝ) : ℂ) * I := by
  refine Complex.ext ?_ ?_ <;>
    simp [cx, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- norm bound for the rounding error of `(t:ℂ)·cx x y − cx m n`. -/
lemma smul_cx_sub_le (x y m n : ℤ) (t : ℝ) :
    ‖(t : ℂ) * cx x y - cx m n‖
      ≤ (|t * (x : ℝ) - (m : ℝ)| + |t * (y : ℝ) - (n : ℝ)|) / (S : ℝ) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := S_posR
  rw [smul_cx_sub_eq]
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [abs_div, abs_div, abs_of_pos hSpos]
  have hh : |t * (x : ℝ) - (m : ℝ)| / (S : ℝ) + |t * (y : ℝ) - (n : ℝ)| / (S : ℝ)
      = (|t * (x : ℝ) - (m : ℝ)| + |t * (y : ℝ) - (n : ℝ)|) / (S : ℝ) := by
    field_simp
  exact le_of_eq hh

theorem leaf_st0_mem (L : Work.Cert.Leaf) (z : ℂ) (hz : ‖z - Work.Cert.leafC L‖ ≤ Work.Cert.leafR L) :
    ‖(491 / 500 : ℂ) * z - Work.Cert.cx (Work.Cert.stage0 L).cr (Work.Cert.stage0 L).ci‖
      ≤ ((Work.Cert.stage0 L).rho : ℝ) / (Work.Cert.S : ℝ) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := S_posR
  have hSne : (S : ℝ) ≠ 0 := ne_of_gt hSpos
  have hR : (0 : ℝ) ≤ leafR L := le_trans (norm_nonneg _) hz
  have hstage : (stage0 L).cr = md K491 (leafCx L) ∧ (stage0 L).ci = md K491 (leafCy L) ∧
      (stage0 L).rho = mu (leafRz L) K491 + 2 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [stage0]
  obtain ⟨hcr, hci, hrho⟩ := hstage
  rw [hcr, hci, hrho]
  have hleafC : leafC L = cx (leafCx L) (leafCy L) := rfl
  have ht : (491 / 500 : ℂ) = ((491 / 500 : ℝ) : ℂ) := by norm_num
  have hnormt : ‖(491 / 500 : ℂ)‖ = (491 / 500 : ℝ) := by
    rw [ht, norm_ofReal_cx]; norm_num
  have hsplit : (491 / 500 : ℂ) * z - cx (md K491 (leafCx L)) (md K491 (leafCy L))
      = (491 / 500 : ℂ) * (z - leafC L)
        + ((491 / 500 : ℂ) * leafC L - cx (md K491 (leafCx L)) (md K491 (leafCy L))) := by
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(491 / 500 : ℂ) * (z - leafC L)‖ ≤ (491 / 500 : ℝ) * leafR L := by
    rw [norm_mul, hnormt]
    exact mul_le_mul_of_nonneg_left hz (by norm_num)
  have h2 : ‖(491 / 500 : ℂ) * leafC L - cx (md K491 (leafCx L)) (md K491 (leafCy L))‖
      ≤ 2 / (S : ℝ) := by
    rw [ht, hleafC]
    refine le_trans (smul_cx_sub_le (leafCx L) (leafCy L) (md K491 (leafCx L))
      (md K491 (leafCy L)) (491 / 500)) ?_
    have hb1 : |(491 / 500 : ℝ) * (leafCx L : ℝ) - ((md K491 (leafCx L) : ℤ) : ℝ)| ≤ 1 := by
      have := md_K491_close (leafCx L); rwa [abs_sub_comm] at this
    have hb2 : |(491 / 500 : ℝ) * (leafCy L : ℝ) - ((md K491 (leafCy L) : ℤ) : ℝ)| ≤ 1 := by
      have := md_K491_close (leafCy L); rwa [abs_sub_comm] at this
    have hsum : |(491 / 500 : ℝ) * (leafCx L : ℝ) - ((md K491 (leafCx L) : ℤ) : ℝ)|
        + |(491 / 500 : ℝ) * (leafCy L : ℝ) - ((md K491 (leafCy L) : ℤ) : ℝ)| ≤ 2 := by
      linarith
    exact div_le_div_of_nonneg_right hsum hSpos.le
  have h3 : (491 / 500 : ℝ) * leafR L + 2 / (S : ℝ)
      ≤ (((mu (leafRz L) K491 + 2 : ℤ)) : ℝ) / (S : ℝ) := by
    have hmuk : (491 / 500 : ℝ) * (leafRz L : ℝ) ≤ ((mu (leafRz L) K491 : ℤ) : ℝ) := by
      have h := mu_ge (leafRz L) K491
      rw [K491_eq] at h
      have h2 : (leafRz L : ℝ) * ((S : ℝ) * (491 / 500)) / (S : ℝ)
          = (491 / 500) * (leafRz L : ℝ) := by
        field_simp
      linarith [h, h2]
    have hleafR : leafR L = (leafRz L : ℝ) / (S : ℝ) := rfl
    rw [hleafR]
    have hcomb : (491 / 500 : ℝ) * ((leafRz L : ℝ) / (S : ℝ)) + 2 / (S : ℝ)
        = ((491 / 500) * (leafRz L : ℝ) + 2) / (S : ℝ) := by
      field_simp
    rw [hcomb]
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hSpos.le
  linarith

end Work.Cert
