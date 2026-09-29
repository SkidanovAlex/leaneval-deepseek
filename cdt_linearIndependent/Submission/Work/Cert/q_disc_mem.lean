import Mathlib
import Submission.Work.Cert.LeafAux

/-! # The rounding step `ψ_A`-disc → `q`-disc

`qrZ/qiZ/rqZ` are the mantissas of `q = -(4/5)·(stage5 value)`, obtained from the stage-5 centre
`(cr, ci)` by flooring/clamping at the exact constant `K45 = (4/5)·S`.  Multiplying a point of the
stage-5 disc by `-(4/5)` therefore moves its centre by the two one-ulp rounding errors
`e_j = (4/5)·c_j − md K45 c_j ∈ [0,1)`, and enlarges its radius by the factor `4/5`:
`√(e₁²+e₂²) ≤ 2` and `(4/5)ρ ≤ mu ρ K45`, which is exactly the slack `+2` in `rqZ`. -/

namespace Work.Cert

theorem q_disc_mem (L : Work.Cert.Leaf) (w : ℂ)
    (hw : ‖w - Work.Cert.cx (Work.Cert.stage5 L).cr (Work.Cert.stage5 L).ci‖
      ≤ ((Work.Cert.stage5 L).rho : ℝ) / (Work.Cert.S : ℝ)) :
    ‖(-(4 / 5 : ℂ)) * w - Work.Cert.cx (Work.Cert.qrZ L) (Work.Cert.qiZ L)‖
      ≤ ((Work.Cert.rqZ L : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := S_posR
  have h45 : ((4/5:ℂ)) = ((4/5:ℝ):ℂ) := by norm_num
  simp only [qrZ, qiZ, rqZ]
  set st : St := stage5 L with hst
  rcases st with ⟨ok, cr, ci, rho⟩
  dsimp only at hw ⊢
  rw [h45]
  -- write the input point as the stage-5 centre plus a displacement `δ`
  set δ : ℂ := w - cx cr ci with hδdef
  have hδ : ‖δ‖ ≤ ((rho:ℝ))/(S:ℝ) := hw
  -- the two rounding errors of the flooring by `K45 = (4/5)S`
  set e1 : ℝ := (4/5) * (cr:ℝ) - ((md K45 cr : ℤ) : ℝ) with he1
  set e2 : ℝ := (4/5) * (ci:ℝ) - ((md K45 ci : ℤ) : ℝ) with he2
  have hK : ((K45:ℤ):ℝ) * (cr:ℝ) / (S:ℝ) = (4/5) * (cr:ℝ) := by
    rw [K45_eq]
    field_simp
  have hK' : ((K45:ℤ):ℝ) * (ci:ℝ) / (S:ℝ) = (4/5) * (ci:ℝ) := by
    rw [K45_eq]
    field_simp
  have he1nn : 0 ≤ e1 := by
    have h := md_le K45 cr
    rw [hK] at h
    simp only [he1]
    linarith
  have he1lt : e1 < 1 := by
    have h := md_gt K45 cr
    rw [hK] at h
    simp only [he1]
    linarith
  have he2nn : 0 ≤ e2 := by
    have h := md_le K45 ci
    rw [hK'] at h
    simp only [he2]
    linarith
  have he2lt : e2 < 1 := by
    have h := md_gt K45 ci
    rw [hK'] at h
    simp only [he2]
    linarith
  -- the rounding part `A = -(4/5)·cx cr ci - cx qrZ qiZ` has coordinates `-e₁/S`, `-e₂/S`
  have hAre : ((-((4/5:ℝ):ℂ)) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))).re = -(e1/(S:ℝ)) := by
    rw [he1]
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, cx_re, cx_im]
    push_cast
    ring
  have hAim : ((-((4/5:ℝ):ℂ)) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))).im = -(e2/(S:ℝ)) := by
    rw [he2]
    simp only [Complex.sub_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, cx_re, cx_im]
    push_cast
    ring
  have hAnorm : ‖-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))‖ ≤ 2/(S:ℝ) := by
    calc ‖-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))‖
        ≤ |(-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))).re|
          + |(-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))).im|
          := Complex.norm_le_abs_re_add_abs_im _
      _ = e1/(S:ℝ) + e2/(S:ℝ) := by
            rw [hAre, hAim, abs_neg, abs_neg, abs_of_nonneg (div_nonneg he1nn hS.le),
              abs_of_nonneg (div_nonneg he2nn hS.le)]
      _ = (e1 + e2)/(S:ℝ) := by ring
      _ ≤ 2/(S:ℝ) := by
            apply div_le_div_of_nonneg_right _ hS.le
            linarith
  -- the displacement contributes `(4/5)|δ| ≤ (4/5)ρ/S`
  have hZeq : -((4/5:ℝ):ℂ) * w - cx (-(md K45 cr)) (-(md K45 ci))
      = (-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))) - ((4/5:ℝ):ℂ) * δ := by
    rw [hδdef]
    ring
  -- the ceiling of `(4/5)ρ` pays for the slack `2`
  have hmu : (4/5) * (rho:ℝ) ≤ ((mu rho K45 : ℤ):ℝ) := by
    have h := mu_ge rho K45
    have h' : ((rho:ℝ) * ((K45:ℤ):ℝ))/(S:ℝ) = (4/5) * (rho:ℝ) := by
      rw [K45_eq]
      field_simp
    linarith [h, h']
  have hfinal : 2/(S:ℝ) + (4/5) * ((rho:ℝ)/(S:ℝ)) ≤ ((mu rho K45 + 2 : ℤ):ℝ)/(S:ℝ) := by
    have hL : 2/(S:ℝ) + (4/5) * ((rho:ℝ)/(S:ℝ)) = (2 + (4/5)*(rho:ℝ))/(S:ℝ) := by ring
    rw [hL]
    apply div_le_div_of_nonneg_right _ hS.le
    push_cast
    linarith
  calc ‖-((4/5:ℝ):ℂ) * w - cx (-(md K45 cr)) (-(md K45 ci))‖
      ≤ 2/(S:ℝ) + (4/5) * ((rho:ℝ)/(S:ℝ)) := by
          calc ‖-((4/5:ℝ):ℂ) * w - cx (-(md K45 cr)) (-(md K45 ci))‖
              = ‖(-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))) - ((4/5:ℝ):ℂ) * δ‖ := by rw [hZeq]
            _ ≤ ‖-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))‖ + ‖((4/5:ℝ):ℂ) * δ‖ := norm_sub_le _ _
            _ = ‖-((4/5:ℝ):ℂ) * cx cr ci - cx (-(md K45 cr)) (-(md K45 ci))‖ + (4/5) * ‖δ‖ := by rw [norm_mul]; norm_num
            _ ≤ 2/(S:ℝ) + (4/5) * ((rho:ℝ)/(S:ℝ)) := by
                  have h2 : (4/5) * ‖δ‖ ≤ (4/5) * ((rho:ℝ)/(S:ℝ)) :=
                    mul_le_mul_of_nonneg_left hδ (by norm_num)
                  linarith [hAnorm]
    _ ≤ ((mu rho K45 + 2 : ℤ):ℝ)/(S:ℝ) := hfinal

end Work.Cert
