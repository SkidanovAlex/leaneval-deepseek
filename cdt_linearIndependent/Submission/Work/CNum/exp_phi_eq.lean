import Mathlib
import Submission.Work.CNum.Basic

/-!
# `Work.CNum.exp_phi_eq`

The polar form of `Wfun` on the `C₁` arc: for `θ ∈ (-α, α)` (`α = arccos γ` the cusp
half-angle of the unit circle),

`Complex.exp (Complex.I * (phiR θ : ℂ)) = Wfun (Complex.exp (Complex.I * (θ : ℂ)))`.

The proof unfolds both sides explicitly: on the unit circle `z = e^{iθ}`,
`1 + z = 2 cos(θ/2) e^{iθ/2}` and `z - 1 = 2i sin(θ/2) e^{iθ/2}`, so that

`Ra z = A (1+z)^2 - B z = PR θ ^ 2 · e^{iθ}` (with principal square root
`PR θ · e^{iθ/2}`), and using `PR θ ^ 2 + QR θ ^ 2 = dR ^ 2` on the circle one finds
`Wfun z = -(PR θ + i QR θ) e^{iθ/2} / dR = e^{i(θ/2 + π + arctan(QR θ / PR θ))}`.
-/

namespace Work.CNum
namespace ExpPhi

/-! ## The numerical constants -/

lemma cR_gt_one : 1 < cR := by unfold cR; norm_num

lemma AR_pos : 0 < AR := by unfold AR cR; norm_num

lemma dR_pos : 0 < dR := by unfold dR cR; norm_num

lemma gamR_bounds : -1 ≤ gamR ∧ gamR ≤ 1 := by
  unfold gamR AR cR; constructor <;> norm_num

lemma gamR_lt_one : gamR < 1 := by unfold gamR AR cR; norm_num

lemma gamR_gt_neg_one : -1 < gamR := by unfold gamR AR cR; norm_num

lemma cos_alpR : Real.cos alpR = gamR := Real.cos_arccos gamR_bounds.1 gamR_bounds.2

lemma alpR_pos : 0 < alpR := Real.arccos_pos.mpr gamR_lt_one

lemma alpR_lt_pi : alpR < Real.pi := Real.arccos_lt_pi.mpr gamR_gt_neg_one

lemma abs_lt_alpR {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) : |θ| < alpR := by
  rw [abs_lt]; exact h

lemma cos_gt_gamR {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) : gamR < Real.cos θ := by
  have habs := abs_lt_alpR h
  have h1 : |θ| ∈ Set.Icc (0 : ℝ) Real.pi :=
    Set.mem_Icc.mpr ⟨abs_nonneg θ, le_of_lt (lt_trans habs alpR_lt_pi)⟩
  have h2 : alpR ∈ Set.Icc (0 : ℝ) Real.pi := Set.mem_Icc.mpr ⟨alpR_pos.le, alpR_lt_pi.le⟩
  have := Real.strictAntiOn_cos h1 h2 habs
  rwa [cos_alpR, Real.cos_abs] at this

/-! ## The real functions `PR`, `QR` on the arc -/

lemma PR_pos {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) : 0 < PR θ := by
  have hcos := cos_gt_gamR h
  have hAR := AR_pos
  rw [PR]
  apply Real.sqrt_pos.mpr
  have h1 : 0 < 2 * AR := by linarith
  exact mul_pos h1 (by linarith)

lemma PR_sq {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    PR θ ^ 2 = 2 * AR * (Real.cos θ - gamR) := by
  have hcos := cos_gt_gamR h
  have hAR := AR_pos
  have hnn : 0 ≤ 2 * AR * (Real.cos θ - gamR) := by
    have h1 : 0 < 2 * AR := by linarith
    exact (mul_pos h1 (by linarith)).le
  rw [PR, Real.sq_sqrt hnn]

lemma PRQ_sq {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) : PR θ ^ 2 + QR θ ^ 2 = dR ^ 2 := by
  rw [PR_sq h, QR]
  have hcos2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at this
  rw [hcos2]
  have hsin := Real.sin_sq_add_cos_sq (θ / 2)
  have hA : AR = 395641 / 10000 := by unfold AR cR; norm_num
  have hg : gamR = 27559 / 395641 := by unfold gamR AR cR; norm_num
  have hd : dR = 429 / 50 := by unfold dR cR; norm_num
  have hc : cR = 23 / 10 := rfl
  rw [hA, hg, hd, hc] at *
  nlinarith [hsin]

/-! ## The complex exponential identities -/

lemma exp_half_sq (θ : ℝ) :
    Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) ^ 2 = Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma one_add_exp (θ : ℝ) :
    1 + Complex.exp (Complex.I * (θ : ℂ)) =
      2 * (Real.cos (θ / 2) : ℂ) * Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) := by
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I θ
  have h2 : Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) =
      (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I (θ / 2)
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at this
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at this
  rw [h1, h2, hc, hs]
  push_cast
  ring

lemma exp_I_sub_one (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) - 1 =
      2 * Complex.I * (Real.sin (θ / 2) : ℂ) * Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) := by
  have hw2 : Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]; congr 1; push_cast; ring
  have hwne : Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hinv : (Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)))⁻¹ =
      Complex.exp (Complex.I * (((-(θ / 2) : ℝ)) : ℂ)) := by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring
  have hsub : Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) -
        (Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)))⁻¹ =
        2 * Complex.I * (Real.sin (θ / 2) : ℂ) := by
    rw [hinv]
    have h1 : Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) =
        (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
      rw [mul_comm]; exact Complex.exp_ofReal_mul_I (θ / 2)
    have h2 : Complex.exp (Complex.I * (((-(θ / 2) : ℝ)) : ℂ)) =
        (Real.cos (θ / 2) : ℂ) - (Real.sin (θ / 2) : ℂ) * Complex.I := by
      rw [mul_comm, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [h1, h2]; ring
  have hfac : Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) - 1 =
      Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) *
        (Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) -
          (Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)))⁻¹) := by
    rw [mul_sub, mul_inv_cancel₀ hwne]
  rw [hw2, pow_two, hfac, hsub]
  ring

/-! ## The explicit value of `Ra` and of `sqrt (Ra)` on the arc -/

lemma Ra_exp_sq {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Ra (Complex.exp (Complex.I * (θ : ℂ))) =
      ((PR θ : ℂ) * Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ))) ^ 2 := by
  set w : ℂ := Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) with hw
  have hcoef : AR * (2 * Real.cos (θ / 2)) ^ 2 - BR = (PR θ) ^ 2 := by
    rw [PR_sq h]
    have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (θ / 2); rwa [show 2 * (θ / 2) = θ by ring] at this
    rw [hc]
    have hA : AR = 395641 / 10000 := by unfold AR cR; norm_num
    have hg : gamR = 27559 / 395641 := by unfold gamR AR cR; norm_num
    have hB : BR = 2116 / 25 := by unfold BR cR; norm_num
    rw [hA, hg, hB]; ring
  have hkeyC : (↑AR) * (2 * (↑(Real.cos (θ / 2)))) ^ 2 - (↑BR) = ((PR θ : ℂ)) ^ 2 := by
    have h1 : ((AR * (2 * Real.cos (θ / 2)) ^ 2 - BR : ℝ) : ℂ) =
        (↑AR) * (2 * (↑(Real.cos (θ / 2)))) ^ 2 - (↑BR) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    calc (↑AR) * (2 * (↑(Real.cos (θ / 2)))) ^ 2 - (↑BR)
        = ((AR * (2 * Real.cos (θ / 2)) ^ 2 - BR : ℝ) : ℂ) := h1.symm
      _ = ((PR θ ^ 2 : ℝ) : ℂ) := by rw [hcoef]
      _ = ((PR θ : ℂ)) ^ 2 := by rw [Complex.ofReal_pow]
  have hone : 1 + Complex.exp (Complex.I * (θ : ℂ)) = 2 * (↑(Real.cos (θ / 2))) * w := by
    rw [hw]; exact one_add_exp θ
  have hwe : Complex.exp (Complex.I * (θ : ℂ)) = w ^ 2 := by
    rw [hw]; exact (exp_half_sq θ).symm
  have hfac : (↑AR) * (2 * (↑(Real.cos (θ / 2))) * w) ^ 2 - (↑BR) * w ^ 2 =
      ((↑AR) * (2 * (↑(Real.cos (θ / 2)))) ^ 2 - (↑BR)) * w ^ 2 := by ring
  unfold Ra
  rw [hone, hwe, hfac, hkeyC]
  ring

lemma sqrt_Ra_exp {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ)))) =
      (PR θ : ℂ) * Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) := by
  have hPpos := PR_pos h
  have hPne : (PR θ : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hwne : Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hne : ((PR θ : ℂ) * Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ))) ≠ 0 :=
    mul_ne_zero hPne hwne
  have hRa := Ra_exp_sq h
  have habs := abs_lt_alpR h
  have hlog : Complex.log (Ra (Complex.exp (Complex.I * (θ : ℂ)))) =
      2 * ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ)) := by
    rw [hRa]
    have hPe : (PR θ : ℂ) * Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ)) =
        Complex.exp ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ)) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hPpos]
    rw [hPe, pow_two, ← Complex.exp_add]
    have hsum : ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ)) +
        ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ)) =
        2 * ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ)) := by ring
    rw [hsum]
    have him : (2 * ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ))).im = θ := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
      ring
    have hθ := abs_lt.mp habs
    rw [Complex.log_exp]
    · rw [him]; linarith [hθ.1, alpR_lt_pi]
    · rw [him]; linarith [hθ.2, alpR_lt_pi]
  rw [sqrt_eq_exp (by rw [hRa]; exact pow_ne_zero 2 hne), hlog]
  have hhalf : 2 * ((Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ)) / 2 =
      (Real.log (PR θ) : ℂ) + Complex.I * (((θ / 2 : ℝ)) : ℂ) := by ring
  rw [hhalf, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hPpos]

/-! ## The value of `Wfun` on the arc -/

lemma Wfun_eval {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Wfun (Complex.exp (Complex.I * (θ : ℂ))) =
      -(((PR θ : ℂ) + Complex.I * (QR θ : ℂ)) *
          Complex.exp (Complex.I * (((θ / 2 : ℝ)) : ℂ))) / (dR : ℂ) := by
  have hQRc : (QR θ : ℂ) = 2 * (1 + (cR : ℂ) ^ 2) * (Real.sin (θ / 2) : ℂ) := by
    unfold QR
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  unfold Wfun
  rw [sqrt_Ra_exp h, exp_I_sub_one θ, hQRc]
  ring

end ExpPhi

open ExpPhi

theorem exp_phi_eq {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Complex.exp (Complex.I * (phiR θ : ℂ)) = Wfun (Complex.exp (Complex.I * (θ : ℂ))) := by
  set t : ℝ := θ / 2 with ht
  set P : ℝ := PR θ with hP
  set Q : ℝ := QR θ with hQ
  set d : ℝ := dR with hd
  have hdpos : 0 < d := by rw [hd]; exact dR_pos
  have hPpos : 0 < P := by rw [hP]; exact PR_pos h
  have hPQ : P ^ 2 + Q ^ 2 = d ^ 2 := by rw [hP, hQ, hd]; exact PRQ_sq h
  set ψ : ℝ := Real.arctan (Q / P) with hψ
  have hPne : P ≠ 0 := hPpos.ne'
  have hdne : d ≠ 0 := hdpos.ne'
  have hx : 1 + (Q / P) ^ 2 = d ^ 2 / P ^ 2 := by
    field_simp
    nlinarith [hPQ]
  have hs : Real.sqrt (1 + (Q / P) ^ 2) = d / P := by
    rw [hx, Real.sqrt_div (sq_nonneg d), Real.sqrt_sq hdpos.le, Real.sqrt_sq hPpos.le]
  have hcosψ : Real.cos ψ = P / d := by
    rw [hψ, Real.cos_arctan, hs]
    field_simp
  have hsinψ : Real.sin ψ = Q / d := by
    rw [hψ, Real.sin_arctan, hs]
    field_simp
  have hmain : Complex.exp (Complex.I * (((Real.pi + ψ : ℝ)) : ℂ)) =
      -(((P : ℂ) + Complex.I * (Q : ℂ)) / (d : ℂ)) := by
    rw [show Complex.I * (((Real.pi + ψ : ℝ)) : ℂ) =
        (((Real.pi + ψ : ℝ)) : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I]
    rw [show Real.pi + ψ = ψ + Real.pi by ring, Real.cos_add_pi, Real.sin_add_pi,
      hcosψ, hsinψ]
    push_cast
    ring
  have hphi : phiR θ = t + (Real.pi + ψ) := by
    rw [phiR, hψ, ht, hP, hQ]
    ring
  have hsplit : -(((P : ℂ) + Complex.I * (Q : ℂ)) * Complex.exp (Complex.I * (t : ℂ))) / (d : ℂ)
      = Complex.exp (Complex.I * (t : ℂ)) * (-(((P : ℂ) + Complex.I * (Q : ℂ)) / (d : ℂ))) := by
    ring
  rw [Wfun_eval h, hP.symm, hQ.symm, hd.symm, ht.symm, hphi, hsplit, ← hmain, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Work.CNum
