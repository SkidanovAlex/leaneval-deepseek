
/-
# ZeroFreeTables/XY/LamPrimeSup

The two supremum estimates of the order-2 `λ'`-section (`LamPrimeDefs`):
`Gfun 1 λ t ≤ 1/25` and `Hfun 1 λ t ≤ 1/25` for `0 ≤ λ ≤ 628/1000` and all `t`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData
import Submission.Work.ZeroFreeTables.XY.LamPrimeAux
import Submission.Work.ZeroFreeTables.XY.FcAddFcNeg
import Submission.Work.ZeroFreeTables.XY.SupE0
import Submission.Work.ZeroFreeTables.XY.SupEs
import Submission.Work.ZeroFreeTables.XY.SupCfun
import Submission.Work.ZeroFreeTables.XY.SupYcTaylor
import Submission.Work.ZeroFreeTables.XY.SupYcNonpos
import Submission.Work.ZeroFreeTables.XY.SupEcAbs
import Submission.Work.ZeroFreeTables.XY.SupScLe

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

open Work.ZeroFreeTables

/-- `xyRe` is even in the imaginary part. -/
lemma xyRe_neg (x t : ℝ) : xyRe x (-t) = xyRe x t := by
  rw [xyRe_eq_integral, xyRe_eq_integral]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show (-t)*u = -(t*u) by ring, Real.cos_neg]

/-- The square of `(a + b i)` for real `a`, `b`. -/
lemma sq_ofReal_add (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * Complex.I))^2
      = (((a^2 - b^2 : ℝ)) : ℂ) + (((2*a*b : ℝ)) : ℂ) * Complex.I := by
  calc (((a : ℂ) + (b : ℂ) * Complex.I))^2
      = (a : ℂ)^2 + ((b : ℂ)^2) * (Complex.I * Complex.I) + 2*((a : ℂ)*(b : ℂ))*Complex.I := by
        ring
    _ = (a : ℂ)^2 + ((b : ℂ)^2) * (-1) + 2*((a : ℂ)*(b : ℂ))*Complex.I := by
        rw [Complex.I_mul_I]
    _ = (((a^2 - b^2 : ℝ)) : ℂ) + (((2*a*b : ℝ)) : ℂ) * Complex.I := by push_cast; ring

/-- Real part of `A(it-λ)²`. -/
lemma Ac_it_sub_sq_re (lam t : ℝ) :
    (Ac ((t : ℂ) * Complex.I - (lam : ℂ))^2).re
      = 4 * ((Cc t + Ec lam t)^2 - (Bc lam t)^2) := by
  have hz : Ac ((t : ℂ) * Complex.I - (lam : ℂ))
      = ((2*(Cc t + Ec lam t) : ℝ) : ℂ) + (((-(2*Bc lam t)) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Ac_it_sub_re lam t]
      simp
    · rw [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Ac_it_sub_im lam t]
      simp
  rw [hz, sq_ofReal_add]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero]
  ring

/-- The exact form of `xyRe (-λ) t`. -/
theorem xyRe_neg_lam_eq (lam t : ℝ) :
    xyRe (-lam) t = 2*((Cc t + Ec lam t)^2 - (Bc lam t)^2) + Sc lam t := by
  have hz : -((t : ℂ) * Complex.I - (lam : ℂ)) = ((lam : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hz1 : ((-lam : ℝ) : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I - (lam : ℂ) := by
    push_cast; ring
  have hsum : (xyT.Fc ((t : ℂ) * Complex.I - (lam : ℂ))
        + xyT.Fc (-((t : ℂ) * Complex.I - (lam : ℂ)))).re
      = 4 * ((Cc t + Ec lam t)^2 - (Bc lam t)^2) := by
    rw [FcAddFcNeg]
    exact Ac_it_sub_sq_re lam t
  rw [Complex.add_re, hz] at hsum
  have hL : (xyT.Fc ((t : ℂ) * Complex.I - (lam : ℂ))).re = xyRe (-lam) t := by
    simp only [xyRe, hz1]
  have hR : (xyT.Fc (((lam : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)).re = xyRe lam (-t) := rfl
  rw [hL, hR, xyRe_neg lam t] at hsum
  have hsub := xyRe_sub_lam lam t
  linarith

/-- The exact form of `xyRe 0 t`. -/
theorem xyRe_zero_eq (t : ℝ) : xyRe 0 t = 2*(Cc t)^2 := by
  have h := xyRe_neg_lam_eq 0 t
  rw [neg_zero] at h
  have hE : Ec 0 t = 0 := by simp [Ec]
  have hB : Bc 0 t = 0 := by simp [Bc]
  have hS : Sc 0 t = 0 := by simp [Sc]
  rw [hE, hB, hS] at h
  simpa using h

/-- The exact form of `Gfun 1 λ t`. -/
theorem Gfun_eq (lam t : ℝ) :
    Gfun 1 lam t = -(3/2)*(Cc t)^2 + 4*(Cc t)*(Ec lam t) + 2*(Ec lam t)^2
      - 2*(Bc lam t)^2 + Sc lam t := by
  rw [Gfun, xyRe_neg_lam_eq, xyRe_zero_eq]
  ring

/-- The exact form of `Hfun 1 λ t`. -/
theorem Hfun_eq (lam t : ℝ) :
    Hfun 1 lam t = -3*(Cc t)^2 + 2*(Cc t)*(Ec lam t) + (Ec lam t)^2
      - (Bc lam t)^2 + (1/2)*Sc lam t := by
  rw [Hfun, xyRe_neg_lam_eq, xyRe_zero_eq]
  ring

/-- The Taylor polynomial `12/35 - t²/14 + 9t⁴/2112` is nonnegative. -/
lemma ytay_nonneg (t : ℝ) : 0 ≤ 12/35 - t^2/14 + 9*t^4/2112 := by
  nlinarith [sq_nonneg (t^2 - 176/21), sq_nonneg t]

/-- Region `|t| ≤ 3`: the `S`-term is controlled by the Taylor polynomial. -/
lemma ytay_quad (t : ℝ) (h : t^2 ≤ 9) :
    -(3/2)*(2/3 - 3*t^2/80)^2 + (12/35 - t^2/14 + 9*t^4/2112) ≤ -1/10 := by
  nlinarith [h, sq_nonneg t, sq_nonneg (t^2 - 9), sq_nonneg (t^2 - 8),
    mul_nonneg (sub_nonneg.mpr h) (by positivity : (0:ℝ) ≤ t^2 + 9)]

lemma ytay_quad2 (t : ℝ) (h : t^2 ≤ 9) :
    -3*(2/3 - 3*t^2/80)^2 + (12/35 - t^2/14 + 9*t^4/2112) ≤ -1/4 := by
  nlinarith [h, sq_nonneg t, sq_nonneg (t^2 - 9), sq_nonneg (t^2 - 8),
    mul_nonneg (sub_nonneg.mpr h) (by positivity : (0:ℝ) ≤ t^2 + 9)]

/-- Region `|t| ≤ 3` for `Gfun`. -/
lemma Gfun_le_small (lam t : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 628/1000) (h : |t| ≤ 3) :
    Gfun 1 lam t ≤ 1/25 := by
  have hτ : t^2 ≤ 9 := by
    have := abs_le.mp h; nlinarith [this.2, neg_le.mp this.1]
  have hC1 : 2/3 - 3*t^2/80 ≤ Cc t := (SupCfun t).1
  have hC2 : |Cc t| ≤ 2/3 := (SupCfun t).2
  have hCn : 0 ≤ 2/3 - 3*t^2/80 := by nlinarith [hτ]
  have hE0 : E0c lam ≤ 3/200 := SupE0 h0 h1
  have hEabs : |Ec lam t| ≤ E0c lam := SupEcAbs lam t h0
  have hE3 : |Ec lam t| ≤ 3/200 := le_trans hEabs hE0
  have hEsc : Esc lam ≤ 3/500 := SupEs h0 h1
  have hYt : Yc t ≤ 12/35 - t^2/14 + 9*t^4/2112 := SupYcTaylor t h
  have hYnn := ytay_nonneg t
  have hYmax : max (Yc t) 0 ≤ 12/35 - t^2/14 + 9*t^4/2112 := max_le hYt hYnn
  have hS : Sc lam t ≤ max (Yc t) 0 + Esc lam := by
    have hSc := SupScLe lam t h0
    have hlam1 : lam ≤ 1 := by linarith
    have hmax0 : 0 ≤ max (Yc t) 0 := le_max_right _ _
    nlinarith
  have hCsq : (2/3 - 3*t^2/80)^2 ≤ (Cc t)^2 := by
    nlinarith [hC1, hCn, sq_nonneg (Cc t + (2/3 - 3*t^2/80))]
  have hCE : Cc t * Ec lam t ≤ (2/3)*(3/200) := by
    nlinarith [hC2, hE3, abs_nonneg (Cc t), abs_nonneg (Ec lam t),
      le_abs_self (Cc t * Ec lam t), abs_mul (Cc t) (Ec lam t)]
  have hq := ytay_quad t hτ
  have h1' : -(3/2)*(Cc t)^2 ≤ -(3/2)*(2/3 - 3*t^2/80)^2 := by linarith
  have h2' : 4*(Cc t)*(Ec lam t) ≤ 4*((2/3)*(3/200)) := by linarith
  have h3' : 2*(Ec lam t)^2 ≤ 2*(3/200)^2 := by nlinarith [hE3, abs_nonneg (Ec lam t), sq_abs (Ec lam t)]
  have h4' : Sc lam t ≤ (12/35 - t^2/14 + 9*t^4/2112) + 3/500 := by linarith
  rw [Gfun_eq]
  linarith [h1', h2', h3', h4', hq, sq_nonneg (Bc lam t)]

/-- Region `|t| ≥ 3` for `Gfun`. -/
lemma Gfun_le_large (lam t : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 628/1000) (h : 3 ≤ |t|) :
    Gfun 1 lam t ≤ 1/25 := by
  have hE0 : E0c lam ≤ 3/200 := SupE0 h0 h1
  have hEabs : |Ec lam t| ≤ E0c lam := SupEcAbs lam t h0
  have hE3 : |Ec lam t| ≤ 3/200 := le_trans hEabs hE0
  have hEsc : Esc lam ≤ 3/500 := SupEs h0 h1
  have hYt : Yc t ≤ 0 := SupYcNonpos t h
  have hYmax : max (Yc t) 0 ≤ 0 := max_le hYt le_rfl
  have hS : Sc lam t ≤ 3/500 := by
    have hSc := SupScLe lam t h0
    have hlam1 : lam ≤ 1 := by linarith
    nlinarith
  have hE2 : (Ec lam t)^2 ≤ (3/200)^2 := by nlinarith [hE3, abs_nonneg (Ec lam t), sq_abs (Ec lam t)]
  have hCE : Cc t * Ec lam t ≤ (1/2)*(3/200)^2 + (1/2)*(Cc t)^2 := by
    nlinarith [sq_nonneg (Cc t - Ec lam t), hE2]
  rw [Gfun_eq]
  nlinarith [hE2, hEsc, hS, sq_nonneg (Bc lam t), sq_nonneg (Cc t + (4/3)*Ec lam t)]

/-- Region `|t| ≤ 3` for `Hfun`. -/
lemma Hfun_le_small (lam t : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 628/1000) (h : |t| ≤ 3) :
    Hfun 1 lam t ≤ 1/25 := by
  have hτ : t^2 ≤ 9 := by
    have := abs_le.mp h; nlinarith [this.2, neg_le.mp this.1]
  have hC1 : 2/3 - 3*t^2/80 ≤ Cc t := (SupCfun t).1
  have hC2 : |Cc t| ≤ 2/3 := (SupCfun t).2
  have hCn : 0 ≤ 2/3 - 3*t^2/80 := by nlinarith [hτ]
  have hE0 : E0c lam ≤ 3/200 := SupE0 h0 h1
  have hEabs : |Ec lam t| ≤ E0c lam := SupEcAbs lam t h0
  have hE3 : |Ec lam t| ≤ 3/200 := le_trans hEabs hE0
  have hEsc : Esc lam ≤ 3/500 := SupEs h0 h1
  have hYt : Yc t ≤ 12/35 - t^2/14 + 9*t^4/2112 := SupYcTaylor t h
  have hYnn := ytay_nonneg t
  have hYmax : max (Yc t) 0 ≤ 12/35 - t^2/14 + 9*t^4/2112 := max_le hYt hYnn
  have hS : Sc lam t ≤ max (Yc t) 0 + Esc lam := by
    have hSc := SupScLe lam t h0
    have hlam1 : lam ≤ 1 := by linarith
    have hmax0 : 0 ≤ max (Yc t) 0 := le_max_right _ _
    nlinarith
  have hCsq : (2/3 - 3*t^2/80)^2 ≤ (Cc t)^2 := by
    nlinarith [hC1, hCn, sq_nonneg (Cc t + (2/3 - 3*t^2/80))]
  have hCE : Cc t * Ec lam t ≤ (2/3)*(3/200) := by
    nlinarith [hC2, hE3, abs_nonneg (Cc t), abs_nonneg (Ec lam t),
      le_abs_self (Cc t * Ec lam t), abs_mul (Cc t) (Ec lam t)]
  have hq := ytay_quad2 t hτ
  have h1' : -3*(Cc t)^2 ≤ -3*(2/3 - 3*t^2/80)^2 := by linarith
  have h2' : 2*(Cc t)*(Ec lam t) ≤ 2*((2/3)*(3/200)) := by linarith
  have h3' : (Ec lam t)^2 ≤ (3/200)^2 := by nlinarith [hE3, abs_nonneg (Ec lam t), sq_abs (Ec lam t)]
  have h4' : (1/2)*Sc lam t ≤ (1/2)*((12/35 - t^2/14 + 9*t^4/2112) + 3/500) := by linarith
  rw [Hfun_eq]
  linarith [h1', h2', h3', h4', hq, sq_nonneg (Bc lam t)]

/-- Region `|t| ≥ 3` for `Hfun`. -/
lemma Hfun_le_large (lam t : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 628/1000) (h : 3 ≤ |t|) :
    Hfun 1 lam t ≤ 1/25 := by
  have hE0 : E0c lam ≤ 3/200 := SupE0 h0 h1
  have hEabs : |Ec lam t| ≤ E0c lam := SupEcAbs lam t h0
  have hE3 : |Ec lam t| ≤ 3/200 := le_trans hEabs hE0
  have hEsc : Esc lam ≤ 3/500 := SupEs h0 h1
  have hYt : Yc t ≤ 0 := SupYcNonpos t h
  have hYmax : max (Yc t) 0 ≤ 0 := max_le hYt le_rfl
  have hS : Sc lam t ≤ 3/500 := by
    have hSc := SupScLe lam t h0
    have hlam1 : lam ≤ 1 := by linarith
    nlinarith
  have hE2 : (Ec lam t)^2 ≤ (3/200)^2 := by nlinarith [hE3, abs_nonneg (Ec lam t), sq_abs (Ec lam t)]
  have hCE : Cc t * Ec lam t ≤ (3/200)^2/2 + (Cc t)^2/2 := by
    nlinarith [sq_nonneg (Cc t - Ec lam t), hE2]
  rw [Hfun_eq]
  nlinarith [hE2, hEsc, hS, sq_nonneg (Bc lam t), sq_nonneg (Cc t + Ec lam t)]

theorem LamPrimeSup :
    (∀ lam : ℝ, 0 ≤ lam → lam ≤ 628/1000 → ∀ t : ℝ, Gfun 1 lam t ≤ 1/25) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam ≤ 628/1000 → ∀ t : ℝ, Hfun 1 lam t ≤ 1/25) := by
  constructor
  · intro lam h0 h1 t
    rcases le_total |t| 3 with h | h
    · exact Gfun_le_small lam t h0 h1 h
    · exact Gfun_le_large lam t h0 h1 h
  · intro lam h0 h1 t
    rcases le_total |t| 3 with h | h
    · exact Hfun_le_small lam t h0 h1 h
    · exact Hfun_le_large lam t h0 h1 h

end Work.ZeroFreeTables.XY
