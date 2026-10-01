import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_poly_bounds_on_unit
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg

namespace Commons.Analysis.Real

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 4000000

/-! ## Derivative helpers -/

private lemma hd_sub (c β : ℝ) : HasDerivAt (fun x : ℝ => x - c) 1 β :=
  (hasDerivAt_id β).sub_const c

private lemma hd_csub (c β : ℝ) : HasDerivAt (fun x : ℝ => c - x) (-1) β :=
  HasDerivAt.const_sub c (hasDerivAt_id β)

private lemma hd_twom (β : ℝ) : HasDerivAt (fun x : ℝ => 2-x) (-1) β := hd_csub 2 β
private lemma hd_onem (β : ℝ) : HasDerivAt (fun x : ℝ => 1-x) (-1) β := hd_csub 1 β

private lemma hd_sq (β : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*β) β := by
  have h := (hasDerivAt_id β).pow 2
  refine h.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq]
  ring

private lemma hd_sq_sub (a β : ℝ) : HasDerivAt (fun x : ℝ => (a-x)^2) (-2*(a-β)) β := by
  have h := (HasDerivAt.const_sub a (hasDerivAt_id β)).pow 2
  refine h.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq]
  ring

private lemma hd_mono (n : ℕ) (c β : ℝ) :
    HasDerivAt (fun x : ℝ => c * x^n) (c * (n:ℝ) * β^(n-1)) β := by
  have h := ((hasDerivAt_id β).pow n).const_mul c
  refine h.congr_deriv ?_
  simp only [id_eq, mul_one]
  ring

private lemma hd_div_const {c : ℝ} {q : ℝ → ℝ} {q' x : ℝ} (hq : HasDerivAt q q' x) (h : q x ≠ 0) :
    HasDerivAt (fun y : ℝ => c/(q y)) (-(c*q')/(q x)^2) x := by
  have h2 := (hasDerivAt_const x c).div hq h
  refine h2.congr_deriv ?_
  ring

private lemma hd_arctan_csub {a k : ℝ} {β : ℝ} (h : a - β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.arctan (k/(a-x))) (k/((a-β)^2+k^2)) β := by
  have hlin : HasDerivAt (fun x : ℝ => a - x) (-1) β := hd_csub a β
  have hd : HasDerivAt (fun x : ℝ => k/(a-x)) (k/(a-β)^2) β := by
    have h2 := (hasDerivAt_const β k).div hlin (by simpa using h)
    refine h2.congr_deriv ?_
    ring
  have h3 := (Real.hasDerivAt_arctan (k/(a-β))).comp β hd
  refine h3.congr_deriv ?_
  field_simp
  try ring

private lemma hd_arctan_add {a k : ℝ} {β : ℝ} (h : a + β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.arctan (k/(a+x))) (-k/((a+β)^2+k^2)) β := by
  have hlin : HasDerivAt (fun x : ℝ => a + x) 1 β := (hasDerivAt_id β).const_add a
  have hd : HasDerivAt (fun x : ℝ => k/(a+x)) (-(k/(a+β)^2)) β := by
    have h2 := (hasDerivAt_const β k).div hlin (by simpa using h)
    refine h2.congr_deriv ?_
    ring
  have h3 := (Real.hasDerivAt_arctan (k/(a+β))).comp β hd
  refine h3.congr_deriv ?_
  field_simp
  try ring

private lemma hd_inv2sub_1 (β : ℝ) (h : (2:ℝ) - β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/(2-x)) (1/(2-β)^2) β := by
  have h2 := hd_div_const (c := (1:ℝ)) (hd_csub (2:ℝ) β) h
  refine h2.congr_deriv ?_
  rw [show -(1 * (-1)) / (((2:ℝ))-β)^2 = 1/(2-β)^2 by ring]

private lemma hd_inv_self (β : ℝ) (h : β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/x) (-1/β^2) β := by
  have h2 := hd_div_const (c := (1:ℝ)) (hasDerivAt_id β) h
  refine h2.congr_deriv ?_
  rw [show -(1 * 1) / (id β)^2 = -1/β^2 by simp only [id_eq]; ring]

/-! ## arctan atoms -/

private def at1 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/6)/(3/2-β))
private def dat1 (β : ℝ) : ℝ := ((1:ℝ)/6)/((3/2-β)^2+((1:ℝ)/6)^2)
private def d2at1 (β : ℝ) : ℝ := 2*((1:ℝ)/6)*(3/2-β)/(((3/2-β)^2+((1:ℝ)/6)^2)^2)

private def at2 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/6)/(1+β))
private def dat2 (β : ℝ) : ℝ := -((1:ℝ)/6)/((1+β)^2+((1:ℝ)/6)^2)
private def d2at2 (β : ℝ) : ℝ := 2*((1:ℝ)/6)*(1+β)/(((1+β)^2+((1:ℝ)/6)^2)^2)

private def at3 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/6)/(2-β))
private def dat3 (β : ℝ) : ℝ := ((1:ℝ)/6)/((2-β)^2+((1:ℝ)/6)^2)
private def d2at3 (β : ℝ) : ℝ := 2*((1:ℝ)/6)*(2-β)/(((2-β)^2+((1:ℝ)/6)^2)^2)

private def fA (β : ℝ) : ℝ := 2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5)
private def dfA (β : ℝ) : ℝ := -(2*β^4-18*β^3+81*β^2-136*β+75)/(2*(2-β)^6)
private def d2fA (β : ℝ) : ℝ := -(2*β^4-19*β^3+108*β^2-178*β+89)/(2-β)^7

private def fQ1 (β : ℝ) : ℝ := (1-β)^2*((1:ℝ)/6)/((2-β)^2*((2-β)^2+((1:ℝ)/6)^2))
      + (1-β)^3*((1:ℝ)/6)*(5*(2-β)^2+3*((1:ℝ)/6)^2)/(2*(2-β)^4*((2-β)^2+((1:ℝ)/6)^2)^2)
private def dfQ1 (β : ℝ) : ℝ :=
  (3*(β-1)) * (5184*β^7 - 81648*β^6 + 486144*β^5 - 1452888*β^4 + 2336400*β^3 - 1929959*β^2 + 637901*β + 4342)
    / ((2-β)^5 * 46656 * ((2-β)^2+((1:ℝ)/6)^2)^3)
private def d2fQ1 (β : ℝ) : ℝ := (1679616*β^10 - 35271936*β^9 + 296203392*β^8 - 1335349152*β^7 + 3549004848*β^6 - 5556474720*β^5 + 4415502240*β^4 - 83777970*β^3 - 2970540810*β^2 + 2291526972*β - 571894644)/((2-β)^6 * 1679616 * ((2-β)^2+((1:ℝ)/6)^2)^4)

private lemma hasDerivAt_at1 {β : ℝ} (h : β ≠ 3/2) : HasDerivAt at1 (dat1 β) β :=
  hd_arctan_csub (a := (3:ℝ)/2) (k := (1:ℝ)/6) (β := β) (by
    intro hc; exact h (by linarith [hc]))

private lemma hasDerivAt_at2 {β : ℝ} (h : β ≠ -1) : HasDerivAt at2 (dat2 β) β := by
  have hh := hd_arctan_add (a := (1:ℝ)) (k := (1:ℝ)/6) (β := β) (by
    intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat2]; try ring

private lemma hasDerivAt_at3 {β : ℝ} (h : β ≠ 2) : HasDerivAt at3 (dat3 β) β :=
  hd_arctan_csub (a := (2:ℝ)) (k := (1:ℝ)/6) (β := β) (by
    intro hc; exact h (by linarith [hc]))

private lemma hasDerivAt_dat1 (β : ℝ) : HasDerivAt dat1 (d2at1 β) β := by
  unfold dat1
  have hq : HasDerivAt (fun x : ℝ => ((3/2:ℝ)-x)^2+((1:ℝ)/6)^2) (-2*((3/2:ℝ)-β)) β := by
    have h2 := ((hd_csub (3/2) β).pow 2).add_const (((1:ℝ)/6)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((3/2:ℝ)-β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((1:ℝ)/6)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at1]
  field_simp
  try ring

private lemma hasDerivAt_dat2 (β : ℝ) : HasDerivAt dat2 (d2at2 β) β := by
  unfold dat2
  have hq : HasDerivAt (fun x : ℝ => ((1:ℝ)+x)^2+((1:ℝ)/6)^2) (2*((1:ℝ)+β)) β := by
    have h2 := (((hasDerivAt_id β).const_add (1:ℝ)).pow 2).add_const (((1:ℝ)/6)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]
    ring
  have hq0 : ((1:ℝ)+β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := (-((1:ℝ)/6))) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at2]
  field_simp
  try ring

private lemma hasDerivAt_dat3 (β : ℝ) : HasDerivAt dat3 (d2at3 β) β := by
  unfold dat3
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^2+((1:ℝ)/6)^2) (-2*((2:ℝ)-β)) β := by
    have h2 := ((hd_csub (2) β).pow 2).add_const (((1:ℝ)/6)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((2:ℝ)-β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((1:ℝ)/6)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at3]
  field_simp
  try ring

/-! ## prefactors -/

private lemma hasDerivAt_fA {β : ℝ} (h : β ≠ 2) : HasDerivAt fA (dfA β) β := by
  unfold fA
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have ht1 := ((hasDerivAt_const β (2:ℝ)).mul (hd_onem β)).div (hd_twom β) hne
  have ht2 := ((hd_onem β).pow 2).div ((hd_twom β).pow 3) (pow_ne_zero 3 hne)
  have ht3 := ((hasDerivAt_const β (3:ℝ)).mul ((hd_onem β).pow 3)).div
      ((hasDerivAt_const β (2:ℝ)).mul ((hd_twom β).pow 5)) (by
        exact mul_ne_zero (by norm_num) (pow_ne_zero 5 hne))
  have hsum := (ht1.add ht2).add ht3
  refine hsum.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfA]
  field_simp [hne] <;> ring

private lemma hasDerivAt_dfA {β : ℝ} (h : β ≠ 2) : HasDerivAt dfA (d2fA β) β := by
  unfold dfA
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hp : HasDerivAt (fun x : ℝ => 2*x^4-18*x^3+81*x^2-136*x+75)
      (8*β^3-54*β^2+162*β-136) β := by
    have h4 := hd_mono 4 (2:ℝ) β
    have h3 := hd_mono 3 (18:ℝ) β
    have h2 := hd_mono 2 (81:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 136*x) (136:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (136:ℝ)
    have h0 := hasDerivAt_const β (75:ℝ)
    have hs := ((((h4.sub h3).add h2).sub h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := hp.neg
  have hq := ((hd_twom β).pow 6).const_mul (2:ℝ)
  have hd := hn.div hq (by exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hne))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fA]
  field_simp [hne] <;> ring

private lemma hasDerivAt_fQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt fQ1 (dfQ1 β) β := by
  unfold fQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have h36 : (36:ℝ)*β^2-144*β+145 ≠ 0 := by nlinarith [sq_nonneg (6*β-12)]
  have ht1 := (((hd_onem β).pow 2).mul_const ((1:ℝ)/6)).div
      (((hd_twom β).pow 2).mul (((hd_twom β).pow 2).add_const (((1:ℝ)/6)^2 : ℝ)))
      (by
        apply mul_ne_zero (pow_ne_zero 2 hne)
        exact hq1d)
  have ht2 := ((((hd_onem β).pow 3).mul_const ((1:ℝ)/6)).mul
        ((((hd_twom β).pow 2).const_mul (5:ℝ)).add_const (3*((1:ℝ)/6)^2 : ℝ))).div
      ((((hd_twom β).pow 4).const_mul (2:ℝ)).mul ((((hd_twom β).pow 2).add_const (((1:ℝ)/6)^2 : ℝ)).pow 2))
      (by
        apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hne))
        exact pow_ne_zero 2 hq1d)
  have hsum := ht1.add ht2
  refine hsum.congr_deriv ?_
  rw [dfQ1]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d, h36]
  ring

private lemma hasDerivAt_dfQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt dfQ1 (d2fQ1 β) β := by
  unfold dfQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have h36 : (36:ℝ)*β^2-144*β+145 ≠ 0 := by nlinarith [sq_nonneg (6*β-12)]
  have hA : HasDerivAt (fun x : ℝ => 5184*x^7 - 81648*x^6 + 486144*x^5 - 1452888*x^4 + 2336400*x^3 - 1929959*x^2 + 637901*x + 4342)
      (36288*β^6 - 489888*β^5 + 2430720*β^4 - 5811552*β^3 + 7009200*β^2 - 3859918*β + 637901) β := by
    have h7 := hd_mono 7 (5184:ℝ) β
    have h6 := hd_mono 6 (81648:ℝ) β
    have h5 := hd_mono 5 (486144:ℝ) β
    have h4 := hd_mono 4 (1452888:ℝ) β
    have h3 := hd_mono 3 (2336400:ℝ) β
    have h2 := hd_mono 2 (1929959:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 637901*x) (637901:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (637901:ℝ)
    have h0 := hasDerivAt_const β (4342:ℝ)
    have hs := (((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := ((hd_sub 1 β).const_mul (3:ℝ)).mul hA
  have hq := ((((hd_twom β).pow 5).mul_const (46656:ℝ))).mul ((((hd_twom β).pow 2).add_const (((1:ℝ)/6)^2 : ℝ)).pow 3)
  have hd := hn.div hq (by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hne) (by norm_num))
    exact pow_ne_zero 3 hq1d)
  refine hd.congr_deriv ?_
  rw [d2fQ1]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d, h36]
  ring_nf

/-! ## log atoms -/

private lemma hd_log_2sub (β : ℝ) (h : (2:ℝ) - β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (2*(2-x))) (-(1/(2-β))) β := by
  have harg : HasDerivAt (fun x:ℝ => 2*(2-x)) (-2) β := by
    simpa using (hd_twom β).const_mul (2:ℝ)
  have hpos : (2:ℝ)*(2-β) ≠ 0 := mul_ne_zero (by norm_num) h
  have hlog := (Real.hasDerivAt_log hpos).comp β harg
  refine hlog.congr_deriv ?_
  field_simp <;> ring

private lemma hd_log_2b (β : ℝ) (h : β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (2*x)) (1/β) β := by
  have harg : HasDerivAt (fun x:ℝ => 2*x) 2 β := by simpa using (hasDerivAt_id β).const_mul (2:ℝ)
  have hpos : (2:ℝ)*β ≠ 0 := mul_ne_zero (by norm_num) h
  have hlog := (Real.hasDerivAt_log hpos).comp β harg
  refine hlog.congr_deriv ?_
  field_simp <;> ring

private lemma hd_inv2sub (β : ℝ) (h : (2:ℝ) - β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/(2-x)^2) (2/(2-β)^3) β := by
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^2) (2*((2:ℝ)-β)*(-1)) β := by
    have h2 := (hd_csub (2:ℝ) β).pow 2
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

private lemma hd_inv2sub3 (β : ℝ) (h : (2:ℝ) - β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/(2-x)^3) (3/(2-β)^4) β := by
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^3) (3*((2:ℝ)-β)^2*(-1)) β := by
    have h2 := (hd_csub (2:ℝ) β).pow 3
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

private lemma hd_invbetasq (β : ℝ) (h : β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/x^2) (-2/β^3) β := by
  have hq : HasDerivAt (fun x : ℝ => x^2) (2*β) β := hd_sq β
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

private lemma hd_invbetacu (β : ℝ) (h : β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/x^3) (-3/β^4) β := by
  have hq : HasDerivAt (fun x : ℝ => x^3) (3*β^2) β := by
    have h2 := (hasDerivAt_id β).pow 3
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]
    ring
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

/-! ## log / power atoms -/

private def Kc : ℝ := ((1:ℝ)/6)*(-Real.log ((1:ℝ)/6) + 1)
private def C3 : ℝ := ((1:ℝ)/6)^3/12

private def lg1 (β : ℝ) : ℝ := Real.log (2*(2-β))
private def dlg1 (β : ℝ) : ℝ := -(1/(2-β))
private def d2lg1 (β : ℝ) : ℝ := -(1/(2-β)^2)
private def lg2 (β : ℝ) : ℝ := Real.log (2*β)
private def dlg2 (β : ℝ) : ℝ := 1/β
private def d2lg2 (β : ℝ) : ℝ := -1/β^2

private def n1 (β : ℝ) : ℝ := 1/(2-β)
private def n2 (β : ℝ) : ℝ := 1/(2-β)^2
private def n3 (β : ℝ) : ℝ := 1/(2-β)^3
private def n4 (β : ℝ) : ℝ := 1/(2-β)^4
private def m1 (β : ℝ) : ℝ := 1/β
private def m2 (β : ℝ) : ℝ := 1/β^2
private def m3 (β : ℝ) : ℝ := 1/β^3
private def m4 (β : ℝ) : ℝ := 1/β^4

private lemma hasDerivAt_lg1 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt lg1 (dlg1 β) β :=
  hd_log_2sub β h

private lemma hasDerivAt_dlg1 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt dlg1 (d2lg1 β) β :=
  (hd_inv2sub_1 β h).neg

private lemma hasDerivAt_lg2 {β : ℝ} (h : β ≠ 0) : HasDerivAt lg2 (dlg2 β) β :=
  hd_log_2b β h

private lemma hasDerivAt_dlg2 {β : ℝ} (h : β ≠ 0) : HasDerivAt dlg2 (d2lg2 β) β :=
  hd_inv_self β h

private lemma hasDerivAt_n1 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt n1 (n2 β) β :=
  hd_inv2sub_1 β h

private lemma hasDerivAt_n2 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt n2 (2*(n3 β)) β := by
  have h0 := hd_inv2sub β h
  refine h0.congr_deriv ?_
  simp only [n3]; ring_nf

private lemma hasDerivAt_n3 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt n3 (3*(n4 β)) β := by
  have h0 := hd_inv2sub3 β h
  refine h0.congr_deriv ?_
  simp only [n4]; ring_nf

private lemma hasDerivAt_m2 {β : ℝ} (h : β ≠ 0) : HasDerivAt m2 (-2*(m3 β)) β := by
  have h0 := hd_invbetasq β h
  refine h0.congr_deriv ?_
  simp only [m3]; ring_nf

private lemma hasDerivAt_m3 {β : ℝ} (h : β ≠ 0) : HasDerivAt m3 (-3*(m4 β)) β := by
  have h0 := hd_invbetacu β h
  refine h0.congr_deriv ?_
  simp only [m4]; ring_nf

private def T5 (β : ℝ) : ℝ := ((1:ℝ)/6)*(lg1 β) + Kc + C3*(n2 β)
private def dT5 (β : ℝ) : ℝ := ((1:ℝ)/6)*(dlg1 β) + C3*(2*(n3 β))
private def d2T5 (β : ℝ) : ℝ := ((1:ℝ)/6)*(d2lg1 β) + C3*(2*(3*(n4 β)))
private def T6 (β : ℝ) : ℝ := ((1:ℝ)/6)*(lg2 β) + Kc + C3*(m2 β)
private def dT6 (β : ℝ) : ℝ := ((1:ℝ)/6)*(dlg2 β) + C3*(-2*(m3 β))
private def d2T6 (β : ℝ) : ℝ := ((1:ℝ)/6)*(d2lg2 β) + C3*(-2*(-3*(m4 β)))

private lemma hasDerivAt_T5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt T5 (dT5 β) β := by
  have h1 := (hasDerivAt_lg1 h).const_mul (((1:ℝ)/6))
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_n2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT5] <;> ring

private lemma hasDerivAt_dT5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt dT5 (d2T5 β) β := by
  rw [show dT5 = (fun x : ℝ => ((1:ℝ)/6)*(dlg1 x) + C3*(2*(n3 x))) from rfl]
  have h1 := (hasDerivAt_dlg1 h).const_mul (((1:ℝ)/6))
  have h2 := ((hasDerivAt_n3 h).const_mul (2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T5] <;> ring

private lemma hasDerivAt_T6 {β : ℝ} (h : β ≠ 0) : HasDerivAt T6 (dT6 β) β := by
  have h1 := (hasDerivAt_lg2 h).const_mul (((1:ℝ)/6))
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_m2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT6] <;> ring

private lemma hasDerivAt_dT6 {β : ℝ} (h : β ≠ 0) : HasDerivAt dT6 (d2T6 β) β := by
  rw [show dT6 = (fun x : ℝ => ((1:ℝ)/6)*(dlg2 x) + C3*(-2*(m3 x))) from rfl]
  have h1 := (hasDerivAt_dlg2 h).const_mul (((1:ℝ)/6))
  have h2 := ((hasDerivAt_m3 h).const_mul (-2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T6] <;> ring

/-! ## the function, its two derivatives -/

private def Ef (β : ℝ) : ℝ := ((13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)) - (T5 β + T6 β)

private def Df (β : ℝ) : ℝ :=
  ((13/5)*(dat1 β + dat2 β) + ((dfA β * at3 β + fA β * dat3 β) + dfQ1 β)) - (dT5 β + dT6 β)

private def E2f (β : ℝ) : ℝ :=
  ((13/5)*(d2at1 β + d2at2 β)
    + (((d2fA β * at3 β + 2*(dfA β * dat3 β)) + fA β * d2at3 β) + d2fQ1 β))
  - (d2T5 β + d2T6 β)

private lemma hasDerivAt_Ef {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1) (h2 : β ≠ 2) (h0 : β ≠ 0) :
    HasDerivAt Ef (Df β) β := by
  have hE : Ef = fun x : ℝ => ((13/5)*(at1 x + at2 x) + (fA x * at3 x + fQ1 x)) - (T5 x + T6 x) :=
    funext (fun x => rfl)
  rw [hE]
  have h1 := ((hasDerivAt_at1 h32).add (hasDerivAt_at2 hm1)).const_mul (13/5)
  have h2' := ((hasDerivAt_fA h2).mul (hasDerivAt_at3 h2)).add (hasDerivAt_fQ1 h2)
  have h3' := (hasDerivAt_T5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_T6 h0)
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [Df] <;> ring

private lemma hasDerivAt_Df {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1) (h2 : β ≠ 2) (h0 : β ≠ 0) :
    HasDerivAt Df (E2f β) β := by
  have hD : Df = fun x : ℝ =>
      ((13/5)*(dat1 x + dat2 x) + ((dfA x * at3 x + fA x * dat3 x) + dfQ1 x)) - (dT5 x + dT6 x) :=
    funext (fun x => rfl)
  rw [hD]
  have h1 := ((hasDerivAt_dat1 β).add (hasDerivAt_dat2 β)).const_mul (13/5)
  have h2' := (((hasDerivAt_dfA h2).mul (hasDerivAt_at3 h2)).add
      ((hasDerivAt_fA h2).mul (hasDerivAt_dat3 β))).add (hasDerivAt_dfQ1 h2)
  have h3' := ((hasDerivAt_dT5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_dT6 h0))
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [E2f] <;> ring


private def P1f (β : ℝ) : ℝ := (13/5)*(d2at1 β + d2at2 β)
private def ARred (β : ℝ) : ℝ := 2*dfA β * dat3 β + fA β * d2at3 β + d2fQ1 β + d2fA β * ((1:ℝ)/6/(2-β))
private def LGf (β : ℝ) : ℝ := -(d2T5 β + d2T6 β)

private lemma P1f_lower {β : ℝ} (h1 : (1:ℝ)/6 ≤ β) (h2 : β ≤ 1) : (23:ℝ)/50 ≤ P1f β := by
  have hq1 : ((3/2:ℝ)-β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have hq2 : ((1:ℝ)+β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < 419904 * (((3/2:ℝ)-β)^2+((1:ℝ)/6)^2)^2 * (((1:ℝ)+β)^2+((1:ℝ)/6)^2)^2 := by positivity
  have hkey : (50*(P1f β) - 23) * (419904 * (((3/2:ℝ)-β)^2+((1:ℝ)/6)^2)^2 * (((1:ℝ)+β)^2+((1:ℝ)/6)^2)^2)
      = 70306453 + -127856628*β + 189358704*β^2 + 258309000*β^3 + -223366572*β^4 + -80481600*β^5 + 42386976*β^6 + 19315584*β^7 + -9657792*β^8 := by
    unfold P1f d2at1 d2at2
    field_simp [hq1, hq2]
    ring
  have hnum : (0:ℝ) ≤ 70306453 + -127856628*β + 189358704*β^2 + 258309000*β^3 + -223366572*β^4 + -80481600*β^5 + 42386976*β^6 + 19315584*β^7 + -9657792*β^8 := by
    rw [show 70306453 + -127856628*β + 189358704*β^2 + 258309000*β^3 + -223366572*β^4 + -80481600*β^5 + 42386976*β^6 + 19315584*β^7 + -9657792*β^8 = (742674127104/3125)*(1-β)^8 + (5408138451456/3125)*(β-1/6)*(1-β)^7 + (3931413345792/625)*(β-1/6)^2*(1-β)^6 + (46672116288768/3125)*(β-1/6)^3*(1-β)^5 + (14810313471552/625)*(β-1/6)^4*(1-β)^4 + (74772958650624/3125)*(β-1/6)^5*(1-β)^3 + (44909011616256/3125)*(β-1/6)^6*(1-β)^2 + (2879160795648/625)*(β-1/6)^7*(1-β) + (1858516939008/3125)*(β-1/6)^8 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (50*(P1f β) - 23) * (419904 * (((3/2:ℝ)-β)^2+((1:ℝ)/6)^2)^2 * (((1:ℝ)+β)^2+((1:ℝ)/6)^2)^2) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma ARred_lower {β : ℝ} (h1 : (1:ℝ)/6 ≤ β) (h2 : β ≤ 1) : -(7:ℝ)/10 ≤ ARred β := by
  have hne : (2:ℝ)-β ≠ 0 := by linarith
  have hB : ((2:ℝ)-β)^2+((1:ℝ)/6)^2 ≠ 0 := by positivity
  have h2p : (0:ℝ) < 2-β := by linarith
  have hden : (0:ℝ) < 100776960 * (2-β)^8 * ((2-β)^2+((1:ℝ)/6)^2)^4 := by positivity
  have hkey : (ARred β + 7/10) * (100776960 * (2-β)^8 * ((2-β)^2+((1:ℝ)/6)^2)^4)
      = 4219977849190 + -35232511775660*β + 136319044764480*β^2 + -324855980111570*β^3 + 534521249508172*β^4 + -645073288794600*β^5 + 591741907489104*β^6 + -421634300028288*β^7 + 236202859048938*β^8 + -104509650218112*β^9 + 36430638699168*β^10 + -9904138292736*β^11 + 2058837787584*β^12 + -316323201024*β^13 + 33868896768*β^14 + -2257403904*β^15 + 70543872*β^16 := by
    unfold ARred dfA dat3 fA d2at3 d2fQ1 d2fA
    field_simp [hne, hB]
    ring
  have hnum : (0:ℝ) ≤ 4219977849190 + -35232511775660*β + 136319044764480*β^2 + -324855980111570*β^3 + 534521249508172*β^4 + -645073288794600*β^5 + 591741907489104*β^6 + -421634300028288*β^7 + 236202859048938*β^8 + -104509650218112*β^9 + 36430638699168*β^10 + -9904138292736*β^11 + 2058837787584*β^12 + -316323201024*β^13 + 33868896768*β^14 + -2257403904*β^15 + 70543872*β^16 := by
    rw [show 4219977849190 + -35232511775660*β + 136319044764480*β^2 + -324855980111570*β^3 + 534521249508172*β^4 + -645073288794600*β^5 + 591741907489104*β^6 + -421634300028288*β^7 + 236202859048938*β^8 + -104509650218112*β^9 + 36430638699168*β^10 + -9904138292736*β^11 + 2058837787584*β^12 + -316323201024*β^13 + 33868896768*β^14 + -2257403904*β^15 + 70543872*β^16 = (2740312843086385699725312/152587890625)*(1-β)^16 + (22557914210091650496233472/152587890625)*(β-1/6)*(1-β)^15 + (17168774225161793519812608/30517578125)*(β-1/6)^2*(1-β)^14 + (40007534974071047022034944/30517578125)*(β-1/6)^3*(1-β)^13 + (63759266475503445735395328/30517578125)*(β-1/6)^4*(1-β)^12 + (367750618217210453859311616/152587890625)*(β-1/6)^5*(1-β)^11 + (317301593565386799504654336/152587890625)*(β-1/6)^6*(1-β)^10 + (41810793564520497071517696/30517578125)*(β-1/6)^7*(1-β)^9 + (21358409446409103879602688/30517578125)*(β-1/6)^8*(1-β)^8 + (8586411694856457196363776/30517578125)*(β-1/6)^9*(1-β)^7 + (13826823088277377585668096/152587890625)*(β-1/6)^10*(1-β)^6 + (3629686739803538205229056/152587890625)*(β-1/6)^11*(1-β)^5 + (155171444916751452684288/30517578125)*(β-1/6)^12*(1-β)^4 + (25743398539169783660544/30517578125)*(β-1/6)^13*(1-β)^3 + (2940446464270775451648/30517578125)*(β-1/6)^14*(1-β)^2 + (905030227200058785792/152587890625)*(β-1/6)^15*(1-β) + (13432381933382664192/152587890625)*(β-1/6)^16 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (ARred β + 7/10) * (100776960 * (2-β)^8 * ((2-β)^2+((1:ℝ)/6)^2)^4) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma LGf_lower {β : ℝ} (h1 : (1:ℝ)/6 ≤ β) (h2 : β ≤ 1) : (3:ℝ)/10 ≤ LGf β := by
  have hb : β ≠ 0 := by linarith
  have hne : (2:ℝ)-β ≠ 0 := by linarith
  have hbp : (0:ℝ) < β := by linarith
  have h2p : (0:ℝ) < 2-β := by linarith
  have hden : (0:ℝ) < 1080*β^4*(2-β)^4 := by positivity
  have hkey : (LGf β - 3/10) * (1080*β^4*(2-β)^4)
      = -40 + 80*β + 2820*β^2 + -5740*β^3 + -149*β^4 + 8208*β^5 + -7416*β^6 + 2592*β^7 + -324*β^8 := by
    unfold LGf d2T5 d2T6 C3 d2lg1 d2lg2 n4 m4
    field_simp [hb, hne]
    ring
  have hnum : (0:ℝ) ≤ -40 + 80*β + 2820*β^2 + -5740*β^3 + -149*β^4 + 8208*β^5 + -7416*β^6 + 2592*β^7 + -324*β^8 := by
    rw [show -40 + 80*β + 2820*β^2 + -5740*β^3 + -149*β^4 + 8208*β^5 + -7416*β^6 + 2592*β^7 + -324*β^8 = (43473996/390625)*(1-β)^8 + (1138935168/390625)*(β-1/6)*(1-β)^7 + (7019042688/390625)*(β-1/6)^2*(1-β)^6 + (16569821376/390625)*(β-1/6)^3*(1-β)^5 + (3525170544/78125)*(β-1/6)^4*(1-β)^4 + (9256363776/390625)*(β-1/6)^5*(1-β)^3 + (2514665088/390625)*(β-1/6)^6*(1-β)^2 + (416544768/390625)*(β-1/6)^7*(1-β) + (52068096/390625)*(β-1/6)^8 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (LGf β - 3/10) * (1080*β^4*(2-β)^4) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

/-! ## convexity of `Ef` -/

private lemma d2fA_nonpos {β : ℝ} (h : β ≤ 1) : d2fA β ≤ 0 := by
  unfold d2fA
  have h1 : (0:ℝ) ≤ 1-β := by linarith
  have h2 : (0:ℝ) ≤ 2*β^2-15*β+76 := by nlinarith [sq_nonneg (4*β-15)]
  have h3 : (0:ℝ) ≤ 11 + (1-β)*(2*β^2-15*β+76) := by nlinarith [mul_nonneg h1 h2]
  have hp : (0:ℝ) < 2*β^4-19*β^3+108*β^2-178*β+89 := by
    have hkey : 2*β^4-19*β^3+108*β^2-178*β+89 = 2 + (1-β)*(11+(1-β)*(2*β^2-15*β+76)) := by ring
    nlinarith [mul_nonneg h1 h3]
  have hd : (0:ℝ) < (2-β)^7 := pow_pos (by linarith) 7
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hd)

private lemma at3_le {β : ℝ} (h : β ≤ 1) : at3 β ≤ (1:ℝ)/6/(2-β) := by
  unfold at3
  apply Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
  apply div_nonneg (by norm_num); linarith

private lemma E2f_nonneg {β : ℝ} (h1 : (1:ℝ)/6 ≤ β) (h2 : β ≤ 1) : (0:ℝ) ≤ E2f β := by
  have hP1 := P1f_lower h1 h2
  have hAR := ARred_lower h1 h2
  have hLG := LGf_lower h1 h2
  have hsplit : E2f β = P1f β + ARred β + LGf β + d2fA β * (at3 β - (1:ℝ)/6/(2-β)) := by
    unfold E2f P1f ARred LGf; ring
  have hd2 : d2fA β ≤ 0 := d2fA_nonpos h2
  have hat : at3 β - (1:ℝ)/6/(2-β) ≤ 0 := by have := at3_le h2; linarith
  have hprod : 0 ≤ d2fA β * (at3 β - (1:ℝ)/6/(2-β)) := mul_nonneg_of_nonpos_of_nonpos hd2 hat
  rw [hsplit]; linarith

private lemma hasDerivAt_Ef_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/8:ℝ) (9/8)) : HasDerivAt Ef (Df x) x :=
  hasDerivAt_Ef (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_Df_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/8:ℝ) (9/8)) : HasDerivAt Df (E2f x) x :=
  hasDerivAt_Df (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma nbd_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/6:ℝ) 1) : Set.Ioo (1/8:ℝ) (9/8) ∈ 𝓝 x := by
  apply isOpen_Ioo.mem_nhds
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private lemma differentiableOn_Ef : DifferentiableOn ℝ Ef (Set.Icc (1/6:ℝ) 1) := by
  intro x hx
  exact (hasDerivAt_Ef_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt

private lemma differentiableOn_deriv_Ef : DifferentiableOn ℝ (deriv Ef) (Set.Ioo (1/6:ℝ) 1) := by
  intro x hx
  have hev : deriv Ef =ᶠ[𝓝 x] Df := by
    filter_upwards [nbd_Ioo hx] with y hy
    exact (hasDerivAt_Ef_Ioo hy).deriv
  have h1 : DifferentiableAt ℝ (deriv Ef) x := by
    rw [hev.differentiableAt_iff]
    exact (hasDerivAt_Df_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt
  exact h1.differentiableWithinAt

private lemma second_deriv_Ef_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (1/6:ℝ) 1) : 0 ≤ deriv^[2] Ef x := by
  have hev : deriv Ef =ᶠ[𝓝 x] Df := by
    filter_upwards [nbd_Ioo hx] with y hy
    exact (hasDerivAt_Ef_Ioo hy).deriv
  have hdd : deriv (deriv Ef) x = E2f x := by
    rw [hev.deriv_eq]
    exact (hasDerivAt_Df_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).deriv
  change 0 ≤ deriv (deriv Ef) x
  rw [hdd]
  exact E2f_nonneg (le_of_lt hx.1) (le_of_lt hx.2)

private lemma convexOn_Ef : ConvexOn ℝ (Set.Icc (1/6:ℝ) 1) Ef := by
  refine convexOn_of_deriv2_nonneg (convex_Icc _ _) differentiableOn_Ef.continuousOn ?_ ?_ ?_
  · rw [interior_Icc]; exact differentiableOn_Ef.mono Set.Ioo_subset_Icc_self
  · rw [interior_Icc]; exact differentiableOn_deriv_Ef
  · intro x hx
    rw [interior_Icc] at hx
    exact second_deriv_Ef_nonneg hx

private lemma Ef_tangent {β : ℝ} (h1 : (1:ℝ)/6 ≤ β) (h2 : β ≤ 1) :
    Ef (11/20) + deriv Ef (11/20) * (β - 11/20) ≤ Ef β := by
  have hmem : β ∈ Set.Icc (1/6:ℝ) 1 := ⟨h1, h2⟩
  have hmem2 : (11/20:ℝ) ∈ Set.Icc (1/6:ℝ) 1 := by norm_num
  have hdiff : DifferentiableAt ℝ Ef (11/20) :=
    (hasDerivAt_Ef_Ioo (by norm_num)).differentiableAt
  rcases lt_trichotomy β (11/20) with hlt | heq | hgt
  · have hsl := convexOn_Ef.slope_le_deriv hmem hmem2 hlt hdiff
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < 11/20 - β := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith
  · subst heq; simp
  · have hsl := convexOn_Ef.deriv_le_slope hmem2 hmem hgt hdiff
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < β - 11/20 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith

/-! ## numeric bounds -/

private lemma arctan_10_57_lower : (17366/100000:ℝ) ≤ Real.arctan (10/57) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((10:ℝ)/57) (by norm_num)
  have hpoly : (17366/100000:ℝ) ≤ (10/57) - (10/57)^3/3 + (10/57)^5/5 - (10/57)^7/7
      + (10/57)^9/9 - (10/57)^11/11 + (10/57)^13/13 - (10/57)^15/15 := by norm_num
  linarith

private lemma arctan_10_93_lower : (10711/100000:ℝ) ≤ Real.arctan (10/93) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((10:ℝ)/93) (by norm_num)
  have hpoly : (10711/100000:ℝ) ≤ (10/93) - (10/93)^3/3 + (10/93)^5/5 - (10/93)^7/7
      + (10/93)^9/9 - (10/93)^11/11 + (10/93)^13/13 - (10/93)^15/15 := by norm_num
  linarith

private lemma arctan_10_87_lower : (11444/100000:ℝ) ≤ Real.arctan (10/87) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((10:ℝ)/87) (by norm_num)
  have hpoly : (11444/100000:ℝ) ≤ (10/87) - (10/87)^3/3 + (10/87)^5/5 - (10/87)^7/7
      + (10/87)^9/9 - (10/87)^11/11 + (10/87)^13/13 - (10/87)^15/15 := by norm_num
  linarith

private lemma arctan_10_87_upper : Real.arctan (10/87) ≤ (11445/100000:ℝ) := by
  have h := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4 ((10:ℝ)/87) (by norm_num)
  have hpoly : (10/87) - (10/87)^3/3 + (10/87)^5/5 - (10/87)^7/7 + (10/87)^9/9 ≤ (11445/100000:ℝ) := by norm_num
  linarith

private lemma log_29_10_upper : Real.log (29/10) ≤ (106472/100000:ℝ) := by
  have hsplit : Real.log ((29:ℝ)/10) = Real.log 3 + Real.log ((29:ℝ)/30) := by
    rw [show (29:ℝ)/10 = 3*((29:ℝ)/30) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hsplit]
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/30)) (by norm_num) 4
  have heq : Real.log ((29:ℝ)/30) = Real.log (1 - (1:ℝ)/30) := by congr 1; norm_num
  rw [heq]
  have hub : Real.log ((29:ℝ)/30) ≤ -(∑ i ∈ Finset.range 4, ((1:ℝ)/30)^(i+1)/(i+1)) + (1/30)^5/(1-1/30) := by
    have h2 := (abs_le.mp h).2; linarith
  have h3 := Real.log_three_lt_d9
  have hkey : (1.0986122888:ℝ) + (-(∑ i ∈ Finset.range 4, ((1:ℝ)/30)^(i+1)/(i+1)) + (1/30)^5/(1-1/30)) ≤ (106472/100000:ℝ) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma log_11_10_upper : Real.log (11/10) ≤ (9532/100000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-1:ℝ)/10)) (by norm_num) 4
  have heq : Real.log ((11:ℝ)/10) = Real.log (1 - ((-1:ℝ)/10)) := by congr 1; norm_num
  rw [heq]
  have hub : Real.log ((11:ℝ)/10) ≤ -(∑ i ∈ Finset.range 4, (-(1:ℝ)/10)^(i+1)/(i+1)) + (1/10)^5/(1-1/10) := by
    have h2 := (abs_le.mp h).2; linarith
  have hkey : -(∑ i ∈ Finset.range 4, (-(1:ℝ)/10)^(i+1)/(i+1)) + (1/10)^5/(1-1/10) ≤ (9532/100000:ℝ) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma log_one_sixth_lower : (-(1791760/1000000):ℝ) ≤ Real.log ((1:ℝ)/6) := by
  rw [one_div, Real.log_inv]
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog6]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  linarith

private lemma Ef_at_1120_lower : -(305:ℝ)/1000 ≤ Ef (11/20) := by
  have h1 : at1 (11/20) = Real.arctan (10/57) := by unfold at1; norm_num
  have h2 : at2 (11/20) = Real.arctan (10/93) := by unfold at2; norm_num
  have h3 : at3 (11/20) = Real.arctan (10/87) := by unfold at3; norm_num
  have h4 : fA (11/20) = (14530878:ℝ)/20511149 := by unfold fA; norm_num
  have h5 : fQ1 (11/20) = (480298199400:ℝ)/41597714237641 := by unfold fQ1; norm_num
  have h6 : lg1 (11/20) = Real.log (29/10) := by unfold lg1; norm_num
  have h7 : lg2 (11/20) = Real.log (11/10) := by unfold lg2; norm_num
  have h8 : n2 (11/20) = (400:ℝ)/841 := by unfold n2; norm_num
  have h9 : m2 (11/20) = (400:ℝ)/121 := by unfold m2; norm_num
  have hE : Ef (11/20) = ((13/5)*(at1 (11/20)+at2 (11/20)) + (fA (11/20)*at3 (11/20) + fQ1 (11/20))) - (T5 (11/20)+T6 (11/20)) := rfl
  rw [hE, h1, h2, h3, h4, h5]
  unfold T5 T6
  rw [h6, h7, h8, h9]
  unfold Kc C3
  have ha1 := arctan_10_57_lower
  have ha2 := arctan_10_93_lower
  have ha3 := arctan_10_87_lower
  have hl1 := log_29_10_upper
  have hl2 := log_11_10_upper
  have hl3 := log_one_sixth_lower
  linarith

private lemma Df_at_1120_lower : (0:ℝ) ≤ Df (11/20) := by
  have h1 : dat1 (11/20) = (600:ℝ)/3349 := by unfold dat1; norm_num
  have h2 : dat2 (11/20) = -(600:ℝ)/8749 := by unfold dat2; norm_num
  have h3 : dat3 (11/20) = (600:ℝ)/7669 := by unfold dat3; norm_num
  have h4 : fA (11/20) = (14530878:ℝ)/20511149 := by unfold fA; norm_num
  have h5 : dfA (11/20) = -(700504400:ℝ)/594823321 := by unfold dfA; norm_num
  have h6 : dfQ1 (11/20) = -(213541453296576000:ℝ)/9251373244165596041 := by unfold dfQ1; norm_num
  have h7 : dT5 (11/20) = -(226570:ℝ)/1975509 := by unfold dT5 dlg1 n3 C3; norm_num
  have h8 : dT6 (11/20) = (32170:ℝ)/107811 := by unfold dT6 dlg2 m3 C3; norm_num
  have h3e : at3 (11/20) = Real.arctan (10/87) := by unfold at3; norm_num
  have hD : Df (11/20) = ((13/5)*(dat1 (11/20)+dat2 (11/20)) + ((dfA (11/20)*at3 (11/20) + fA (11/20)*dat3 (11/20)) + dfQ1 (11/20))) - (dT5 (11/20)+dT6 (11/20)) := rfl
  rw [hD, h1, h2, h3, h4, h5, h6, h7, h8, h3e]
  have haU := arctan_10_87_upper
  have hmult : (-(700504400:ℝ)/594823321)*((11445:ℝ)/100000) ≤ (-(700504400:ℝ)/594823321)*Real.arctan (10/87) :=
    mul_le_mul_of_nonpos_left haU (by norm_num)
  linarith

private lemma Df_at_1120_upper : Df (11/20) ≤ (1:ℝ)/400 := by
  have h1 : dat1 (11/20) = (600:ℝ)/3349 := by unfold dat1; norm_num
  have h2 : dat2 (11/20) = -(600:ℝ)/8749 := by unfold dat2; norm_num
  have h3 : dat3 (11/20) = (600:ℝ)/7669 := by unfold dat3; norm_num
  have h4 : fA (11/20) = (14530878:ℝ)/20511149 := by unfold fA; norm_num
  have h5 : dfA (11/20) = -(700504400:ℝ)/594823321 := by unfold dfA; norm_num
  have h6 : dfQ1 (11/20) = -(213541453296576000:ℝ)/9251373244165596041 := by unfold dfQ1; norm_num
  have h7 : dT5 (11/20) = -(226570:ℝ)/1975509 := by unfold dT5 dlg1 n3 C3; norm_num
  have h8 : dT6 (11/20) = (32170:ℝ)/107811 := by unfold dT6 dlg2 m3 C3; norm_num
  have h3e : at3 (11/20) = Real.arctan (10/87) := by unfold at3; norm_num
  have hD : Df (11/20) = ((13/5)*(dat1 (11/20)+dat2 (11/20)) + ((dfA (11/20)*at3 (11/20) + fA (11/20)*dat3 (11/20)) + dfQ1 (11/20))) - (dT5 (11/20)+dT6 (11/20)) := rfl
  rw [hD, h1, h2, h3, h4, h5, h6, h7, h8, h3e]
  have haL := arctan_10_87_lower
  have hmult : (-(700504400:ℝ)/594823321)*Real.arctan (10/87) ≤ (-(700504400:ℝ)/594823321)*((11444:ℝ)/100000) :=
    mul_le_mul_of_nonpos_left haL (by norm_num)
  linarith

private lemma deriv_Ef_1120 : deriv Ef (11/20) = Df (11/20) :=
  (hasDerivAt_Ef_Ioo (by norm_num)).deriv


theorem WJ_sixth_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    -(31:ℝ)/100 ≤
      ( (13/5)*(Real.arctan ((1/6)/(3/2-β)) + Real.arctan ((1/6)/(1+β)))
        + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan ((1/6)/(2-β))
        + ((2-β)^2-β^2)^2/8 * ((Real.arctan ((1/6)/(2-β)) + (2-β)*(1/6)/((2-β)^2+(1/6)^2))/(2*(2-β)^3))
        + ((2-β)^2-β^2)^3/16 * (3*Real.arctan ((1/6)/(2-β))/(8*(2-β)^5) + (1/6)*(5*(2-β)^2+3*(1/6)^2)/(8*(2-β)^4*((2-β)^2+(1/6)^2)^2)) )
      - ((1/6)*(Real.log (2*(2-β)) - Real.log (1/6) + 1) + (1/6)^3/(12*(2-β)^2))
      - (if (1/6 : ℝ) ≤ β then (1/6)*(Real.log (2*β) - Real.log (1/6) + 1) + (1/6)^3/(12*β^2)
          else β*(Real.log 2 + 13/12) + β*Real.log ((1/6)/β)) := by
  rcases lt_or_ge β ((1:ℝ)/6) with hlt | hge
  · -- case β < 1/6
    rw [if_neg (not_le.mpr hlt)]
    have hβle : β ≤ (1:ℝ)/6 := le_of_lt hlt
    have hP1 : (13/5)*((11:ℝ)/100 + (14:ℝ)/100) ≤
        (13/5)*(Real.arctan ((1:ℝ)/6/(3/2-β)) + Real.arctan ((1:ℝ)/6/(1+β))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have ha1 : (11:ℝ)/100 ≤ Real.arctan ((1:ℝ)/6/(3/2-β)) := by
        have hx : (1:ℝ)/9 ≤ (1:ℝ)/6/(3/2-β) := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 3/2-β)]; linarith
        have hp := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_lower_poly_of_nonneg (x := (1:ℝ)/9) (by norm_num)
        have h2 : (11:ℝ)/100 ≤ (1:ℝ)/9 - ((1:ℝ)/9)^3/3 := by norm_num
        exact le_trans h2 (le_trans hp (Real.arctan_mono hx))
      have ha2 : (14:ℝ)/100 ≤ Real.arctan ((1:ℝ)/6/(1+β)) := by
        have hx : (1:ℝ)/7 ≤ (1:ℝ)/6/(1+β) := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 1+β)]; linarith
        have hp := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_lower_poly_of_nonneg (x := (1:ℝ)/7) (by norm_num)
        have h2 : (14:ℝ)/100 ≤ (1:ℝ)/7 - ((1:ℝ)/7)^3/3 := by norm_num
        exact le_trans h2 (le_trans hp (Real.arctan_mono hx))
      linarith
    have hP2 : ((10:ℝ)/11)*((83:ℝ)/1000) ≤
        ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan ((1:ℝ)/6/(2-β)) := by
      have hcoef : (10:ℝ)/11 ≤ ((2-β)^2-β^2)/(2*(2-β)) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 2*(2-β))]
        nlinarith [hβ0]
      have ha : (83:ℝ)/1000 ≤ Real.arctan ((1:ℝ)/6/(2-β)) := by
        have hx : (1:ℝ)/12 ≤ (1:ℝ)/6/(2-β) := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 2-β)]; linarith
        have hp := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_lower_poly_of_nonneg (x := (1:ℝ)/12) (by norm_num)
        have h2 : (83:ℝ)/1000 ≤ (1:ℝ)/12 - ((1:ℝ)/12)^3/3 := by norm_num
        exact le_trans h2 (le_trans hp (Real.arctan_mono hx))
      have h0 : (0:ℝ) ≤ Real.arctan ((1:ℝ)/6/(2-β)) := by
        exact (Real.arctan_nonneg).mpr (by apply div_nonneg (by norm_num); linarith)
      nlinarith [hcoef, ha, h0]
    have hP34 : (0:ℝ) ≤
        ((2-β)^2-β^2)^2/8 * ((Real.arctan ((1:ℝ)/6/(2-β)) + (2-β)*((1:ℝ)/6)/((2-β)^2+((1:ℝ)/6)^2))/(2*(2-β)^3))
        + ((2-β)^2-β^2)^3/16 * (3*Real.arctan ((1:ℝ)/6/(2-β))/(8*(2-β)^5)
            + ((1:ℝ)/6)*(5*(2-β)^2+3*((1:ℝ)/6)^2)/(8*(2-β)^4*((2-β)^2+((1:ℝ)/6)^2)^2)) := by
      have hD : (0:ℝ) < (2-β)^2-β^2 := by nlinarith [hβ0, hβle]
      have h2b : (0:ℝ) < 2-β := by linarith
      have ha0 : (0:ℝ) ≤ Real.arctan ((1:ℝ)/6/(2-β)) :=
        (Real.arctan_nonneg).mpr (by apply div_nonneg (by norm_num); linarith)
      have hX : (0:ℝ) ≤ (Real.arctan ((1:ℝ)/6/(2-β)) + (2-β)*((1:ℝ)/6)/((2-β)^2+((1:ℝ)/6)^2))/(2*(2-β)^3) := by
        apply div_nonneg _ (by positivity)
        have hb : (0:ℝ) ≤ (2-β)*((1:ℝ)/6)/((2-β)^2+((1:ℝ)/6)^2) := by positivity
        linarith
      have hY : (0:ℝ) ≤ 3*Real.arctan ((1:ℝ)/6/(2-β))/(8*(2-β)^5)
          + ((1:ℝ)/6)*(5*(2-β)^2+3*((1:ℝ)/6)^2)/(8*(2-β)^4*((2-β)^2+((1:ℝ)/6)^2)^2) := by
        have h1 : (0:ℝ) ≤ 3*Real.arctan ((1:ℝ)/6/(2-β))/(8*(2-β)^5) := by positivity
        have h2 : (0:ℝ) ≤ ((1:ℝ)/6)*(5*(2-β)^2+3*((1:ℝ)/6)^2)/(8*(2-β)^4*((2-β)^2+((1:ℝ)/6)^2)^2) := by positivity
        linarith
      have hD2 : (0:ℝ) ≤ ((2-β)^2-β^2)^2/8 := by positivity
      have hD3 : (0:ℝ) ≤ ((2-β)^2-β^2)^3/16 := by positivity
      exact add_nonneg (mul_nonneg hD2 hX) (mul_nonneg hD3 hY)
    have hT5 : (1:ℝ)/6*(Real.log (2*(2-β)) - Real.log ((1:ℝ)/6) + 1) + ((1:ℝ)/6)^3/(12*(2-β)^2) ≤ (6968:ℝ)/10000 := by
      have h2b : (1:ℝ) ≤ (2-β)^2 := by nlinarith
      have hl : Real.log (2*(2-β)) - Real.log ((1:ℝ)/6) + 1 ≤ 4.1780539 := by
        have h4 : Real.log (2*(2-β)) ≤ 2*0.6931471808 := by
          have hle : (2:ℝ)*(2-β) ≤ 4 := by linarith
          calc Real.log (2*(2-β)) ≤ Real.log 4 := Real.log_le_log (by linarith) hle
            _ = 2*Real.log 2 := by rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
            _ ≤ 2*0.6931471808 := by linarith [Real.log_two_lt_d9]
        have h6 : Real.log 6 ≤ 1.7917594696 := by
          have ha := Real.log_two_lt_d9; have hb := Real.log_three_lt_d9
          rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
          linarith
        have hne6 : Real.log ((1:ℝ)/6) = -Real.log 6 := by rw [one_div, Real.log_inv]
        rw [hne6]; linarith
      have hc : ((1:ℝ)/6)^3/(12*(2-β)^2) ≤ ((1:ℝ)/6)^3/12 := by
        have hpos : (0:ℝ) < 12*(2-β)^2 := by positivity
        rw [div_le_iff₀ hpos]
        nlinarith [h2b]
      nlinarith
    have hT6 : β*(Real.log 2 + 13/12) + β*Real.log ((1:ℝ)/6/β) ≤ (2961:ℝ)/10000 := by
      have hl2 : Real.log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
      have hlogc : Real.log ((1:ℝ)/6/β) ≤ (1:ℝ)/6/β - 1 := by
        apply Real.log_le_sub_one_of_pos
        apply div_pos (by norm_num) hβ0
      have h1 : β*Real.log ((1:ℝ)/6/β) ≤ (1:ℝ)/6 - β := by
        have h := mul_le_mul_of_nonneg_left hlogc (le_of_lt hβ0)
        have h2 : β*((1:ℝ)/6/β - 1) = (1:ℝ)/6 - β := by field_simp <;> ring
        linarith [h]
      have h3 : β*(Real.log 2 + 13/12) ≤ (1:ℝ)/6*(0.6931471808 + 13/12) := by
        have hle : Real.log 2 + 13/12 ≤ 0.6931471808 + 13/12 := by linarith
        calc β*(Real.log 2 + 13/12) ≤ β*(0.6931471808 + 13/12) := mul_le_mul_of_nonneg_left hle (le_of_lt hβ0)
          _ ≤ (1:ℝ)/6*(0.6931471808 + 13/12) := mul_le_mul_of_nonneg_right hβle (by norm_num)
      nlinarith [h1, h3]
    nlinarith [hP1, hP2, hP34, hT5, hT6]
  · -- case 1/6 ≤ β
    rw [if_pos hge]
    have key : -(31:ℝ)/100 ≤ Ef β := by
      have htan := Ef_tangent hge (le_of_lt hβ1)
      rw [deriv_Ef_1120] at htan
      have hElow := Ef_at_1120_lower
      have hDlow := Df_at_1120_lower
      have hDhi := Df_at_1120_upper
      have hprod : (1/400 : ℝ) * (-(23/60)) ≤ Df (11/20) * (β - 11/20) := by
        have h1 : Df (11/20) * (-(23/60)) ≤ Df (11/20) * (β - 11/20) :=
          mul_le_mul_of_nonneg_left (by linarith) hDlow
        have h2 : (1/400 : ℝ) * (-(23/60)) ≤ Df (11/20) * (-(23/60)) :=
          mul_le_mul_of_nonpos_right hDhi (by norm_num)
        linarith
      linarith
    convert key using 1
    unfold Ef at1 at2 at3 fA fQ1 T5 T6 lg1 lg2 n2 m2 Kc C3
    have hb0 : β ≠ 0 := by linarith
    have h2b : (2:ℝ)-β ≠ 0 := by linarith
    have h32 : (3:ℝ)/2-β ≠ 0 := by linarith
    have hm1 : (1:ℝ)+β ≠ 0 := by linarith
    field_simp
    ring

end
end Commons.Analysis.Real