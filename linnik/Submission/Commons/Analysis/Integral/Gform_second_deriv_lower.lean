import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg

namespace Commons.Analysis.Integral

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1600000

/-! ## Definitions -/

private def at1 (β : ℝ) : ℝ := Real.arctan ((1/4)/(3/2-β))
private def dat1 (β : ℝ) : ℝ := (1/4)/((3/2-β)^2+(1/4)^2)
private def d2at1 (β : ℝ) : ℝ := 2*(1/4)*(3/2-β)/(((3/2-β)^2+(1/4)^2)^2)

private def at2 (β : ℝ) : ℝ := Real.arctan ((1/4)/(1+β))
private def dat2 (β : ℝ) : ℝ := -(1/4)/((1+β)^2+(1/4)^2)
private def d2at2 (β : ℝ) : ℝ := 2*(1/4)*(1+β)/(((1+β)^2+(1/4)^2)^2)

private def at3 (β : ℝ) : ℝ := Real.arctan ((1/4)/(2-β))
private def dat3 (β : ℝ) : ℝ := (1/4)/((2-β)^2+(1/4)^2)
private def d2at3 (β : ℝ) : ℝ := 2*(1/4)*(2-β)/(((2-β)^2+(1/4)^2)^2)

private def at4 (β : ℝ) : ℝ := Real.arctan ((1/4)/(2*(2-β)))
private def dat4 (β : ℝ) : ℝ := 2*(1/4)/(4*(2-β)^2+(1/4)^2)
private def d2at4 (β : ℝ) : ℝ := 16*(1/4)*(2-β)/((4*(2-β)^2+(1/4)^2)^2)

private def at5 (β : ℝ) : ℝ := Real.arctan ((1/4)/(2*β))
private def dat5 (β : ℝ) : ℝ := -2*(1/4)/(4*β^2+(1/4)^2)
private def d2at5 (β : ℝ) : ℝ := 16*(1/4)*β/((4*β^2+(1/4)^2)^2)

private def lg1 (β : ℝ) : ℝ := Real.log (8*(2-β)+1/(8*(2-β)))
private def dlg1 (β : ℝ) : ℝ := (1-64*(2-β)^2)/((2-β)*(64*(2-β)^2+1))
private def d2lg1 (β : ℝ) : ℝ :=
  -(4096*β^4-32768*β^3+98048*β^2-130048*β+64511)/((2-β)^2*(64*(2-β)^2+1)^2)

private def lg2 (β : ℝ) : ℝ := Real.log (8*β+1/(8*β))
private def dlg2 (β : ℝ) : ℝ := (64*β^2-1)/(β*(64*β^2+1))
private def d2lg2 (β : ℝ) : ℝ := -(4096*β^4-256*β^2-1)/(β^2*(64*β^2+1)^2)

private def fA (β : ℝ) : ℝ := 2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5)
private def dfA (β : ℝ) : ℝ := -(2*β^4-18*β^3+81*β^2-136*β+75)/(2*(2-β)^6)
private def d2fA (β : ℝ) : ℝ := -(2*β^4-19*β^3+108*β^2-178*β+89)/(2-β)^7

private def fQ1 (β : ℝ) : ℝ := (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
  + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2)
private def dfQ1 (β : ℝ) : ℝ :=
  2*(β-1)*(1024*β^7-16128*β^6+96064*β^5-287328*β^4+462400*β^3-381599*β^2+124781*β+1942)
    /((2-β)^5*4096*((2-β)^2+(1/4)^2)^3)
private def d2fQ1 (β : ℝ) : ℝ :=
  4*(24576*β^10-516096*β^9+4334592*β^8-19544832*β^7+51933408*β^6-81143360*β^5
      +63792320*β^4+608945*β^3-45627275*β^2+34820522*β-8672974)
    /((2-β)^6*65536*((2-β)^2+(1/4)^2)^4)

private def fB (β : ℝ) : ℝ := (1/4) - (1/4)^3/(12*(2-β)^2)
private def dfB (β : ℝ) : ℝ := -1/(384*(2-β)^3)
private def d2fB (β : ℝ) : ℝ := -1/(128*(2-β)^4)

private def fG (β : ℝ) : ℝ := 16*(2-β)/3
private def dfG (_β : ℝ) : ℝ := -16/3

private def fQ2 (β : ℝ) : ℝ := -5*(1/4)/3 + (1/4)^3/(36*(2-β)^2)
private def dfQ2 (β : ℝ) : ℝ := 1/(1152*(2-β)^3)
private def d2fQ2 (β : ℝ) : ℝ := 1/(384*(2-β)^4)

private def fC (β : ℝ) : ℝ := (1/4) - (1/4)^3/(3*(2*((2-β)^2+β^2)))
private def dfC (β : ℝ) : ℝ := (β-1)/(96*((2-β)^2+β^2)^2)
private def d2fC (β : ℝ) : ℝ := (-3*β^2+6*β-2)/(48*((2-β)^2+β^2)^3)

private def fH (β : ℝ) : ℝ := 4*β + 16*β^3/(3*(2*((2-β)^2+β^2)))
private def dfH (β : ℝ) : ℝ := 32*(2*β^4-8*β^3+15*β^2-12*β+6)/(3*((2-β)^2+β^2)^2)
private def d2fH (β : ℝ) : ℝ := 128*β*(β^2-6*β+6)/(3*((2-β)^2+β^2)^3)

private def fQ3 (β : ℝ) : ℝ := -1/4 + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2))
private def dfQ3 (β : ℝ) : ℝ := (384*β^2-769*β+1)/(288*((2-β)^2+β^2)^2)
private def d2fQ3 (β : ℝ) : ℝ := (-768*β^3+2307*β^2-6*β-1534)/(144*((2-β)^2+β^2)^3)


/-! ## Basic derivative helpers -/

private lemma hd_sub (c β : ℝ) : HasDerivAt (fun x : ℝ => x - c) 1 β :=
  (hasDerivAt_id β).sub_const c

private lemma hd_csub (c β : ℝ) : HasDerivAt (fun x : ℝ => c - x) (-1) β :=
  HasDerivAt.const_sub c (hasDerivAt_id β)

private lemma hd_add (c β : ℝ) : HasDerivAt (fun x : ℝ => c + x) 1 β :=
  (hasDerivAt_id β).const_add c

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

/-! ## arctan atoms -/

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
  have hlin : HasDerivAt (fun x : ℝ => a + x) 1 β := hd_add a β
  have hd : HasDerivAt (fun x : ℝ => k/(a+x)) (-(k/(a+β)^2)) β := by
    have h2 := (hasDerivAt_const β k).div hlin (by simpa using h)
    refine h2.congr_deriv ?_
    ring
  have h3 := (Real.hasDerivAt_arctan (k/(a+β))).comp β hd
  refine h3.congr_deriv ?_
  field_simp
  try ring

private lemma hd_arctan_csub_mul {a m k : ℝ} {β : ℝ} (hm : m ≠ 0) (h : a - β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.arctan (k/(m*(a-x)))) (k*m/((m*(a-β))^2+k^2)) β := by
  have hlin : HasDerivAt (fun x : ℝ => m*(a-x)) (-m) β := by
    have h1 : HasDerivAt (fun x : ℝ => a - x) (-1) β := hd_csub a β
    simpa using h1.const_mul m
  have hd : HasDerivAt (fun x : ℝ => k/(m*(a-x))) (k*m/(m*(a-β))^2) β := by
    have h2 := (hasDerivAt_const β k).div hlin (by
      change m * (a-β) ≠ 0
      exact mul_ne_zero hm h)
    refine h2.congr_deriv ?_
    ring
  have h3 := (Real.hasDerivAt_arctan (k/(m*(a-β)))).comp β hd
  refine h3.congr_deriv ?_
  field_simp
  try ring

private lemma hd_arctan_mul {m k : ℝ} {β : ℝ} (hm : m ≠ 0) (h : β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.arctan (k/(m*x))) (-(k*m)/((m*β)^2+k^2)) β := by
  have hlin : HasDerivAt (fun x : ℝ => m*x) m β := by
    simpa using (hasDerivAt_id β).const_mul m
  have hd : HasDerivAt (fun x : ℝ => k/(m*x)) (-(k*m/(m*β)^2)) β := by
    have h2 := (hasDerivAt_const β k).div hlin (by
      change m * β ≠ 0
      exact mul_ne_zero hm h)
    refine h2.congr_deriv ?_
    ring
  have h3 := (Real.hasDerivAt_arctan (k/(m*β))).comp β hd
  refine h3.congr_deriv ?_
  field_simp
  try ring

private lemma hasDerivAt_at1 {β : ℝ} (h : β ≠ 3/2) : HasDerivAt at1 (dat1 β) β :=
  hd_arctan_csub (a := (3:ℝ)/2) (k := (1:ℝ)/4) (β := β) (by
    intro hc; exact h (by linarith [hc]))

private lemma hasDerivAt_at2 {β : ℝ} (h : β ≠ -1) : HasDerivAt at2 (dat2 β) β := by
  have hh := hd_arctan_add (a := (1:ℝ)) (k := (1:ℝ)/4) (β := β) (by
    intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat2]; try ring

private lemma hasDerivAt_at3 {β : ℝ} (h : β ≠ 2) : HasDerivAt at3 (dat3 β) β :=
  hd_arctan_csub (a := (2:ℝ)) (k := (1:ℝ)/4) (β := β) (by
    intro hc; exact h (by linarith [hc]))

private lemma hasDerivAt_at4 {β : ℝ} (h : β ≠ 2) : HasDerivAt at4 (dat4 β) β := by
  have hh := hd_arctan_csub_mul (a := (2:ℝ)) (m := (2:ℝ)) (k := (1:ℝ)/4) (β := β)
    (by norm_num) (by intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat4]; ring

private lemma hasDerivAt_at5 {β : ℝ} (h : β ≠ 0) : HasDerivAt at5 (dat5 β) β := by
  have hh := hd_arctan_mul (m := (2:ℝ)) (k := (1:ℝ)/4) (β := β) (by norm_num) h
  refine hh.congr_deriv ?_
  rw [dat5]; ring


/-! ## log atoms -/

private lemma hasDerivAt_lg1 {β : ℝ} (h : β ≠ 2) : HasDerivAt lg1 (dlg1 β) β := by
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hnum : HasDerivAt (fun x : ℝ => 8*(2-x)+1/(8*(2-x))) (-8 + 1/(8*(2-β)^2)) β := by
    have h1 : HasDerivAt (fun x : ℝ => 8*(2-x)) (-8) β := by
      simpa using (hd_twom β).const_mul 8
    have hlin : HasDerivAt (fun x : ℝ => 8*(2-x)) (-8) β := by
      simpa using (hd_twom β).const_mul 8
    have h2 : HasDerivAt (fun x : ℝ => 1/(8*(2-x))) (1/(8*(2-β)^2)) β := by
      have h3 := hd_div_const (c := (1:ℝ)) hlin (by
        change (8:ℝ)*(2-β) ≠ 0
        exact mul_ne_zero (by norm_num) hne)
      refine h3.congr_deriv ?_
      field_simp
      try ring
    exact h1.add h2
  have hpos : (8*(2-β)+1/(8*(2-β))) ≠ 0 := by
    have heq : 8*(2-β)+1/(8*(2-β)) = (64*(2-β)^2+1)/(8*(2-β)) := by field_simp; ring
    rw [heq]
    apply div_ne_zero _ (by positivity)
    nlinarith [sq_nonneg (8*(2-β))]
  have h3 := (Real.hasDerivAt_log hpos).comp β hnum
  unfold lg1
  refine h3.congr_deriv ?_
  rw [dlg1]
  field_simp
  ring

private lemma hasDerivAt_dlg1 {β : ℝ} (h : β ≠ 2) : HasDerivAt dlg1 (d2lg1 β) β := by
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold dlg1
  have hnum : HasDerivAt (fun x : ℝ => 1-64*(2-x)^2) (128*(2-β)) β := by
    have h2 := ((hasDerivAt_const β (1:ℝ)).sub (((hd_twom β).pow 2).const_mul (64:ℝ)))
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hden : HasDerivAt (fun x : ℝ => (2-x)*(64*(2-x)^2+1)) (-(192*(2-β)^2+1)) β := by
    have h2 : HasDerivAt (fun x : ℝ => 64*(2-x)^2+1) (-128*(2-β)) β := by
      have h3 := (((hd_twom β).pow 2).const_mul (64:ℝ)).add_const (1:ℝ)
      refine h3.congr_deriv ?_
      simp only [Nat.reduceSub, pow_one]
      ring
    have h4 := (hd_twom β).mul h2
    refine h4.congr_deriv ?_
    ring
  have hd0 : ((2:ℝ)-β)*(64*(2-β)^2+1) ≠ 0 :=
    mul_ne_zero hne (by positivity)
  have h5 := hnum.div hden hd0
  refine h5.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2lg1]
  field_simp
  ring

private lemma hasDerivAt_lg2 {β : ℝ} (h : β ≠ 0) : HasDerivAt lg2 (dlg2 β) β := by
  have hnum : HasDerivAt (fun x : ℝ => 8*x+1/(8*x)) (8 - 1/(8*β^2)) β := by
    have h1 : HasDerivAt (fun x : ℝ => 8*x) 8 β := by simpa using (hasDerivAt_id β).const_mul 8
    have h2 : HasDerivAt (fun x : ℝ => 1/(8*x)) (-(1/(8*β^2))) β := by
      have hlin : HasDerivAt (fun x : ℝ => 8*x) 8 β := by simpa using (hasDerivAt_id β).const_mul 8
      have h3 := hd_div_const (c := (1:ℝ)) hlin (by
        change (8:ℝ)*β ≠ 0
        exact mul_ne_zero (by norm_num) h)
      refine h3.congr_deriv ?_
      field_simp
      try ring
    exact h1.add h2
  have hpos : (8*β+1/(8*β)) ≠ 0 := by
    have heq : 8*β+1/(8*β) = (64*β^2+1)/(8*β) := by field_simp; ring
    rw [heq]
    apply div_ne_zero _ (by positivity)
    nlinarith [sq_nonneg (8*β)]
  have h3 := (Real.hasDerivAt_log hpos).comp β hnum
  unfold lg2
  refine h3.congr_deriv ?_
  rw [dlg2]
  field_simp
  ring

private lemma hasDerivAt_dlg2 {β : ℝ} (h : β ≠ 0) : HasDerivAt dlg2 (d2lg2 β) β := by
  unfold dlg2
  have hnum : HasDerivAt (fun x : ℝ => 64*x^2-1) (128*β) β := by
    have h2 := (((hd_sq β)).const_mul (64:ℝ)).sub_const (1:ℝ)
    refine h2.congr_deriv ?_
    ring
  have hden : HasDerivAt (fun x : ℝ => x*(64*x^2+1)) (192*β^2+1) β := by
    have h2 : HasDerivAt (fun x : ℝ => 64*x^2+1) (128*β) β := by
      have h3 := ((hd_sq β).const_mul (64:ℝ)).add_const (1:ℝ)
      refine h3.congr_deriv ?_
      ring
    have h4 := (hasDerivAt_id β).mul h2
    refine h4.congr_deriv ?_
    simp only [id_eq]
    ring
  have hd0 : β*(64*β^2+1) ≠ 0 := mul_ne_zero h (by positivity)
  have h5 := hnum.div hden hd0
  refine h5.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2lg2]
  field_simp
  ring

/-! ## second derivatives of arctan atoms -/

private lemma hasDerivAt_dat1 (β : ℝ) : HasDerivAt dat1 (d2at1 β) β := by
  unfold dat1
  have hq : HasDerivAt (fun x : ℝ => ((3/2:ℝ)-x)^2+(1/4)^2) (-2*((3/2:ℝ)-β)) β := by
    have h2 := ((hd_csub (3/2) β).pow 2).add_const ((1/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((3/2:ℝ)-β)^2+(1/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := (1:ℝ)/4) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at1]
  field_simp
  try ring

private lemma hasDerivAt_dat2 (β : ℝ) : HasDerivAt dat2 (d2at2 β) β := by
  unfold dat2
  have hq : HasDerivAt (fun x : ℝ => ((1:ℝ)+x)^2+(1/4)^2) (2*((1:ℝ)+β)) β := by
    have h2 := (((hasDerivAt_id β).const_add (1:ℝ)).pow 2).add_const ((1/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]
    ring
  have hq0 : ((1:ℝ)+β)^2+(1/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := (-((1:ℝ)/4))) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at2]
  field_simp
  try ring

private lemma hasDerivAt_dat3 (β : ℝ) : HasDerivAt dat3 (d2at3 β) β := by
  unfold dat3
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^2+(1/4)^2) (-2*((2:ℝ)-β)) β := by
    have h2 := ((hd_csub (2) β).pow 2).add_const ((1/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((2:ℝ)-β)^2+(1/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := (1:ℝ)/4) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at3]
  field_simp
  try ring

private lemma hasDerivAt_dat4 (β : ℝ) : HasDerivAt dat4 (d2at4 β) β := by
  unfold dat4
  have hq : HasDerivAt (fun x : ℝ => 4*((2:ℝ)-x)^2+(1/4)^2) (-8*((2:ℝ)-β)) β := by
    have h2 := (((hd_csub (2) β).pow 2).const_mul (4:ℝ)).add_const ((1/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : 4*((2:ℝ)-β)^2+(1/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := (2:ℝ)*(1/4)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at4]
  field_simp
  try ring

private lemma hasDerivAt_dat5 (β : ℝ) : HasDerivAt dat5 (d2at5 β) β := by
  unfold dat5
  have hq : HasDerivAt (fun x : ℝ => 4*x^2+(1/4)^2) (8*β) β := by
    have h2 := (((hd_sq β)).const_mul (4:ℝ)).add_const ((1/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    ring
  have hq0 : 4*β^2+(1/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((-2:ℝ)*((1:ℝ)/4))) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at5]
  field_simp
  try ring



/-! ## prefactors -/

private lemma hd_W (β : ℝ) : HasDerivAt (fun x : ℝ => (2-x)^2+x^2) (4*β-4) β := by
  have h := (hd_sq_sub 2 β).add (hd_sq β)
  refine h.congr_deriv ?_
  ring

private lemma hd_dm (β : ℝ) : HasDerivAt (fun x : ℝ => 2*((2-x)^2+x^2)) (8*β-8) β := by
  have h := (hd_W β).const_mul (2:ℝ)
  refine h.congr_deriv ?_
  ring

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
  field_simp [hne]
  ring

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
  field_simp [hne]
  ring

private lemma hasDerivAt_fQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt fQ1 (dfQ1 β) β := by
  unfold fQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+(1/4)^2 ≠ 0 := by positivity
  have ht1 := (((hd_onem β).pow 2).mul_const ((1:ℝ)/4)).div
      (((hd_twom β).pow 2).mul (((hd_twom β).pow 2).add_const ((1/4)^2 : ℝ)))
      (by
        apply mul_ne_zero (pow_ne_zero 2 hne)
        exact hq1d)
  have ht2 := ((((hd_onem β).pow 3).mul_const ((1:ℝ)/4)).mul
        ((((hd_twom β).pow 2).const_mul (5:ℝ)).add_const (3*(1/4)^2 : ℝ))).div
      ((((hd_twom β).pow 4).const_mul (2:ℝ)).mul ((((hd_twom β).pow 2).add_const ((1/4)^2 : ℝ)).pow 2))
      (by
        apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hne))
        exact pow_ne_zero 2 hq1d)
  have hsum := ht1.add ht2
  refine hsum.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfQ1]
  field_simp [hne, hq1d]
  ring

private lemma hasDerivAt_dfQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt dfQ1 (d2fQ1 β) β := by
  unfold dfQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+(1/4)^2 ≠ 0 := by positivity
  have hA : HasDerivAt (fun x : ℝ => 1024*x^7-16128*x^6+96064*x^5-287328*x^4+462400*x^3-381599*x^2+124781*x+1942)
      (7168*β^6-96768*β^5+480320*β^4-1149312*β^3+1387200*β^2-763198*β+124781) β := by
    have h7 := hd_mono 7 (1024:ℝ) β
    have h6 := hd_mono 6 (16128:ℝ) β
    have h5 := hd_mono 5 (96064:ℝ) β
    have h4 := hd_mono 4 (287328:ℝ) β
    have h3 := hd_mono 3 (462400:ℝ) β
    have h2 := hd_mono 2 (381599:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 124781*x) (124781:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (124781:ℝ)
    have h0 := hasDerivAt_const β (1942:ℝ)
    have hs := (((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := (((hd_sub 1 β).const_mul (2:ℝ)).mul hA)
  have hq := (((hd_twom β).pow 5).mul_const (4096:ℝ)).mul
      ((((hd_twom β).pow 2).add_const ((1/4)^2 : ℝ)).pow 3)
  have hd := hn.div hq (by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hne) (by norm_num))
    exact pow_ne_zero 3 hq1d)
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fQ1]
  field_simp [hne, hq1d]
  ring

private lemma hasDerivAt_fB {β : ℝ} (h : β ≠ 2) : HasDerivAt fB (dfB β) β := by
  unfold fB
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq := ((hd_sq_sub 2 β).const_mul (12:ℝ))
  have hd := (hasDerivAt_const β ((1:ℝ)/4)).sub
      ((hasDerivAt_const β (((1:ℝ)/4)^3)).div hq (by
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfB]
  field_simp [hne]
  ring

private lemma hasDerivAt_dfB {β : ℝ} (h : β ≠ 2) : HasDerivAt dfB (d2fB β) β := by
  unfold dfB
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq := ((hd_twom β).pow 3).const_mul (384:ℝ)
  have hd := (hasDerivAt_const β (-(1:ℝ))).div hq (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hne))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fB]
  field_simp [hne]
  ring

private lemma hasDerivAt_fG (β : ℝ) : HasDerivAt fG (dfG β) β := by
  unfold fG dfG
  have hd := ((hd_twom β).const_mul (16:ℝ)).div (hasDerivAt_const β (3:ℝ)) (by norm_num)
  refine hd.congr_deriv ?_
  ring

private lemma hasDerivAt_dfG (β : ℝ) : HasDerivAt dfG 0 β := by
  unfold dfG
  exact hasDerivAt_const β (-(16:ℝ)/3)

private lemma hasDerivAt_fQ2 {β : ℝ} (h : β ≠ 2) : HasDerivAt fQ2 (dfQ2 β) β := by
  unfold fQ2
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq := ((hd_sq_sub 2 β).const_mul (36:ℝ))
  have hd := (hasDerivAt_const β (-5*(1/4)/3)).add
      ((hasDerivAt_const β (((1:ℝ)/4)^3)).div hq (by
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfQ2]
  field_simp [hne]
  ring

private lemma hasDerivAt_dfQ2 {β : ℝ} (h : β ≠ 2) : HasDerivAt dfQ2 (d2fQ2 β) β := by
  unfold dfQ2
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq := ((hd_twom β).pow 3).const_mul (1152:ℝ)
  have hd := (hasDerivAt_const β (1:ℝ)).div hq (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hne))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fQ2]
  field_simp [hne]
  ring

private lemma hbase_pos (β : ℝ) : (0:ℝ) < (2-β)^2+β^2 := by nlinarith [sq_nonneg (β-1)]

private lemma hbase_ne (β : ℝ) : ((2:ℝ)-β)^2+β^2 ≠ 0 := ne_of_gt (hbase_pos β)

private lemma hW_ne (β : ℝ) : (2:ℝ)*((2-β)^2+β^2) ≠ 0 := mul_ne_zero (by norm_num) (hbase_ne β)

private lemma hasDerivAt_fC (β : ℝ) : HasDerivAt fC (dfC β) β := by
  unfold fC
  have hq := (hd_dm β).const_mul (3:ℝ)
  have hd := (hasDerivAt_const β ((1:ℝ)/4)).sub
      ((hasDerivAt_const β (((1:ℝ)/4)^3)).div hq (by
        exact mul_ne_zero (by norm_num) (hW_ne β)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfC]
  field_simp [hW_ne β, hbase_ne β]
  ring

private lemma hasDerivAt_dfC (β : ℝ) : HasDerivAt dfC (d2fC β) β := by
  unfold dfC
  have hq := ((hd_W β).pow 2).const_mul (96:ℝ)
  have hd := (hd_sub 1 β).div hq (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hbase_ne β)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fC]
  field_simp [hW_ne β, hbase_ne β]
  ring

private lemma hasDerivAt_fH (β : ℝ) : HasDerivAt fH (dfH β) β := by
  unfold fH
  have hd := ((hasDerivAt_id β).const_mul (4:ℝ)).add
      ((hd_mono 3 (16:ℝ) β).div ((hd_dm β).const_mul (3:ℝ)) (by
        exact mul_ne_zero (by norm_num) (hW_ne β)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfH]
  field_simp [hW_ne β, hbase_ne β]
  ring

private lemma hasDerivAt_dfH (β : ℝ) : HasDerivAt dfH (d2fH β) β := by
  unfold dfH
  have hn : HasDerivAt (fun x : ℝ => 2*x^4-8*x^3+15*x^2-12*x+6)
      (8*β^3-24*β^2+30*β-12) β := by
    have h4 := hd_mono 4 (2:ℝ) β
    have h3 := hd_mono 3 (8:ℝ) β
    have h2 := hd_mono 2 (15:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 12*x) (12:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (12:ℝ)
    have h0 := hasDerivAt_const β (6:ℝ)
    have hs := ((((h4.sub h3).add h2).sub h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hd := ((hn.const_mul (32:ℝ))).div (((hd_W β).pow 2).const_mul (3:ℝ)) (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hbase_ne β)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fH]
  field_simp [hW_ne β, hbase_ne β]
  ring

private lemma hasDerivAt_fQ3 (β : ℝ) : HasDerivAt fQ3 (dfQ3 β) β := by
  unfold fQ3
  have ha := (((hd_sq β).const_mul (8:ℝ)).mul_const ((1:ℝ)/4)).div
      (hasDerivAt_const β (3:ℝ)) (by norm_num)
  have hb := (hasDerivAt_const β ((1/4)^3/9)).sub ha
  have hd := (hasDerivAt_const β (-(1:ℝ)/4)).add (hb.div (hd_dm β) (hW_ne β))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [dfQ3]
  field_simp [hW_ne β, hbase_ne β]
  ring

private lemma hasDerivAt_dfQ3 (β : ℝ) : HasDerivAt dfQ3 (d2fQ3 β) β := by
  unfold dfQ3
  have hn : HasDerivAt (fun x : ℝ => 384*x^2-769*x+1) (768*β-769) β := by
    have h2 := hd_mono 2 (384:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 769*x) (769:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (769:ℝ)
    have h0 := hasDerivAt_const β (1:ℝ)
    have hs := ((h2.sub h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hd := hn.div (((hd_W β).pow 2).const_mul (288:ℝ)) (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hbase_ne β)))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fQ3]
  field_simp [hW_ne β, hbase_ne β]
  ring


/-! ## Assembly -/

private def Gfun (β : ℝ) : ℝ :=
  (13/5)*(Real.arctan ((1/4)/(3/2-β)) + Real.arctan ((1/4)/(1+β)))
  + ( (2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5))*Real.arctan ((1/4)/(2-β))
      + (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
      + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2) )
  - ( (1/4 - (1/4)^3/(12*(2-β)^2))*Real.log (8*(2-β)+1/(8*(2-β)))
      + (16*(2-β)/3)*Real.arctan ((1/4)/(2*(2-β))) - 5*(1/4)/3 + (1/4)^3/(36*(2-β)^2) )
  - ( (1/4 - (1/4)^3/(3*(2*((2-β)^2+β^2))))*Real.log (8*β+1/(8*β))
      + (4*β+16*β^3/(3*(2*((2-β)^2+β^2))))*Real.arctan ((1/4)/(2*β)) - 1/4
      + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2)) )

private def Dfun (β : ℝ) : ℝ :=
  (13/5)*(dat1 β + dat2 β)
  + (dfA β * at3 β + fA β * dat3 β + dfQ1 β)
  - (dfB β * lg1 β + fB β * dlg1 β + dfG β * at4 β + fG β * dat4 β + dfQ2 β)
  - (dfC β * lg2 β + fC β * dlg2 β + dfH β * at5 β + fH β * dat5 β + dfQ3 β)

private def Efun (β : ℝ) : ℝ :=
  (13/5)*(d2at1 β + d2at2 β)
  + (d2fA β * at3 β + 2*dfA β * dat3 β + fA β * d2at3 β + d2fQ1 β)
  - (d2fB β * lg1 β + 2*dfB β * dlg1 β + fB β * d2lg1 β + 2*dfG β * dat4 β
      + fG β * d2at4 β + d2fQ2 β)
  - (d2fC β * lg2 β + 2*dfC β * dlg2 β + fC β * d2lg2 β + d2fH β * at5 β
      + 2*dfH β * dat5 β + fH β * d2at5 β + d2fQ3 β)

private def P1fun (β : ℝ) : ℝ := (13/5)*(d2at1 β + d2at2 β)
private def AR (β : ℝ) : ℝ := 2*dfA β * dat3 β + fA β * d2at3 β + d2fQ1 β
private def BR (β : ℝ) : ℝ := -(2*dfB β * dlg1 β + fB β * d2lg1 β + 2*dfG β * dat4 β
    + fG β * d2at4 β + d2fQ2 β)
private def CR (β : ℝ) : ℝ := -(2*dfC β * dlg2 β + fC β * d2lg2 β + 2*dfH β * dat5 β
    + fH β * d2at5 β + d2fQ3 β)

private lemma Gfun_eq (β : ℝ) :
    Gfun β = (13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)
      - (fB β * lg1 β + fG β * at4 β + fQ2 β)
      - (fC β * lg2 β + fH β * at5 β + fQ3 β) := by
  unfold Gfun at1 at2 at3 at4 at5 lg1 lg2 fA fQ1 fB fG fQ2 fC fH fQ3
  ring

private lemma Efun_split (β : ℝ) :
    Efun β = P1fun β + (AR β + d2fA β * at3 β) + (BR β - d2fB β * lg1 β)
      + (CR β - d2fC β * lg2 β - d2fH β * at5 β) := by
  unfold Efun P1fun AR BR CR
  ring

private lemma hasDerivAt_Gfun {β : ℝ} (h0 : β ≠ 0) (h2 : β ≠ 2) (h32 : β ≠ 3/2) (hm1 : β ≠ -1) :
    HasDerivAt Gfun (Dfun β) β := by
  have hG : Gfun = fun x : ℝ => (13/5)*(at1 x + at2 x) + (fA x * at3 x + fQ1 x)
      - (fB x * lg1 x + fG x * at4 x + fQ2 x)
      - (fC x * lg2 x + fH x * at5 x + fQ3 x) := funext Gfun_eq
  rw [hG]
  have h1 := ((hasDerivAt_at1 h32).add (hasDerivAt_at2 hm1)).const_mul (13/5)
  have h2' := ((hasDerivAt_fA h2).mul (hasDerivAt_at3 h2)).add (hasDerivAt_fQ1 h2)
  have h3' := (((hasDerivAt_fB h2).mul (hasDerivAt_lg1 h2)).add
    ((hasDerivAt_fG β).mul (hasDerivAt_at4 h2))).add (hasDerivAt_fQ2 h2)
  have h4' := (((hasDerivAt_fC β).mul (hasDerivAt_lg2 h0)).add
    ((hasDerivAt_fH β).mul (hasDerivAt_at5 h0))).add (hasDerivAt_fQ3 β)
  have hall := ((h1.add h2').sub h3').sub h4'
  refine hall.congr_deriv ?_
  unfold Dfun
  ring

private lemma hasDerivAt_Dfun {β : ℝ} (h0 : β ≠ 0) (h2 : β ≠ 2) :
    HasDerivAt Dfun (Efun β) β := by
  unfold Dfun
  have h1 := ((hasDerivAt_dat1 β).add (hasDerivAt_dat2 β)).const_mul (13/5)
  have h2' := (((hasDerivAt_dfA h2).mul (hasDerivAt_at3 h2)).add
    ((hasDerivAt_fA h2).mul (hasDerivAt_dat3 β))).add (hasDerivAt_dfQ1 h2)
  have h3' := ((((hasDerivAt_dfB h2).mul (hasDerivAt_lg1 h2)).add
    ((hasDerivAt_fB h2).mul (hasDerivAt_dlg1 h2))).add
    ((hasDerivAt_dfG β).mul (hasDerivAt_at4 h2))).add
    ((hasDerivAt_fG β).mul (hasDerivAt_dat4 β)) |>.add (hasDerivAt_dfQ2 h2)
  have h4' := ((((hasDerivAt_dfC β).mul (hasDerivAt_lg2 h0)).add
    ((hasDerivAt_fC β).mul (hasDerivAt_dlg2 h0))).add
    ((hasDerivAt_dfH β).mul (hasDerivAt_at5 h0))).add
    ((hasDerivAt_fH β).mul (hasDerivAt_dat5 β)) |>.add (hasDerivAt_dfQ3 β)
  have hall := ((h1.add h2').sub h3').sub h4'
  refine hall.congr_deriv ?_
  unfold Efun
  ring


private lemma h_2sub_ne (β : ℝ) (h2 : β ≤ 1) : (2:ℝ)-β ≠ 0 := by linarith
private lemma h_b_ne (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) : β ≠ 0 := by linarith
private lemma h_1add_ne (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) : (1:ℝ)+β ≠ 0 := by linarith
private lemma h_q_ne (β : ℝ) : (β:ℝ)^2-2*β+2 ≠ 0 := by
  have : (0:ℝ) < β^2-2*β+2 := by nlinarith [sq_nonneg (β-1)]
  exact ne_of_gt this

/-! ## upper/lower certificates -/

private lemma p1_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ P1fun β - 1 := by
  have hden : (0:ℝ) < 65536*β^8 - 131072*β^7 - 278528*β^6 + 532480*β^5 + 585216*β^4 - 816640*β^3 - 709952*β^2 + 462944*β + 395641 := by
    rw [show 65536*β^8 - 131072*β^7 - 278528*β^6 + 532480*β^5 + 585216*β^4 - 816640*β^3 - 709952*β^2 + 462944*β + 395641 = (16*β^2 - 48*β + 37)^2*(16*β^2 + 32*β + 17)^2 by ring]
    apply mul_pos
    · apply pow_pos; nlinarith [sq_nonneg (2*β-3)]
    · apply pow_pos; nlinarith [sq_nonneg (β+1)]
  have hkey : (P1fun β - 1) * (65536*β^8 - 131072*β^7 - 278528*β^6 + 532480*β^5 + 585216*β^4 - 816640*β^3 - 709952*β^2 + 462944*β + 395641) = -65536*β^8 + 131072*β^7 + 278528*β^6 - 532480*β^5 - 1224192*β^4 + 1455616*β^3 + 1109312*β^2 - 742496*β + 204231 := by
    unfold P1fun d2at1 d2at2
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ -65536*β^8 + 131072*β^7 + 278528*β^6 - 532480*β^5 - 1224192*β^4 + 1455616*β^3 + 1109312*β^2 - 742496*β + 204231 := by
    rw [show -65536*β^8 + 131072*β^7 + 278528*β^6 - 532480*β^5 - 1224192*β^4 + 1455616*β^3 + 1109312*β^2 - 742496*β + 204231 = (8998912/27)*(1-β)^4 + (34143712/45)*(β-1/4)^1*(1-β)^2 + (2777817088/3645)*(β-1/4)^1*(1-β)^6 + (3274960/3)*(β-1/4)^2 + (90865856/45)*(β-1/4)^2*(1-β)^1 + (10418520064/10935)*(β-1/4)^2*(1-β)^6 + (785739776/1215)*(β-1/4)^5*(1-β)^1 + (899719168/729)*(β-1/4)^5*(1-β)^2 + (11135156224/10935)*(β-1/4)^5*(1-β)^3 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (P1fun β - 1) * (65536*β^8 - 131072*β^7 - 278528*β^6 + 532480*β^5 + 585216*β^4 - 816640*β^3 - 709952*β^2 + 462944*β + 395641) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma ar_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ AR β + d2fA β * ((1:ℝ)/4/(2-β)) + 1 := by
  have hden : (0:ℝ) < 262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176240128*β^13 + 7657494528*β^12 - 36832428032*β^11 + 135403192576*β^10 - 388072018944*β^9 + 876335281156*β^8 - 1564396470336*β^7 + 2200377303488*β^6 - 2412853036800*β^5 + 2022168105344*β^4 - 1252142095360*β^3 + 540241894400*β^2 - 145107456000*β + 18279040000 := by
    rw [show 262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176240128*β^13 + 7657494528*β^12 - 36832428032*β^11 + 135403192576*β^10 - 388072018944*β^9 + 876335281156*β^8 - 1564396470336*β^7 + 2200377303488*β^6 - 2412853036800*β^5 + 2022168105344*β^4 - 1252142095360*β^3 + 540241894400*β^2 - 145107456000*β + 18279040000 = 4*(β - 2)^8*(16*β^2 - 64*β + 65)^4 by ring]
    have h8 : (0:ℝ) < (β-2)^8 := by
      rw [show (β-2)^8 = (2-β)^8 by ring]; exact pow_pos (by linarith) 8
    have h65 : (0:ℝ) < 16*β^2-64*β+65 := by nlinarith [sq_nonneg (4*β-8)]
    exact mul_pos (mul_pos (by norm_num) h8) (pow_pos h65 4)
  have hkey : (AR β + d2fA β * ((1:ℝ)/4/(2-β)) + 1) * (262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176240128*β^13 + 7657494528*β^12 - 36832428032*β^11 + 135403192576*β^10 - 388072018944*β^9 + 876335281156*β^8 - 1564396470336*β^7 + 2200377303488*β^6 - 2412853036800*β^5 + 2022168105344*β^4 - 1252142095360*β^3 + 540241894400*β^2 - 145107456000*β + 18279040000) = 262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176502272*β^13 + 7664310272*β^12 - 36914249728*β^11 + 135990534400*β^10 - 390838290432*β^9 + 885214209540*β^8 - 1583897600832*β^7 + 2228592846112*β^6 - 2435905722512*β^5 + 2023834599038*β^4 - 1233159351693*β^3 + 518695088708*β^2 - 134332613006*β + 16114984039 := by
    unfold AR dfA dat3 fA d2at3 d2fQ1 d2fA
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ 262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176502272*β^13 + 7664310272*β^12 - 36914249728*β^11 + 135990534400*β^10 - 390838290432*β^9 + 885214209540*β^8 - 1583897600832*β^7 + 2228592846112*β^6 - 2435905722512*β^5 + 2023834599038*β^4 - 1233159351693*β^3 + 518695088708*β^2 - 134332613006*β + 16114984039 := by
    rw [show 262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176502272*β^13 + 7664310272*β^12 - 36914249728*β^11 + 135990534400*β^10 - 390838290432*β^9 + 885214209540*β^8 - 1583897600832*β^7 + 2228592846112*β^6 - 2435905722512*β^5 + 2023834599038*β^4 - 1233159351693*β^3 + 518695088708*β^2 - 134332613006*β + 16114984039 = (37159286752557817/49226751)*(1-β)^5 + (33740105958405087616/1708871499)*(1-β)^9 + (52709657342848256000/322976713311)*(1-β)^11 + (226784486741356947328/11962100493)*(β-1/4)^1*(1-β)^7 + (1403798400701628590/1329122277)*(β-1/4)^2*(1-β)^4 + (1821970239468489211904/968930139933)*(β-1/4)^2*(1-β)^11 + (45783607098480609198080/78483341334573)*(β-1/4)^3*(1-β)^13 + (479834757761187165184/107658904437)*(β-1/4)^4*(1-β)^6 + (812244700520888392/11962100493)*(β-1/4)^6*(1-β)^2 + (173974761323396330946560/78483341334573)*(β-1/4)^6*(1-β)^10 + (12184230198006872960/107658904437)*(β-1/4)^8*(1-β)^2 + (6644561458312668273664/968930139933)*(β-1/4)^8*(1-β)^4 + (210370102051008497582080/78483341334573)*(β-1/4)^9*(1-β)^7 + (2220257712130328821760/968930139933)*(β-1/4)^11*(1-β)^3 + (164852924416/531441)*(β-1/4)^12 + (20970261708800/531441)*(β-1/4)^12*(1-β)^1 + (82199521763123586138112/78483341334573)*(β-1/4)^12*(1-β)^4 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (AR β + d2fA β * ((1:ℝ)/4/(2-β)) + 1) * (262144*β^16 - 8388608*β^15 + 125894656*β^14 - 1176240128*β^13 + 7657494528*β^12 - 36832428032*β^11 + 135403192576*β^10 - 388072018944*β^9 + 876335281156*β^8 - 1564396470336*β^7 + 2200377303488*β^6 - 2412853036800*β^5 + 2022168105344*β^4 - 1252142095360*β^3 + 540241894400*β^2 - 145107456000*β + 18279040000) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma br_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ BR β := by
  have hden : (0:ℝ) < 16384*β^6 - 196608*β^5 + 983296*β^4 - 2623488*β^3 + 3938304*β^2 - 3153920*β + 1052672 := by
    rw [show 16384*β^6 - 196608*β^5 + 983296*β^4 - 2623488*β^3 + 3938304*β^2 - 3153920*β + 1052672 = 256*(β - 2)^4*(64*β^2 - 256*β + 257) by ring]
    have hp : (0:ℝ) < (β-2)^4 := by
      rw [show (β-2)^4 = (2-β)^4 by ring]; exact pow_pos (by linarith) 4
    have hq : (0:ℝ) < 64*β^2-256*β+257 := by nlinarith [sq_nonneg (8*β-16)]
    exact mul_pos (mul_pos (by norm_num) hp) hq
  have hkey : (BR β) * (16384*β^6 - 196608*β^5 + 983296*β^4 - 2623488*β^3 + 3938304*β^2 - 3153920*β + 1052672) = 4096*β^4 - 32768*β^3 + 98176*β^2 - 130560*β + 65025 := by
    unfold BR dfB dlg1 fB d2lg1 dfG dat4 fG d2at4 d2fQ2
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ 4096*β^4 - 32768*β^3 + 98176*β^2 - 130560*β + 65025 := by
    rw [show 4096*β^4 - 32768*β^3 + 98176*β^2 - 130560*β + 65025 = (67600)*(1-β)^2 + (5292)*(β-1/4)^1 + (11664)*(β-1/4)^1*(1-β)^1 + (102400/3)*(β-1/4)^2*(1-β)^2 + (90112/3)*(β-1/4)^3*(1-β)^1 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (BR β) * (16384*β^6 - 196608*β^5 + 983296*β^4 - 2623488*β^3 + 3938304*β^2 - 3153920*β + 1052672) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma cr_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ CR β - d2fH β * ((1:ℝ)/4/(2*β)) - 1/5 := by
  have hden : (0:ℝ) < 737280*β^10 - 4423680*β^9 + 13282560*β^8 - 23662080*β^7 + 26749440*β^6 - 18063360*β^5 + 6312960*β^4 - 276480*β^3 + 92160*β^2 := by
    rw [show 737280*β^10 - 4423680*β^9 + 13282560*β^8 - 23662080*β^7 + 26749440*β^6 - 18063360*β^5 + 6312960*β^4 - 276480*β^3 + 92160*β^2 = 11520*β^2*(64*β^2 + 1)*(β^2 - 2*β + 2)^3 by ring]
    have hb : (0:ℝ) < β := by linarith
    have h4 : (0:ℝ) < β^2-2*β+2 := by nlinarith [sq_nonneg (β-1)]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hb 2)) (by positivity)) (pow_pos h4 3)
  have hkey : (CR β - d2fH β * ((1:ℝ)/4/(2*β)) - 1/5) * (737280*β^10 - 4423680*β^9 + 13282560*β^8 - 23662080*β^7 + 26749440*β^6 - 18063360*β^5 + 6312960*β^4 - 276480*β^3 + 92160*β^2) = -147456*β^10 + 884736*β^9 - 2472192*β^8 + 3626496*β^7 - 2037888*β^6 - 2256768*β^5 + 5296813*β^4 - 4245684*β^3 + 1333588*β^2 + 68880*β - 22980 := by
    unfold CR dfC dlg2 fC d2lg2 dfH dat5 fH d2at5 d2fQ3 d2fH
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ -147456*β^10 + 884736*β^9 - 2472192*β^8 + 3626496*β^7 - 2037888*β^6 - 2256768*β^5 + 5296813*β^4 - 4245684*β^3 + 1333588*β^2 + 68880*β - 22980 := by
    rw [show -147456*β^10 + 884736*β^9 - 2472192*β^8 + 3626496*β^7 - 2037888*β^6 - 2256768*β^5 + 5296813*β^4 - 4245684*β^3 + 1333588*β^2 + 68880*β - 22980 = (5570920973/150012)*(1-β)^3 + (1252529619712/9113229)*(1-β)^8 + (114458251475/112509)*(β-1/4)^1*(1-β)^3 + (26363872643/37503)*(β-1/4)^2*(1-β)^1 + (9596671816/37503)*(β-1/4)^2*(1-β)^2 + (1321575891968/9113229)*(β-1/4)^3*(1-β)^5 + (5224301854720/82019061)*(β-1/4)^3*(1-β)^7 + (112824320/729)*(β-1/4)^6 + (302490601472/1012581)*(β-1/4)^6*(1-β)^1 + (6869900804096/82019061)*(β-1/4)^7*(1-β)^3 + (185050746880/27339687)*(β-1/4)^8*(1-β)^1 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (CR β - d2fH β * ((1:ℝ)/4/(2*β)) - 1/5) * (737280*β^10 - 4423680*β^9 + 13282560*β^8 - 23662080*β^7 + 26749440*β^6 - 18063360*β^5 + 6312960*β^4 - 276480*β^3 + 92160*β^2) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma d2fA_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ -d2fA β := by
  have hden : (0:ℝ) < -β^7 + 14*β^6 - 84*β^5 + 280*β^4 - 560*β^3 + 672*β^2 - 448*β + 128 := by
    rw [show -β^7 + 14*β^6 - 84*β^5 + 280*β^4 - 560*β^3 + 672*β^2 - 448*β + 128 = -(β - 2)^7 by ring]
    have h : (β-2)^7 = -(2-β)^7 := by ring
    have : (β-2)^7 < 0 := by
      rw [h]; exact neg_lt_zero.mpr (pow_pos (by linarith) 7)
    linarith
  have hkey : (-d2fA β) * (-β^7 + 14*β^6 - 84*β^5 + 280*β^4 - 560*β^3 + 672*β^2 - 448*β + 128) = 2*β^4 - 19*β^3 + 108*β^2 - 178*β + 89 := by
    unfold d2fA
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ 2*β^4 - 19*β^3 + 108*β^2 - 178*β + 89 := by
    rw [show 2*β^4 - 19*β^3 + 108*β^2 - 178*β + 89 = (6523/72)*(1-β)^2 + (8/3)*(β-1/4)^1 + (139/18)*(β-1/4)^1*(1-β)^1 + (62/3)*(β-1/4)^2*(1-β)^2 + (56/3)*(β-1/4)^3*(1-β)^1 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (-d2fA β) * (-β^7 + 14*β^6 - 84*β^5 + 280*β^4 - 560*β^3 + 672*β^2 - 448*β + 128) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma d2fH_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ d2fH β := by
  have hden : (0:ℝ) < 3*β^6 - 18*β^5 + 54*β^4 - 96*β^3 + 108*β^2 - 72*β + 24 := by
    rw [show 3*β^6 - 18*β^5 + 54*β^4 - 96*β^3 + 108*β^2 - 72*β + 24 = 3*(β^2 - 2*β + 2)^3 by ring]
    have h4 : (0:ℝ) < β^2-2*β+2 := by nlinarith [sq_nonneg (β-1)]
    exact mul_pos (by norm_num) (pow_pos h4 3)
  have hkey : (d2fH β) * (3*β^6 - 18*β^5 + 54*β^4 - 96*β^3 + 108*β^2 - 72*β + 24) = 16*β^3 - 96*β^2 + 96*β := by
    unfold d2fH
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ 16*β^3 - 96*β^2 + 96*β := by
    rw [show 16*β^3 - 96*β^2 + 96*β = (16) + (4)*(1-β)^2 + (304/3)*(β-1/4)^1*(1-β)^2 + (256/3)*(β-1/4)^2*(1-β)^1 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (d2fH β) * (3*β^6 - 18*β^5 + 54*β^4 - 96*β^3 + 108*β^2 - 72*β + 24) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma d2fC_cert (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (0:ℝ) ≤ 3/1000 - d2fC β := by
  have hden : (0:ℝ) < 48000*β^6 - 288000*β^5 + 864000*β^4 - 1536000*β^3 + 1728000*β^2 - 1152000*β + 384000 := by
    rw [show 48000*β^6 - 288000*β^5 + 864000*β^4 - 1536000*β^3 + 1728000*β^2 - 1152000*β + 384000 = 48000*(β^2 - 2*β + 2)^3 by ring]
    have h4 : (0:ℝ) < β^2-2*β+2 := by nlinarith [sq_nonneg (β-1)]
    exact mul_pos (by norm_num) (pow_pos h4 3)
  have hkey : (3/1000 - d2fC β) * (48000*β^6 - 288000*β^5 + 864000*β^4 - 1536000*β^3 + 1728000*β^2 - 1152000*β + 384000) = 144*β^6 - 864*β^5 + 2592*β^4 - 4608*β^3 + 5559*β^2 - 4206*β + 1402 := by
    unfold d2fC
    field_simp [h_2sub_ne β h2, h_b_ne β h1, h_q_ne β, h_1add_ne β h1]
    ring
  have hnum : (0:ℝ) ≤ 144*β^6 - 864*β^5 + 2592*β^4 - 4608*β^3 + 5559*β^2 - 4206*β + 1402 := by
    rw [show 144*β^6 - 864*β^5 + 2592*β^4 - 4608*β^3 + 5559*β^2 - 4206*β + 1402 = (27487/288)*(1-β)^1 + (5743/9)*(1-β)^2 + (157237/243)*(1-β)^4 + (16970/243)*(β-1/4)^2*(1-β)^2 + (602704/2187)*(β-1/4)^2*(1-β)^4 + (19456/243)*(β-1/4)^5 + (287776/2187)*(β-1/4)^5*(1-β)^1 by ring]
    positivity
  have hmul : (0:ℝ) ≤ (3/1000 - d2fC β) * (48000*β^6 - 288000*β^5 + 864000*β^4 - 1536000*β^3 + 1728000*β^2 - 1152000*β + 384000) := by rw [hkey]; exact hnum
  have h := nonneg_of_mul_nonneg_left hmul hden
  linarith




/-! ## the bounds -/

private lemma at3_le (β : ℝ) (h2 : β ≤ 1) : at3 β ≤ (1/4)/(2-β) := by
  unfold at3
  exact Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
    (div_nonneg (by norm_num) (by linarith))

private lemma at5_le (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) : at5 β ≤ (1/4)/(2*β) := by
  unfold at5
  exact Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
    (div_nonneg (by norm_num) (by linarith))

private lemma lg1_nonneg (β : ℝ) (h2 : β ≤ 1) : 0 ≤ lg1 β := by
  unfold lg1
  apply Real.log_nonneg
  have h : (1:ℝ) ≤ 8*(2-β) := by linarith
  have h2' : 0 < 1/(8*(2-β)) := by positivity
  linarith

private lemma lg2_nonneg (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) : 0 ≤ lg2 β := by
  unfold lg2
  apply Real.log_nonneg
  have h : (2:ℝ) ≤ 8*β := by linarith
  have h2' : 0 < 1/(8*β) := by positivity
  linarith

private lemma lg2_le (β : ℝ) (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : lg2 β ≤ 15/2 := by
  unfold lg2
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8*β+1/(8*β) by positivity)
  have hy : 8*β+1/(8*β) ≤ 17/2 := by
    have hb : 0 < 8*β := by linarith
    have key : 8*β + 1/(8*β) = (64*β^2+1)/(8*β) := by field_simp; ring
    rw [key, div_le_iff₀ hb]
    have hq : (0:ℝ) ≤ (8*β-1)*(1-β) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hq]
  linarith

private lemma d2fB_nonpos (β : ℝ) : d2fB β ≤ 0 := by
  unfold d2fB
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)

private lemma Efun_lower {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : (3:ℝ)/20 ≤ Efun β := by
  have hp1 := p1_cert β h1 h2
  have har := ar_cert β h1 h2
  have hbr := br_cert β h1 h2
  have hcr := cr_cert β h1 h2
  have hdA := d2fA_cert β h1 h2
  have hdH := d2fH_cert β h1 h2
  have hdC := d2fC_cert β h1 h2
  have hdB := d2fB_nonpos β
  have hat3 := at3_le β h2
  have hat5 := at5_le β h1
  have hlg1 := lg1_nonneg β h2
  have hlg2 := lg2_nonneg β h1
  have hlg2b := lg2_le β h1 h2
  have hb1 : d2fA β * ((1:ℝ)/4/(2-β)) ≤ d2fA β * at3 β :=
    mul_le_mul_of_nonpos_left hat3 (by linarith [hdA] : d2fA β ≤ 0)
  have hb2 : BR β ≤ BR β - d2fB β * lg1 β := by
    have hnn : 0 ≤ -(d2fB β) * lg1 β := mul_nonneg (by linarith [hdB]) hlg1
    nlinarith [hnn]
  have hb3 : d2fH β * at5 β ≤ d2fH β * ((1:ℝ)/4/(2*β)) :=
    mul_le_mul_of_nonneg_left hat5 hdH
  have hb4 : -(3:ℝ)/1000 * (15/2) ≤ -(d2fC β) * lg2 β := by
    have h5 : -(3:ℝ)/1000 ≤ -(d2fC β) := by linarith [hdC]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right h5 hlg2)
    nlinarith [hlg2b]
  rw [Efun_split]
  linarith [hp1, har, hbr, hcr, hb1, hb2, hb3, hb4]


private lemma deriv_deriv_Gfun {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    deriv (deriv Gfun) β = Efun β := by
  have hmem : Set.Ioo (1/8:ℝ) (9/8) ∈ 𝓝 β := by
    apply isOpen_Ioo.mem_nhds
    exact ⟨by linarith, by linarith⟩
  have hev : deriv Gfun =ᶠ[𝓝 β] Dfun := by
    filter_upwards [hmem] with x hx
    exact (hasDerivAt_Gfun (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.2]) (by linarith [hx.1])).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_Dfun (by linarith) (by linarith)).deriv

/-- The function `Gform` (closed form of a half-integral) has second derivative bounded below by
`3/20` on `[1/4,1]`. -/
theorem Gform_second_deriv_lower {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    (3:ℝ)/20 ≤ deriv (deriv (fun β : ℝ =>
        (13/5)*(Real.arctan ((1/4)/(3/2-β)) + Real.arctan ((1/4)/(1+β)))
        + ( (2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5))*Real.arctan ((1/4)/(2-β))
            + (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
            + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2) )
        - ( (1/4 - (1/4)^3/(12*(2-β)^2))*Real.log (8*(2-β)+1/(8*(2-β)))
            + (16*(2-β)/3)*Real.arctan ((1/4)/(2*(2-β))) - 5*(1/4)/3 + (1/4)^3/(36*(2-β)^2) )
        - ( (1/4 - (1/4)^3/(3*(2*((2-β)^2+β^2))))*Real.log (8*β+1/(8*β))
            + (4*β+16*β^3/(3*(2*((2-β)^2+β^2))))*Real.arctan ((1/4)/(2*β)) - 1/4
            + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2)) ))) β := by
  change (3:ℝ)/20 ≤ deriv (deriv Gfun) β
  rw [deriv_deriv_Gfun h1 h2]
  exact Efun_lower h1 h2

end
end Commons.Analysis.Integral