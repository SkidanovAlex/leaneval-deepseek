import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Submission.Commons.Analysis.Integral.Gform_second_deriv_lower
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4

namespace Commons.Analysis.Integral

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1600000

/-! ## copy of the (private) first-derivative infrastructure from
`Commons.Analysis.Integral.Gform_second_deriv_lower`, needed here to identify
`deriv Gfun` at `β = 11/20`. -/

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

private lemma hasDerivAt_fG (β : ℝ) : HasDerivAt fG (dfG β) β := by
  unfold fG dfG
  have hd := ((hd_twom β).const_mul (16:ℝ)).div (hasDerivAt_const β (3:ℝ)) (by norm_num)
  refine hd.congr_deriv ?_
  ring
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
private lemma Gfun_eq (β : ℝ) :
    Gfun β = (13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)
      - (fB β * lg1 β + fG β * at4 β + fQ2 β)
      - (fC β * lg2 β + fH β * at5 β + fQ3 β) := by
  unfold Gfun at1 at2 at3 at4 at5 lg1 lg2 fA fQ1 fB fG fQ2 fC fH fQ3
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


/-! ## continuity and convexity of `Gfun` on `[1/4,1]` -/

private lemma continuousOn_Gfun : ContinuousOn Gfun (Set.Icc (1/4:ℝ) 1) := by
  intro x hx
  exact (hasDerivAt_Gfun (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2])
    (by linarith [hx.1])).continuousAt.continuousWithinAt

private lemma differentiableOn_Gfun : DifferentiableOn ℝ Gfun (interior (Set.Icc (1/4:ℝ) 1)) := by
  rw [interior_Icc]
  intro x hx
  exact ((hasDerivAt_Gfun (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2])
    (by linarith [hx.1])).differentiableAt).differentiableWithinAt

private lemma second_deriv_Gfun_nonneg {x : ℝ} (hx : x ∈ Set.Icc (1/4:ℝ) 1) :
    (0:ℝ) ≤ deriv^[2] Gfun x := by
  have h := Gform_second_deriv_lower (β := x) hx.1 hx.2
  change (3:ℝ)/20 ≤ deriv (deriv Gfun) x at h
  have h2 : deriv^[2] Gfun x = deriv (deriv Gfun) x := rfl
  rw [h2]; linarith

private lemma differentiableOn_deriv_Gfun :
    DifferentiableOn ℝ (deriv Gfun) (interior (Set.Icc (1/4:ℝ) 1)) := by
  rw [interior_Icc]
  intro x hx
  have h := Gform_second_deriv_lower (β := x) (le_of_lt hx.1) (le_of_lt hx.2)
  change (3:ℝ)/20 ≤ deriv (deriv Gfun) x at h
  have hne : deriv (deriv Gfun) x ≠ 0 := by linarith
  exact (differentiableAt_of_deriv_ne_zero hne).differentiableWithinAt

private lemma convexOn_Gfun : ConvexOn ℝ (Set.Icc (1/4:ℝ) 1) Gfun := by
  refine convexOn_of_deriv2_nonneg (convex_Icc _ _) continuousOn_Gfun
    differentiableOn_Gfun differentiableOn_deriv_Gfun ?_
  intro x hx
  rw [interior_Icc] at hx
  exact second_deriv_Gfun_nonneg ⟨le_of_lt hx.1, le_of_lt hx.2⟩


/-! ## Numeric bounds at `β = 11/20`

The atom arguments at `β = 11/20` are `5/19, 5/31, 5/29, 5/58, 5/22` for the `arctan`s and
`3389/290, 1961/220` for the logs. -/

private lemma arctan_lower_of (x lo : ℝ)
    (h : lo ≤ x - x^3/3 + x^5/5 - x^7/7 + x^9/9 - x^11/11 + x^13/13 - x^15/15)
    (hx : 0 ≤ x) : lo ≤ Real.arctan x :=
  le_trans h (Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 x hx)

private lemma arctan_upper_of (x hi : ℝ)
    (h : x - x^3/3 + x^5/5 - x^7/7 + x^9/9 ≤ hi) (hx : 0 ≤ x) :
    Real.arctan x ≤ hi :=
  le_trans (Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4 x hx) h

private lemma at1_lo : (257323714/10^9 : ℝ) ≤ Real.arctan ((5:ℝ)/19) :=
  arctan_lower_of _ _ (by norm_num) (by norm_num)
private lemma at1_hi : Real.arctan ((5:ℝ)/19) ≤ (257323752/10^9 : ℝ) :=
  arctan_upper_of _ _ (by norm_num) (by norm_num)
private lemma at2_lo : (159913123/10^9 : ℝ) ≤ Real.arctan ((5:ℝ)/31) :=
  arctan_lower_of _ _ (by norm_num) (by norm_num)
private lemma at2_hi : Real.arctan ((5:ℝ)/31) ≤ (159913124/10^9 : ℝ) :=
  arctan_upper_of _ _ (by norm_num) (by norm_num)
private lemma at3_lo : (170735211/10^9 : ℝ) ≤ Real.arctan ((5:ℝ)/29) :=
  arctan_lower_of _ _ (by norm_num) (by norm_num)
private lemma at3_hi : Real.arctan ((5:ℝ)/29) ≤ (170735212/10^9 : ℝ) :=
  arctan_upper_of _ _ (by norm_num) (by norm_num)
private lemma at4_lo : (85994291/10^9 : ℝ) ≤ Real.arctan ((5:ℝ)/58) :=
  arctan_lower_of _ _ (by norm_num) (by norm_num)
private lemma at4_hi : Real.arctan ((5:ℝ)/58) ≤ (85994292/10^9 : ℝ) :=
  arctan_upper_of _ _ (by norm_num) (by norm_num)
private lemma at5_lo : (223476601/10^9 : ℝ) ≤ Real.arctan ((5:ℝ)/22) :=
  arctan_lower_of _ _ (by norm_num) (by norm_num)
private lemma at5_hi : Real.arctan ((5:ℝ)/22) ≤ (223476609/10^9 : ℝ) :=
  arctan_upper_of _ _ (by norm_num) (by norm_num)

private lemma lg1_lo : (2458409247/10^9 : ℝ) ≤ Real.log ((3389:ℝ)/290) := by
  have h1 : ((3389:ℝ)/290) = 2^2 * 3 * (1 - 91/3480) := by norm_num
  have hlog : Real.log ((3389:ℝ)/290)
      = 2*Real.log 2 + Real.log 3 + Real.log (1 - (91:ℝ)/3480) := by
    rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rw [hlog]
  have h := (abs_le.mp (Real.abs_log_sub_add_sum_range_le (x := (91:ℝ)/3480) (by norm_num) 6)).1
  rw [show ((6:ℕ)+1) = 7 from rfl] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have hkey : (2458409247/10^9 : ℝ) ≤ 2*(0.6931471803) + (1.0986122885)
      - (∑ i ∈ Finset.range 6, ((91:ℝ)/3480)^(i+1)/(i+1)) - |((91:ℝ)/3480)|^7/(1-|((91:ℝ)/3480)|) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma lg1_hi : Real.log ((3389:ℝ)/290) ≤ (2458409250/10^9 : ℝ) := by
  have h1 : ((3389:ℝ)/290) = 2^2 * 3 * (1 - 91/3480) := by norm_num
  have hlog : Real.log ((3389:ℝ)/290)
      = 2*Real.log 2 + Real.log 3 + Real.log (1 - (91:ℝ)/3480) := by
    rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rw [hlog]
  have h := (abs_le.mp (Real.abs_log_sub_add_sum_range_le (x := (91:ℝ)/3480) (by norm_num) 6)).2
  rw [show ((6:ℕ)+1) = 7 from rfl] at h
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have hkey : 2*(0.6931471808) + (1.0986122888)
      - (∑ i ∈ Finset.range 6, ((91:ℝ)/3480)^(i+1)/(i+1)) + |((91:ℝ)/3480)|^7/(1-|((91:ℝ)/3480)|)
      ≤ (2458409250/10^9:ℝ) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma lg2_lo : (1531967649/10^9 : ℝ) ≤ Real.log ((509:ℝ)/110) := by
  have hlog : Real.log ((509:ℝ)/110)
      = 2*Real.log 3 - Real.log 2 - Real.log (1 - (14:ℝ)/509) := by
    rw [show ((509:ℝ)/110) = (3:ℝ)^2/2 * (1 - (14:ℝ)/509)⁻¹ by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show Real.log ((3:ℝ)^2/2) = 2*Real.log 3 - Real.log 2 from by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]
        push_cast; ring,
      Real.log_inv]
    ring
  rw [hlog]
  have h := (abs_le.mp (Real.abs_log_sub_add_sum_range_le (x := (14:ℝ)/509) (by norm_num) 6)).2
  rw [show ((6:ℕ)+1) = 7 from rfl] at h
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have hkey : (1531967649/10^9 : ℝ) ≤ 2*(1.0986122885) - 0.6931471808
      + ((∑ i ∈ Finset.range 6, ((14:ℝ)/509)^(i+1)/(i+1)) - |((14:ℝ)/509)|^7/(1-|((14:ℝ)/509)|)) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma lg2_hi : Real.log ((509:ℝ)/110) ≤ (1531967652/10^9 : ℝ) := by
  have hlog : Real.log ((509:ℝ)/110)
      = 2*Real.log 3 - Real.log 2 - Real.log (1 - (14:ℝ)/509) := by
    rw [show ((509:ℝ)/110) = (3:ℝ)^2/2 * (1 - (14:ℝ)/509)⁻¹ by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show Real.log ((3:ℝ)^2/2) = 2*Real.log 3 - Real.log 2 from by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]
        push_cast; ring,
      Real.log_inv]
    ring
  rw [hlog]
  have h := (abs_le.mp (Real.abs_log_sub_add_sum_range_le (x := (14:ℝ)/509) (by norm_num) 6)).1
  rw [show ((6:ℕ)+1) = 7 from rfl] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_lt_d9
  have hkey : 2*(1.0986122888) - 0.6931471803
      + ((∑ i ∈ Finset.range 6, ((14:ℝ)/509)^(i+1)/(i+1)) + |((14:ℝ)/509)|^7/(1-|((14:ℝ)/509)|))
      ≤ (1531967652/10^9:ℝ) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma Gfun_at_1120_lower : -(2616/10^4 : ℝ) ≤ Gfun (11/20) := by
  rw [Gfun_eq]
  unfold at1 at2 at3 at4 at5 lg1 lg2 fA fQ1 fB fG fQ2 fC fH fQ3
  norm_num
  ring_nf
  linarith [at1_lo, at2_lo, at3_lo, at4_hi, at5_hi, lg1_hi, lg2_hi]

private lemma deriv_Gfun_1120_lower : -(63/10^4 : ℝ) ≤ deriv Gfun (11/20) := by
  have hd : deriv Gfun (11/20) = Dfun (11/20) :=
    (hasDerivAt_Gfun (β := 11/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).deriv
  rw [hd]
  unfold Dfun
  unfold at3 at4 at5 lg1 lg2 dat1 dat2 dat3 dat4 dat5 dlg1 dlg2
  unfold fA dfA dfQ1 fB dfB fG dfG dfQ2 fC dfC fH dfH dfQ3
  norm_num
  ring_nf
  linarith [at3_hi, at4_lo, at5_hi, lg1_lo, lg2_lo]

private lemma deriv_Gfun_1120_upper : deriv Gfun (11/20) ≤ -(60/10^4 : ℝ) := by
  have hd : deriv Gfun (11/20) = Dfun (11/20) :=
    (hasDerivAt_Gfun (β := 11/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).deriv
  rw [hd]
  unfold Dfun
  unfold at3 at4 at5 lg1 lg2 dat1 dat2 dat3 dat4 dat5 dlg1 dlg2
  unfold fA dfA dfQ1 fB dfB fG dfG dfQ2 fC dfC fH dfH dfQ3
  norm_num
  ring_nf
  linarith [at3_lo, at4_hi, at5_lo, lg1_hi, lg2_hi]

/-! ## the target -/

theorem Gform_lower {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    -(53:ℝ)/200 ≤
        (13/5)*(Real.arctan ((1/4)/(3/2-β)) + Real.arctan ((1/4)/(1+β)))
        + ( (2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5))*Real.arctan ((1/4)/(2-β))
            + (1-β)^2*(1/4)/((2-β)^2*((2-β)^2+(1/4)^2))
            + (1-β)^3*(1/4)*(5*(2-β)^2+3*(1/4)^2)/(2*(2-β)^4*((2-β)^2+(1/4)^2)^2) )
        - ( (1/4 - (1/4)^3/(12*(2-β)^2))*Real.log (8*(2-β)+1/(8*(2-β)))
            + (16*(2-β)/3)*Real.arctan ((1/4)/(2*(2-β))) - 5*(1/4)/3 + (1/4)^3/(36*(2-β)^2) )
        - ( (1/4 - (1/4)^3/(3*(2*((2-β)^2+β^2))))*Real.log (8*β+1/(8*β))
            + (4*β+16*β^3/(3*(2*((2-β)^2+β^2))))*Real.arctan ((1/4)/(2*β)) - 1/4
            + ((1/4)^3/9 - 8*β^2*(1/4)/3)/(2*((2-β)^2+β^2)) ) := by
  change -(53:ℝ)/200 ≤ Gfun β
  have hmem : β ∈ Set.Icc (1/4:ℝ) 1 := ⟨h1, h2⟩
  have hβ0mem : (11/20:ℝ) ∈ Set.Icc (1/4:ℝ) 1 := by norm_num
  have hdiff : DifferentiableAt ℝ Gfun (11/20) :=
    (hasDerivAt_Gfun (β := 11/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).differentiableAt
  have hL : -(2616/10^4 : ℝ) ≤ Gfun (11/20) := Gfun_at_1120_lower
  have hdlo : -(63/10^4 : ℝ) ≤ deriv Gfun (11/20) := deriv_Gfun_1120_lower
  have hdhi : deriv Gfun (11/20) ≤ -(60/10^4 : ℝ) := deriv_Gfun_1120_upper
  rcases lt_trichotomy β (11/20) with hlt | heq | hgt
  · have hsl := convexOn_Gfun.slope_le_deriv hmem hβ0mem hlt hdiff
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < 11/20 - β := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    have hd0 : deriv Gfun (11/20) ≤ 0 := by linarith
    have h1' : deriv Gfun (11/20) * (11/20 - β) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hd0 (by linarith)
    linarith [hmul, hL, h1']
  · subst heq
    linarith
  · have hsl := convexOn_Gfun.deriv_le_slope hβ0mem hmem hgt hdiff
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < β - 11/20 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    have ht0 : (0:ℝ) ≤ β - 11/20 := by linarith
    have htT : β - 11/20 ≤ 9/20 := by linarith
    have hg1 : (-(63/10^4:ℝ)) * (β - 11/20) ≤ deriv Gfun (11/20) * (β - 11/20) :=
      mul_le_mul_of_nonneg_right hdlo ht0
    have hg2 : (-(63/10^4:ℝ)) * (9/20) ≤ (-(63/10^4:ℝ)) * (β - 11/20) :=
      mul_le_mul_of_nonpos_left htT (by norm_num)
    linarith [hmul, hL, hg1, hg2]


end

end Commons.Analysis.Integral