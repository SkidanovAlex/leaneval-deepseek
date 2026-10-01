import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_poly_bounds_on_unit
import Submission.Commons.Analysis.Real.WJ_threequarter_lower

namespace Commons.Analysis.Real

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

/-! ## Derivative helpers -/

private lemma hd_sub (c β : ℝ) : HasDerivAt (fun x : ℝ => x - c) 1 β :=
  (hasDerivAt_id β).sub_const c

private lemma hd_csub (c β : ℝ) : HasDerivAt (fun x : ℝ => c - x) (-1) β :=
  HasDerivAt.const_sub c (hasDerivAt_id β)

private lemma hd_twom (β : ℝ) : HasDerivAt (fun x : ℝ => 2-x) (-1) β := hd_csub 2 β
private lemma hd_onem (β : ℝ) : HasDerivAt (fun x : ℝ => 1-x) (-1) β := hd_csub 1 β

private lemma hd_div_const {c : ℝ} {q : ℝ → ℝ} {q' x : ℝ} (hq : HasDerivAt q q' x)
    (h : q x ≠ 0) : HasDerivAt (fun y : ℝ => c/(q y)) (-(c*q')/(q x)^2) x := by
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

/-! ## arctan atoms (t = 1/4) -/

private def at1 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/4)/(3/2-β))
private def dat1 (β : ℝ) : ℝ := ((1:ℝ)/4)/((3/2-β)^2+((1:ℝ)/4)^2)
private def d2at1 (β : ℝ) : ℝ := 2*((1:ℝ)/4)*(3/2-β)/(((3/2-β)^2+((1:ℝ)/4)^2)^2)

private def at2 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/4)/(1+β))
private def dat2 (β : ℝ) : ℝ := -((1:ℝ)/4)/((1+β)^2+((1:ℝ)/4)^2)
private def d2at2 (β : ℝ) : ℝ := 2*((1:ℝ)/4)*(1+β)/(((1+β)^2+((1:ℝ)/4)^2)^2)

private def at3 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/4)/(2-β))
private def dat3 (β : ℝ) : ℝ := ((1:ℝ)/4)/((2-β)^2+((1:ℝ)/4)^2)
private def d2at3 (β : ℝ) : ℝ := 2*((1:ℝ)/4)*(2-β)/(((2-β)^2+((1:ℝ)/4)^2)^2)

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

private lemma hasDerivAt_dat1 (β : ℝ) : HasDerivAt dat1 (d2at1 β) β := by
  unfold dat1
  have hq : HasDerivAt (fun x : ℝ => ((3/2:ℝ)-x)^2+((1:ℝ)/4)^2) (-2*((3/2:ℝ)-β)) β := by
    have h2 := ((hd_csub (3/2) β).pow 2).add_const (((1:ℝ)/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((3/2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((1:ℝ)/4)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at1]
  field_simp
  try ring

private lemma hasDerivAt_dat2 (β : ℝ) : HasDerivAt dat2 (d2at2 β) β := by
  unfold dat2
  have hq : HasDerivAt (fun x : ℝ => ((1:ℝ)+x)^2+((1:ℝ)/4)^2) (2*((1:ℝ)+β)) β := by
    have h2 := (((hasDerivAt_id β).const_add (1:ℝ)).pow 2).add_const (((1:ℝ)/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]
    ring
  have hq0 : ((1:ℝ)+β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := (-((1:ℝ)/4))) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at2]
  field_simp
  try ring

private lemma hasDerivAt_dat3 (β : ℝ) : HasDerivAt dat3 (d2at3 β) β := by
  unfold dat3
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^2+((1:ℝ)/4)^2) (-2*((2:ℝ)-β)) β := by
    have h2 := ((hd_csub (2) β).pow 2).add_const (((1:ℝ)/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((1:ℝ)/4)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at3]
  field_simp
  try ring

/-! ## prefactors -/

private lemma hd_mono (n : ℕ) (c β : ℝ) :
    HasDerivAt (fun x : ℝ => c * x^n) (c * (n:ℝ) * β^(n-1)) β := by
  have h := ((hasDerivAt_id β).pow n).const_mul c
  refine h.congr_deriv ?_
  simp only [id_eq, mul_one]
  ring

private def fA (β : ℝ) : ℝ := 2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5)
private def dfA (β : ℝ) : ℝ := -(2*β^4-18*β^3+81*β^2-136*β+75)/(2*(2-β)^6)
private def d2fA (β : ℝ) : ℝ := -(2*β^4-19*β^3+108*β^2-178*β+89)/(2-β)^7

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

private def fQ1 (β : ℝ) : ℝ := (1-β)^2*((1:ℝ)/4)/((2-β)^2*((2-β)^2+((1:ℝ)/4)^2))
      + (1-β)^3*((1:ℝ)/4)*(5*(2-β)^2+3*((1:ℝ)/4)^2)/(2*(2-β)^4*((2-β)^2+((1:ℝ)/4)^2)^2)

private def dfQ1 (β : ℝ) : ℝ :=
  (β - 1) * (2048*β^7 - 32256*β^6 + 192128*β^5 - 574656*β^4 + 924800*β^3
      - 763198*β^2 + 249562*β + 3884)
    / ((2-β)^5 * 4096 * ((2-β)^2+((1:ℝ)/4)^2)^3)

private def d2fQ1 (β : ℝ) : ℝ := (98304*β^10 - 2064384*β^9 + 17338368*β^8 - 78179328*β^7
    + 207733632*β^6 - 324573440*β^5 + 255169280*β^4 + 2435780*β^3 - 182509100*β^2
    + 139282088*β - 34691896)/((2-β)^6 * 65536 * ((2-β)^2+((1:ℝ)/4)^2)^4)

private lemma hasDerivAt_fQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt fQ1 (dfQ1 β) β := by
  unfold fQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have ht1 := (((hd_onem β).pow 2).mul_const ((1:ℝ)/4)).div
      (((hd_twom β).pow 2).mul (((hd_twom β).pow 2).add_const (((1:ℝ)/4)^2 : ℝ)))
      (by
        apply mul_ne_zero (pow_ne_zero 2 hne)
        exact hq1d)
  have ht2 := ((((hd_onem β).pow 3).mul_const ((1:ℝ)/4)).mul
        ((((hd_twom β).pow 2).const_mul (5:ℝ)).add_const (3*((1:ℝ)/4)^2 : ℝ))).div
      ((((hd_twom β).pow 4).const_mul (2:ℝ)).mul ((((hd_twom β).pow 2).add_const (((1:ℝ)/4)^2 : ℝ)).pow 2))
      (by
        apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hne))
        exact pow_ne_zero 2 hq1d)
  have hsum := ht1.add ht2
  refine hsum.congr_deriv ?_
  rw [dfQ1]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d]
  ring

private lemma hasDerivAt_dfQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt dfQ1 (d2fQ1 β) β := by
  unfold dfQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have hQ : (16:ℝ)*β^2-64*β+65 ≠ 0 := by nlinarith [sq_nonneg (4*β-8)]
  have hA : HasDerivAt (fun x : ℝ => 2048*x^7 - 32256*x^6 + 192128*x^5 - 574656*x^4
        + 924800*x^3 - 763198*x^2 + 249562*x + 3884)
      (14336*β^6 - 193536*β^5 + 960640*β^4 - 2298624*β^3 + 2774400*β^2 - 1526396*β + 249562) β := by
    have h7 := hd_mono 7 (2048:ℝ) β
    have h6 := hd_mono 6 (32256:ℝ) β
    have h5 := hd_mono 5 (192128:ℝ) β
    have h4 := hd_mono 4 (574656:ℝ) β
    have h3 := hd_mono 3 (924800:ℝ) β
    have h2 := hd_mono 2 (763198:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 249562*x) (249562:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (249562:ℝ)
    have h0 := hasDerivAt_const β (3884:ℝ)
    have hs := (((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := ((hd_sub 1 β)).mul hA
  have hq := ((((hd_twom β).pow 5).mul_const (4096:ℝ))).mul ((((hd_twom β).pow 2).add_const (((1:ℝ)/4)^2 : ℝ)).pow 3)
  have hd := hn.div hq (by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hne) (by norm_num))
    exact pow_ne_zero 3 hq1d)
  refine hd.congr_deriv ?_
  rw [d2fQ1]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d, hQ]
  ring_nf

/-! ## log / power atoms -/

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
  have hq : HasDerivAt (fun x : ℝ => x^2) (2*β) β := by
    have h2 := (hasDerivAt_id β).pow 2
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]
    ring
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

private def Kc : ℝ := ((1:ℝ)/4)*(-Real.log ((1:ℝ)/4) + 1)
private def C3 : ℝ := ((1:ℝ)/4)^3/12

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

private def T5 (β : ℝ) : ℝ := ((1:ℝ)/4)*(lg1 β) + Kc + C3*(n2 β)
private def dT5 (β : ℝ) : ℝ := ((1:ℝ)/4)*(dlg1 β) + C3*(2*(n3 β))
private def d2T5 (β : ℝ) : ℝ := ((1:ℝ)/4)*(d2lg1 β) + C3*(2*(3*(n4 β)))
private def T6 (β : ℝ) : ℝ := ((1:ℝ)/4)*(lg2 β) + Kc + C3*(m2 β)
private def dT6 (β : ℝ) : ℝ := ((1:ℝ)/4)*(dlg2 β) + C3*(-2*(m3 β))
private def d2T6 (β : ℝ) : ℝ := ((1:ℝ)/4)*(d2lg2 β) + C3*(-2*(-3*(m4 β)))

private lemma hasDerivAt_T5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt T5 (dT5 β) β := by
  have h1 := (hasDerivAt_lg1 h).const_mul (((1:ℝ)/4))
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_n2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT5] <;> ring

private lemma hasDerivAt_dT5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt dT5 (d2T5 β) β := by
  rw [show dT5 = (fun x : ℝ => ((1:ℝ)/4)*(dlg1 x) + C3*(2*(n3 x))) from rfl]
  have h1 := (hasDerivAt_dlg1 h).const_mul (((1:ℝ)/4))
  have h2 := ((hasDerivAt_n3 h).const_mul (2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T5] <;> ring

private lemma hasDerivAt_T6 {β : ℝ} (h : β ≠ 0) : HasDerivAt T6 (dT6 β) β := by
  have h1 := (hasDerivAt_lg2 h).const_mul (((1:ℝ)/4))
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_m2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT6] <;> ring

private lemma hasDerivAt_dT6 {β : ℝ} (h : β ≠ 0) : HasDerivAt dT6 (d2T6 β) β := by
  rw [show dT6 = (fun x : ℝ => ((1:ℝ)/4)*(dlg2 x) + C3*(-2*(m3 x))) from rfl]
  have h1 := (hasDerivAt_dlg2 h).const_mul (((1:ℝ)/4))
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

/-! ## convexity of `Ef` -/

private def P1f (β : ℝ) : ℝ := (13/5)*(d2at1 β + d2at2 β)
private def ARred (β : ℝ) : ℝ := 2*dfA β * dat3 β + fA β * d2at3 β + d2fQ1 β + d2fA β * ((1:ℝ)/4/(2-β))
private def LGf (β : ℝ) : ℝ := -(d2T5 β + d2T6 β)

private lemma P1f_lower {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : (6:ℝ)/5 ≤ P1f β := by
  have hq1 : ((3/2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have hq2 : ((1:ℝ)+β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < 327680*(((3/2:ℝ)-β)^2+((1:ℝ)/4)^2)^2*(((1:ℝ)+β)^2+((1:ℝ)/4)^2)^2 := by
    positivity
  have hkey : (P1f β - 6/5) * (327680*(((3/2:ℝ)-β)^2+((1:ℝ)/4)^2)^2*(((1:ℝ)+β)^2+((1:ℝ)/4)^2)^2)
      = (4607442944/6561)*(1-β)^8 + (36859543552/6561)*(β-1/4)*(1-β)^7
        + (476447768576/6561)*(β-1/4)^2*(1-β)^6 + (2342653001728/6561)*(β-1/4)^3*(1-β)^5
        + (5351417053184/6561)*(β-1/4)^4*(1-β)^4 + (6476026347520/6561)*(β-1/4)^5*(1-β)^3
        + (4271951052800/6561)*(β-1/4)^6*(1-β)^2 + (1445755617280/6561)*(β-1/4)^7*(1-β)
        + (194291302400/6561)*(β-1/4)^8 := by
    unfold P1f d2at1 d2at2
    field_simp [hq1, hq2]
    ring
  have hnum : (0:ℝ) ≤ (4607442944/6561)*(1-β)^8 + (36859543552/6561)*(β-1/4)*(1-β)^7
        + (476447768576/6561)*(β-1/4)^2*(1-β)^6 + (2342653001728/6561)*(β-1/4)^3*(1-β)^5
        + (5351417053184/6561)*(β-1/4)^4*(1-β)^4 + (6476026347520/6561)*(β-1/4)^5*(1-β)^3
        + (4271951052800/6561)*(β-1/4)^6*(1-β)^2 + (1445755617280/6561)*(β-1/4)^7*(1-β)
        + (194291302400/6561)*(β-1/4)^8 := by
    positivity
  have hmul : (0:ℝ) ≤ (P1f β - 6/5) * (327680*(((3/2:ℝ)-β)^2+((1:ℝ)/4)^2)^2*(((1:ℝ)+β)^2+((1:ℝ)/4)^2)^2) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma ARred_lower {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : -(1:ℝ) ≤ ARred β := by
  have hne : (2:ℝ)-β ≠ 0 := by linarith
  have hB : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < 262144*(2-β)^8*((2-β)^2+((1:ℝ)/4)^2)^4 := by positivity
  have hkey : (ARred β + 1) * (262144*(2-β)^8*((2-β)^2+((1:ℝ)/4)^2)^4)
      = (7166165780499791872/43046721)*(1-β)^16
        + (61333255875897327616/43046721)*(β-1/4)*(1-β)^15
        + (80845408156908519424/14348907)*(β-1/4)^2*(1-β)^14
        + (587019090427910291456/43046721)*(β-1/4)^3*(1-β)^13
        + (971378392875854200832/43046721)*(β-1/4)^4*(1-β)^12
        + (387786472002043248640/14348907)*(β-1/4)^5*(1-β)^11
        + (1042360292192586563584/43046721)*(β-1/4)^6*(1-β)^10
        + (713757327412405731328/43046721)*(β-1/4)^7*(1-β)^9
        + (42183694101520842752/4782969)*(β-1/4)^8*(1-β)^8
        + (159464561780457472000/43046721)*(β-1/4)^9*(1-β)^7
        + (53924381667182510080/43046721)*(β-1/4)^10*(1-β)^6
        + (4977557102437335040/14348907)*(β-1/4)^11*(1-β)^5
        + (3368297145407897600/43046721)*(β-1/4)^12*(1-β)^4
        + (585415434778443776/43046721)*(β-1/4)^13*(1-β)^3
        + (22967126893527040/14348907)*(β-1/4)^14*(1-β)^2
        + (4195099642691584/43046721)*(β-1/4)^15*(1-β)
        + (42202348650496/43046721)*(β-1/4)^16 := by
    unfold ARred dfA dat3 fA d2at3 d2fQ1 d2fA
    field_simp [hne, hB]
    ring
  have hnum : (0:ℝ) ≤ (7166165780499791872/43046721)*(1-β)^16
        + (61333255875897327616/43046721)*(β-1/4)*(1-β)^15
        + (80845408156908519424/14348907)*(β-1/4)^2*(1-β)^14
        + (587019090427910291456/43046721)*(β-1/4)^3*(1-β)^13
        + (971378392875854200832/43046721)*(β-1/4)^4*(1-β)^12
        + (387786472002043248640/14348907)*(β-1/4)^5*(1-β)^11
        + (1042360292192586563584/43046721)*(β-1/4)^6*(1-β)^10
        + (713757327412405731328/43046721)*(β-1/4)^7*(1-β)^9
        + (42183694101520842752/4782969)*(β-1/4)^8*(1-β)^8
        + (159464561780457472000/43046721)*(β-1/4)^9*(1-β)^7
        + (53924381667182510080/43046721)*(β-1/4)^10*(1-β)^6
        + (4977557102437335040/14348907)*(β-1/4)^11*(1-β)^5
        + (3368297145407897600/43046721)*(β-1/4)^12*(1-β)^4
        + (585415434778443776/43046721)*(β-1/4)^13*(1-β)^3
        + (22967126893527040/14348907)*(β-1/4)^14*(1-β)^2
        + (4195099642691584/43046721)*(β-1/4)^15*(1-β)
        + (42202348650496/43046721)*(β-1/4)^16 := by
    positivity
  have hmul : (0:ℝ) ≤ (ARred β + 1) * (262144*(2-β)^8*((2-β)^2+((1:ℝ)/4)^2)^4) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma LGf_lower {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : (2:ℝ)/5 ≤ LGf β := by
  have hb : β ≠ 0 := by linarith
  have hne : (2:ℝ)-β ≠ 0 := by linarith
  have hden : (0:ℝ) < (2-β)^4*β^4 := by positivity
  have hkey : (LGf β - 2/5) * ((2-β)^4*β^4)
      = (2242/3645)*(1-β)^8 + (13696/1215)*(β-1/4)*(1-β)^7
        + (23024/405)*(β-1/4)^2*(1-β)^6 + (89968/729)*(β-1/4)^3*(1-β)^5
        + (54508/405)*(β-1/4)^4*(1-β)^4 + (19712/243)*(β-1/4)^5*(1-β)^3
        + (106624/3645)*(β-1/4)^6*(1-β)^2 + (8192/1215)*(β-1/4)^7*(1-β)
        + (1024/1215)*(β-1/4)^8 := by
    unfold LGf d2T5 d2T6 C3 d2lg1 d2lg2 n4 m4
    field_simp [hb, hne]
    ring
  have hnum : (0:ℝ) ≤ (2242/3645)*(1-β)^8 + (13696/1215)*(β-1/4)*(1-β)^7
        + (23024/405)*(β-1/4)^2*(1-β)^6 + (89968/729)*(β-1/4)^3*(1-β)^5
        + (54508/405)*(β-1/4)^4*(1-β)^4 + (19712/243)*(β-1/4)^5*(1-β)^3
        + (106624/3645)*(β-1/4)^6*(1-β)^2 + (8192/1215)*(β-1/4)^7*(1-β)
        + (1024/1215)*(β-1/4)^8 := by
    positivity
  have hmul : (0:ℝ) ≤ (LGf β - 2/5) * ((2-β)^4*β^4) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

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

private lemma at3_le {β : ℝ} (h : β ≤ 1) : at3 β ≤ (1:ℝ)/4/(2-β) := by
  unfold at3
  apply Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
  apply div_nonneg (by norm_num); linarith

private lemma E2f_nonneg {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : (0:ℝ) ≤ E2f β := by
  have hP1 := P1f_lower h1 h2
  have hAR := ARred_lower h1 h2
  have hLG := LGf_lower h1 h2
  have hsplit : E2f β = P1f β + ARred β + LGf β + d2fA β * (at3 β - (1:ℝ)/4/(2-β)) := by
    unfold E2f P1f ARred LGf; ring
  have hd2 : d2fA β ≤ 0 := d2fA_nonpos h2
  have hat : at3 β - (1:ℝ)/4/(2-β) ≤ 0 := by have := at3_le h2; linarith
  have hprod : 0 ≤ d2fA β * (at3 β - (1:ℝ)/4/(2-β)) := mul_nonneg_of_nonpos_of_nonpos hd2 hat
  rw [hsplit]; linarith

/-! ## convexity plumbing -/

private lemma hasDerivAt_Ef_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (9/8)) : HasDerivAt Ef (Df x) x :=
  hasDerivAt_Ef (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_Df_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (9/8)) : HasDerivAt Df (E2f x) x :=
  hasDerivAt_Df (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma nbd_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/4:ℝ) 1) : Set.Ioo (0:ℝ) (9/8) ∈ 𝓝 x := by
  apply isOpen_Ioo.mem_nhds
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private lemma differentiableOn_Ef : DifferentiableOn ℝ Ef (Set.Icc (1/4:ℝ) 1) := by
  intro x hx
  exact (hasDerivAt_Ef_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt

private lemma differentiableOn_deriv_Ef : DifferentiableOn ℝ (deriv Ef) (Set.Ioo (1/4:ℝ) 1) := by
  intro x hx
  have hev : deriv Ef =ᶠ[𝓝 x] Df := by
    filter_upwards [nbd_Ioo hx] with y hy
    exact (hasDerivAt_Ef_Ioo hy).deriv
  have h1 : DifferentiableAt ℝ (deriv Ef) x := by
    rw [hev.differentiableAt_iff]
    exact (hasDerivAt_Df_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt
  exact h1.differentiableWithinAt

private lemma second_deriv_Ef_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (1/4:ℝ) 1) : 0 ≤ deriv^[2] Ef x := by
  have hev : deriv Ef =ᶠ[𝓝 x] Df := by
    filter_upwards [nbd_Ioo hx] with y hy
    exact (hasDerivAt_Ef_Ioo hy).deriv
  have hdd : deriv (deriv Ef) x = E2f x := by
    rw [hev.deriv_eq]
    exact (hasDerivAt_Df_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).deriv
  change 0 ≤ deriv (deriv Ef) x
  rw [hdd]
  exact E2f_nonneg (le_of_lt hx.1) (le_of_lt hx.2)

private lemma convexOn_Ef : ConvexOn ℝ (Set.Icc (1/4:ℝ) 1) Ef := by
  refine convexOn_of_deriv2_nonneg (convex_Icc _ _) differentiableOn_Ef.continuousOn ?_ ?_ ?_
  · rw [interior_Icc]; exact differentiableOn_Ef.mono Set.Ioo_subset_Icc_self
  · rw [interior_Icc]; exact differentiableOn_deriv_Ef
  · intro x hx
    rw [interior_Icc] at hx
    exact second_deriv_Ef_nonneg hx

private lemma Ef_tangent {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    Ef (5/9) + deriv Ef (5/9) * (β - 5/9) ≤ Ef β := by
  have hmem : β ∈ Set.Icc (1/4:ℝ) 1 := ⟨h1, h2⟩
  have hmem2 : (5/9:ℝ) ∈ Set.Icc (1/4:ℝ) 1 := by norm_num
  have hdiff : DifferentiableAt ℝ Ef (5/9) :=
    (hasDerivAt_Ef_Ioo (by norm_num)).differentiableAt
  rcases lt_trichotomy β (5/9) with hlt | heq | hgt
  · have hsl := convexOn_Ef.slope_le_deriv hmem hmem2 hlt hdiff
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < 5/9 - β := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith
  · subst heq; simp
  · have hsl := convexOn_Ef.deriv_le_slope hmem2 hmem hgt hdiff
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < β - 5/9 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith

/-! ## numeric bounds -/

private lemma log_one_add_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (n : ℕ) :
    Real.log (1+y) ≤ -(∑ i ∈ Finset.range n, (-y)^(i+1)/(i+1)) + y^(n+1)/(1-y) := by
  have h1 : |(-y : ℝ)| < 1 := by rw [abs_neg, abs_of_nonneg hy0]; exact hy1
  have h := Real.abs_log_sub_add_sum_range_le h1 n
  have h2 := (abs_le.mp h).2
  rw [abs_neg, abs_of_nonneg hy0] at h2
  rw [show (1:ℝ) - -y = 1+y by ring] at h2
  linarith

private lemma log_13_9_upper : Real.log ((13:ℝ)/9) ≤ (3678:ℝ)/10000 := by
  have h1 : ((13:ℝ)/9) = 1 + (4:ℝ)/9 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (4:ℝ)/9) (by norm_num) (by norm_num) 12
  have hsum : -(∑ i ∈ Finset.range 12, (-((4:ℝ)/9))^(i+1)/(i+1)) + ((4:ℝ)/9)^(12+1)/(1-(4:ℝ)/9)
      ≤ (3678:ℝ)/10000 := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma log_10_9_upper : Real.log ((10:ℝ)/9) ≤ (105361:ℝ)/1000000 := by
  have h1 : ((10:ℝ)/9) = 1 + (1:ℝ)/9 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (1:ℝ)/9) (by norm_num) (by norm_num) 6
  have hsum : -(∑ i ∈ Finset.range 6, (-((1:ℝ)/9))^(i+1)/(i+1)) + ((1:ℝ)/9)^(6+1)/(1-(1:ℝ)/9)
      ≤ (105361:ℝ)/1000000 := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma log_5_4_upper : Real.log ((5:ℝ)/4) ≤ (2243:ℝ)/10000 := by
  have h1 : ((5:ℝ)/4) = 1 + (1:ℝ)/4 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (1:ℝ)/4) (by norm_num) (by norm_num) 4
  have hsum : -(∑ i ∈ Finset.range 4, (-((1:ℝ)/4))^(i+1)/(i+1)) + ((1:ℝ)/4)^(4+1)/(1-(1:ℝ)/4)
      ≤ (2243:ℝ)/10000 := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma log_26_9_upper : Real.log ((26:ℝ)/9) ≤ (106095:ℝ)/100000 := by
  have hsplit : Real.log ((26:ℝ)/9) = Real.log 2 + Real.log ((13:ℝ)/9) := by
    rw [show (26:ℝ)/9 = 2*((13:ℝ)/9) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hsplit]
  have h2 := Real.log_two_lt_d9
  have h3 := log_13_9_upper
  linarith

private lemma log_15_4_upper : Real.log ((15:ℝ)/4) ≤ (1323:ℝ)/1000 := by
  have hsplit : Real.log ((15:ℝ)/4) = Real.log 3 + Real.log ((5:ℝ)/4) := by
    rw [show (15:ℝ)/4 = 3*((5:ℝ)/4) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hsplit]
  have h3 := Real.log_three_lt_d9
  have h5 := log_5_4_upper
  linarith

private lemma arctan_9_34_lower : (258770:ℝ)/1000000 ≤ Real.arctan (9/34) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((9:ℝ)/34) (by norm_num)
  have hpoly : (258770:ℝ)/1000000 ≤ (9/34) - (9/34)^3/3 + (9/34)^5/5 - (9/34)^7/7
      + (9/34)^9/9 - (9/34)^11/11 + (9/34)^13/13 - (9/34)^15/15 := by norm_num
  linarith

private lemma arctan_9_56_lower : (159351:ℝ)/1000000 ≤ Real.arctan (9/56) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((9:ℝ)/56) (by norm_num)
  have hpoly : (159351:ℝ)/1000000 ≤ (9/56) - (9/56)^3/3 + (9/56)^5/5 - (9/56)^7/7
      + (9/56)^9/9 - (9/56)^11/11 + (9/56)^13/13 - (9/56)^15/15 := by norm_num
  linarith

private lemma arctan_9_52_lower : (171379:ℝ)/1000000 ≤ Real.arctan (9/52) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((9:ℝ)/52) (by norm_num)
  have hpoly : (171379:ℝ)/1000000 ≤ (9/52) - (9/52)^3/3 + (9/52)^5/5 - (9/52)^7/7
      + (9/52)^9/9 - (9/52)^11/11 + (9/52)^13/13 - (9/52)^15/15 := by norm_num
  linarith

private lemma arctan_9_52_upper : Real.arctan (9/52) ≤ (171380:ℝ)/1000000 := by
  have h := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_upper_poly_of_nonneg (x := (9:ℝ)/52) (by norm_num)
  have hpoly : (9/52) - (9/52)^3/3 + (9/52)^5/5 ≤ (171380:ℝ)/1000000 := by norm_num
  linarith

private lemma Ef_59_lower : -(7:ℝ)/25 ≤ Ef (5/9) := by
  have h1 : at1 (5/9) = Real.arctan (9/34) := by unfold at1; norm_num
  have h2 : at2 (5/9) = Real.arctan (9/56) := by unfold at2; norm_num
  have h3 : at3 (5/9) = Real.arctan (9/52) := by unfold at3; norm_num
  have h4 : fA (5/9) = (260600:ℝ)/371293 := by unfold fA; norm_num
  have h5 : fQ1 (5/9) = (3724180416:ℝ)/221525542225 := by unfold fQ1; norm_num
  have h6 : lg1 (5/9) = Real.log (26/9) := by unfold lg1; norm_num
  have h7 : lg2 (5/9) = Real.log (10/9) := by unfold lg2; norm_num
  have h8 : n2 (5/9) = (81:ℝ)/169 := by unfold n2; norm_num
  have h9 : m2 (5/9) = (81:ℝ)/25 := by unfold m2; norm_num
  have hE : Ef (5/9) = ((13/5)*(at1 (5/9)+at2 (5/9)) + (fA (5/9)*at3 (5/9) + fQ1 (5/9)))
      - (T5 (5/9)+T6 (5/9)) := rfl
  rw [hE, h1, h2, h3, h4, h5]
  unfold T5 T6
  rw [h6, h7, h8, h9]
  have hP : (122421:ℝ)/100000 ≤ (13/5)*(Real.arctan ((9:ℝ)/34)+Real.arctan ((9:ℝ)/56))
      + ((260600:ℝ)/371293*Real.arctan ((9:ℝ)/52) + (3724180416:ℝ)/221525542225) := by
    have ha1 := arctan_9_34_lower
    have ha2 := arctan_9_56_lower
    have ha3 := mul_le_mul_of_nonneg_left arctan_9_52_lower (show (0:ℝ) ≤ (260600:ℝ)/371293 by norm_num)
    linarith
  have hKc : Kc ≤ ((1:ℝ)/4)*((1.3862943616:ℝ)+1) := by
    unfold Kc
    have hnn : -Real.log ((1:ℝ)/4) ≤ (1.3862943616:ℝ) := by
      rw [show Real.log ((1:ℝ)/4) = -Real.log 4 by rw [one_div, Real.log_inv]]
      have hlog4 : Real.log 4 ≤ (1.3862943616:ℝ) := by
        rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_two_lt_d9]
      linarith
    nlinarith
  have hT : ((1:ℝ)/4)*Real.log ((26:ℝ)/9) + Kc + C3*((81:ℝ)/169)
      + (((1:ℝ)/4)*Real.log ((10:ℝ)/9) + Kc + C3*((81:ℝ)/25)) ≤ (148958:ℝ)/100000 := by
    unfold C3
    have hl1 := log_26_9_upper
    have hl2 := log_10_9_upper
    nlinarith [hKc, hl1, hl2]
  linarith

private lemma Df_59_abs : |Df (5/9)| ≤ (1:ℝ)/1000 := by
  have h1 : dat1 (5/9) = (324:ℝ)/1237 := by unfold dat1; norm_num
  have h2 : dat2 (5/9) = -(324:ℝ)/3217 := by unfold dat2; norm_num
  have h3 : dat3 (5/9) = (324:ℝ)/2785 := by unfold dat3; norm_num
  have h3e : at3 (5/9) = Real.arctan (9/52) := by unfold at3; norm_num
  have h4 : fA (5/9) = (260600:ℝ)/371293 := by unfold fA; norm_num
  have h5 : dfA (5/9) = -(5725890:ℝ)/4826809 := by unfold dfA; norm_num
  have h6 : dfQ1 (5/9) = -(279769316354496:ℝ)/8020332256256125 := by unfold dfQ1; norm_num
  have h7 : dT5 (5/9) = -(48429:ℝ)/281216 := by unfold dT5 dlg1 n3 C3; norm_num
  have h8 : dT6 (5/9) = (6957:ℝ)/16000 := by unfold dT6 dlg2 m3 C3; norm_num
  have hD : Df (5/9) = ((13/5)*(dat1 (5/9)+dat2 (5/9))
      + ((dfA (5/9)*at3 (5/9) + fA (5/9)*dat3 (5/9)) + dfQ1 (5/9))) - (dT5 (5/9)+dT6 (5/9)) := rfl
  rw [hD, h1, h2, h3, h3e, h4, h5, h6, h7, h8]
  have hb1 : (5725890:ℝ)/4826809 * ((171379:ℝ)/1000000)
      ≤ (5725890:ℝ)/4826809 * Real.arctan (9/52) :=
    mul_le_mul_of_nonneg_left arctan_9_52_lower (by norm_num)
  have hb2 : (5725890:ℝ)/4826809 * Real.arctan (9/52)
      ≤ (5725890:ℝ)/4826809 * ((171380:ℝ)/1000000) :=
    mul_le_mul_of_nonneg_left arctan_9_52_upper (by norm_num)
  rw [abs_le]
  constructor <;> linarith

private lemma deriv_Ef_59 : deriv Ef (5/9) = Df (5/9) :=
  (hasDerivAt_Ef_Ioo (by norm_num)).deriv

private lemma Ef_ge_of_ge_quarter {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) : -(43:ℝ)/150 ≤ Ef β := by
  have htan := Ef_tangent h1 h2
  rw [deriv_Ef_59] at htan
  have hlow := Ef_59_lower
  have habs := Df_59_abs
  have hdist : |β - 5/9| ≤ (4:ℝ)/9 := by
    rw [abs_le]; constructor <;> linarith
  have habs2 : |Df (5/9) * (β - 5/9)| ≤ (1:ℝ)/1000 * ((4:ℝ)/9) := by
    rw [abs_mul]
    exact mul_le_mul habs hdist (abs_nonneg _) (by norm_num)
  have hprod : -((1:ℝ)/1000 * ((4:ℝ)/9)) ≤ Df (5/9) * (β - 5/9) := by
    have := neg_le_of_abs_le habs2; linarith
  linarith

/-! ## region `β ≤ 1/4` -/

private lemma arctan_1_6_lower : (165148:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/6) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((1:ℝ)/6) (by norm_num)
  have hpoly : (165148:ℝ)/1000000 ≤ (1/6) - (1/6)^3/3 + (1/6)^5/5 - (1/6)^7/7
      + (1/6)^9/9 - (1/6)^11/11 + (1/6)^13/13 - (1/6)^15/15 := by norm_num
  linarith

private lemma arctan_2_9_lower : (218668:ℝ)/1000000 ≤ Real.arctan ((2:ℝ)/9) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((2:ℝ)/9) (by norm_num)
  have hpoly : (218668:ℝ)/1000000 ≤ (2/9) - (2/9)^3/3 + (2/9)^5/5 - (2/9)^7/7
      + (2/9)^9/9 - (2/9)^11/11 + (2/9)^13/13 - (2/9)^15/15 := by norm_num
  linarith

private lemma arctan_1_8_lower : (124354:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/8) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((1:ℝ)/8) (by norm_num)
  have hpoly : (124354:ℝ)/1000000 ≤ (1/8) - (1/8)^3/3 + (1/8)^5/5 - (1/8)^7/7
      + (1/8)^9/9 - (1/8)^11/11 + (1/8)^13/13 - (1/8)^15/15 := by norm_num
  linarith

private lemma arctan_2_11_lower : (179853:ℝ)/1000000 ≤ Real.arctan ((2:ℝ)/11) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((2:ℝ)/11) (by norm_num)
  have hpoly : (179853:ℝ)/1000000 ≤ (2/11) - (2/11)^3/3 + (2/11)^5/5 - (2/11)^7/7
      + (2/11)^9/9 - (2/11)^11/11 + (2/11)^13/13 - (2/11)^15/15 := by norm_num
  linarith

private lemma arctan_1_5_lower : (197395:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/5) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((1:ℝ)/5) (by norm_num)
  have hpoly : (197395:ℝ)/1000000 ≤ (1/5) - (1/5)^3/3 + (1/5)^5/5 - (1/5)^7/7
      + (1/5)^9/9 - (1/5)^11/11 + (1/5)^13/13 - (1/5)^15/15 := by norm_num
  linarith

private lemma arctan_2_15_lower : (132551:ℝ)/1000000 ≤ Real.arctan ((2:ℝ)/15) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((2:ℝ)/15) (by norm_num)
  have hpoly : (132551:ℝ)/1000000 ≤ (2/15) - (2/15)^3/3 + (2/15)^5/5 - (2/15)^7/7
      + (2/15)^9/9 - (2/15)^11/11 + (2/15)^13/13 - (2/15)^15/15 := by norm_num
  linarith

private lemma fA_ge_one {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1/4) : 1 ≤ fA β := by
  have hne : (2:ℝ)-β ≠ 0 := by linarith
  have h2b : (0:ℝ) < 2-β := by linarith
  have hden : (0:ℝ) < 2*(2-β)^5 := by positivity
  have hkey : (fA β - 1) * (2*(2-β)^5)
      = 11264*((1:ℝ)/4-β)^5 + 39680*β*((1:ℝ)/4-β)^4 + 52416*β^2*((1:ℝ)/4-β)^3
        + 30800*β^3*((1:ℝ)/4-β)^2 + 6824*β^4*((1:ℝ)/4-β) + 22*β^5 := by
    unfold fA
    field_simp [hne]
    ring
  have hnum : (0:ℝ) ≤ 11264*((1:ℝ)/4-β)^5 + 39680*β*((1:ℝ)/4-β)^4 + 52416*β^2*((1:ℝ)/4-β)^3
        + 30800*β^3*((1:ℝ)/4-β)^2 + 6824*β^4*((1:ℝ)/4-β) + 22*β^5 := by
    positivity
  have hmul : (0:ℝ) ≤ (fA β - 1) * (2*(2-β)^5) := by rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

/-- Rewriting the positive part into the `fA`/`fQ1` normal form. -/
private lemma pos_eq_aux (β u1 u2 u3 : ℝ) (h2b : (2:ℝ)-β ≠ 0)
    (hq : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0) :
      ( (13/5)*(u1 + u2)
        + ((2-β)^2-β^2)/(2*(2-β)) * u3
        + ((2-β)^2-β^2)^2/8 * ((u3 + (2-β)*((1:ℝ)/4)/((2-β)^2+((1:ℝ)/4)^2))/(2*(2-β)^3))
        + ((2-β)^2-β^2)^3/16 * (3*u3/(8*(2-β)^5)
            + ((1:ℝ)/4)*(5*(2-β)^2+3*((1:ℝ)/4)^2)/(8*(2-β)^4*((2-β)^2+((1:ℝ)/4)^2)^2)) )
      = (13/5)*(u1 + u2) + fA β * u3 + fQ1 β := by
  unfold fA fQ1
  field_simp [h2b, hq]
  ring

/-- `Ef` agrees with the explicit expression (for `1/4 ≤ β`). -/
private lemma Ef_eq_pos {β : ℝ} (h1 : (1:ℝ)/4 ≤ β) (h2 : β ≤ 1) :
    Ef β =
      ( (13/5)*(Real.arctan ((1:ℝ)/4/(3/2-β)) + Real.arctan ((1:ℝ)/4/(1+β)))
        + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan ((1:ℝ)/4/(2-β))
        + ((2-β)^2-β^2)^2/8 * ((Real.arctan ((1:ℝ)/4/(2-β)) + (2-β)*((1:ℝ)/4)/((2-β)^2+((1:ℝ)/4)^2))/(2*(2-β)^3))
        + ((2-β)^2-β^2)^3/16 * (3*Real.arctan ((1:ℝ)/4/(2-β))/(8*(2-β)^5)
            + ((1:ℝ)/4)*(5*(2-β)^2+3*((1:ℝ)/4)^2)/(8*(2-β)^4*((2-β)^2+((1:ℝ)/4)^2)^2)) )
      - ((1:ℝ)/4*(Real.log (2*(2-β)) - Real.log ((1:ℝ)/4) + 1) + ((1:ℝ)/4)^3/(12*(2-β)^2))
      - ((1:ℝ)/4*(Real.log (2*β) - Real.log ((1:ℝ)/4) + 1) + ((1:ℝ)/4)^3/(12*β^2)) := by
  unfold Ef T5 T6 lg1 lg2 n2 m2 Kc C3 at1 at2 at3 fA fQ1
  have hb0 : β ≠ 0 := by linarith
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have h32 : (3:ℝ)/2-β ≠ 0 := by linarith
  have hm1 : (1:ℝ)+β ≠ 0 := by linarith
  have hq : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by positivity
  generalize hu1 : Real.arctan (1/4/(3/2-β)) = u1
  generalize hu2 : Real.arctan (1/4/(1+β)) = u2
  generalize hu3 : Real.arctan (1/4/(2-β)) = u3
  generalize hl1 : Real.log (2*(2-β)) = l1
  generalize hl2 : Real.log (2*β) = l2
  generalize hl4 : Real.log (1/4) = l4
  field_simp [hb0, h2b, h32, hm1, hq]
  ring

private lemma W_quarter_else_lower {β : ℝ} (hβ0 : 0 < β) (hβlt : β < 1/4) :
    -(43:ℝ)/150 ≤
      ( (13/5)*(Real.arctan ((1:ℝ)/4/(3/2-β)) + Real.arctan ((1:ℝ)/4/(1+β)))
        + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan ((1:ℝ)/4/(2-β))
        + ((2-β)^2-β^2)^2/8 * ((Real.arctan ((1:ℝ)/4/(2-β)) + (2-β)*((1:ℝ)/4)/((2-β)^2+((1:ℝ)/4)^2))/(2*(2-β)^3))
        + ((2-β)^2-β^2)^3/16 * (3*Real.arctan ((1:ℝ)/4/(2-β))/(8*(2-β)^5)
            + ((1:ℝ)/4)*(5*(2-β)^2+3*((1:ℝ)/4)^2)/(8*(2-β)^4*((2-β)^2+((1:ℝ)/4)^2)^2)) )
      - ((1:ℝ)/4*(Real.log (2*(2-β)) - Real.log ((1:ℝ)/4) + 1) + ((1:ℝ)/4)^3/(12*(2-β)^2))
      - (β*(Real.log 2 + 13/12) + β*Real.log (((1:ℝ)/4)/β)) := by
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have hq : ((2:ℝ)-β)^2+((1:ℝ)/4)^2 ≠ 0 := by nlinarith [sq_nonneg ((2:ℝ)-β)]
  rw [pos_eq_aux β (Real.arctan ((1:ℝ)/4/(3/2-β))) (Real.arctan ((1:ℝ)/4/(1+β)))
      (Real.arctan ((1:ℝ)/4/(2-β))) h2b hq]
  have hlog4 : Real.log 4 ≤ (1.3862943616:ℝ) := by
    rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  have hL42 : -Real.log ((1:ℝ)/4) ≤ (1.3862943616:ℝ) := by
    rw [show Real.log ((1:ℝ)/4) = -Real.log 4 by rw [one_div, Real.log_inv]]
    linarith
  have hL4 : β*Real.log (((1:ℝ)/4)/β) ≤ (1:ℝ)/4 - β := by
    have h1 : Real.log (((1:ℝ)/4)/β) ≤ ((1:ℝ)/4)/β - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hβ0)
    have h3 : β*(((1:ℝ)/4)/β - 1) = (1:ℝ)/4 - β := by field_simp
    linarith [h2, h3]
  have hFA : (1:ℝ) ≤ fA β := fA_ge_one (le_of_lt hβ0) (by linarith)
  have hFQ : (0:ℝ) ≤ fQ1 β := by
    have h1b : (0:ℝ) ≤ 1-β := by linarith
    have h2b' : (0:ℝ) < 2-β := by linarith
    unfold fQ1
    apply add_nonneg
    · apply div_nonneg
      · positivity
      · positivity
    · apply div_nonneg
      · positivity
      · positivity
  rcases lt_or_ge β (1/8) with hlt8 | hge8
  · -- case β ≤ 1/8
    have hA1 : (165148:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/4/(3/2-β)) := by
      have hx : (1:ℝ)/6 ≤ (1:ℝ)/4/(3/2-β) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 3/2-β)]; linarith
      exact le_trans arctan_1_6_lower (Real.arctan_mono hx)
    have hA2 : (218668:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/4/(1+β)) := by
      have hx : (2:ℝ)/9 ≤ (1:ℝ)/4/(1+β) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 1+β)]; linarith
      exact le_trans arctan_2_9_lower (Real.arctan_mono hx)
    have hA3 : (124354:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/4/(2-β)) := by
      have hx : (1:ℝ)/8 ≤ (1:ℝ)/4/(2-β) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 2-β)]; linarith
      exact le_trans arctan_1_8_lower (Real.arctan_mono hx)
    have hA3' : (1:ℝ) * ((124354:ℝ)/1000000) ≤ fA β * Real.arctan ((1:ℝ)/4/(2-β)) :=
      mul_le_mul hFA hA3 (by norm_num) (by linarith)
    have hP : (1122275:ℝ)/1000000 ≤ (13/5)*(Real.arctan ((1:ℝ)/4/(3/2-β))
        + Real.arctan ((1:ℝ)/4/(1+β))) + fA β * Real.arctan ((1:ℝ)/4/(2-β)) + fQ1 β := by
      linarith
    have hL1 : Real.log (2*(2-β)) ≤ (1.3862943616:ℝ) := by
      have h : Real.log (2*(2-β)) ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
      linarith [h, hlog4]
    have hL3 : ((1:ℝ)/4)^3/(12*(2-β)^2) ≤ (1:ℝ)/2700 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hLbeta : β*(Real.log 2 + 13/12) ≤ β*((0.6931471808:ℝ) + 13/12) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.log_two_lt_d9]) (le_of_lt hβ0)
    have hQ : ((1:ℝ)/4*(Real.log (2*(2-β)) - Real.log ((1:ℝ)/4) + 1) + ((1:ℝ)/4)^3/(12*(2-β)^2))
        + (β*(Real.log 2 + 13/12) + β*Real.log (((1:ℝ)/4)/β))
        ≤ (1:ℝ)/4*((1.3862943616:ℝ) + (1.3862943616:ℝ) + 1) + (1:ℝ)/2700
          + β*((0.6931471808:ℝ) + 13/12) + ((1:ℝ)/4 - β) := by
      linarith [hL1, hL42, hL3, hL4, hLbeta]
    linarith [hP, hQ, hlt8.le]
  · -- case 1/8 < β
    have hA1 : (179853:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/4/(3/2-β)) := by
      have hx : (2:ℝ)/11 ≤ (1:ℝ)/4/(3/2-β) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 3/2-β)]; linarith
      exact le_trans arctan_2_11_lower (Real.arctan_mono hx)
    have hA2 : (197395:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/4/(1+β)) := by
      have hx : (1:ℝ)/5 ≤ (1:ℝ)/4/(1+β) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 1+β)]; linarith
      exact le_trans arctan_1_5_lower (Real.arctan_mono hx)
    have hA3 : (132551:ℝ)/1000000 ≤ Real.arctan ((1:ℝ)/4/(2-β)) := by
      have hx : (2:ℝ)/15 ≤ (1:ℝ)/4/(2-β) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 2-β)]; linarith
      exact le_trans arctan_2_15_lower (Real.arctan_mono hx)
    have hA3' : (1:ℝ) * ((132551:ℝ)/1000000) ≤ fA β * Real.arctan ((1:ℝ)/4/(2-β)) :=
      mul_le_mul hFA hA3 (by norm_num) (by linarith)
    have hP : (1113395:ℝ)/1000000 ≤ (13/5)*(Real.arctan ((1:ℝ)/4/(3/2-β))
        + Real.arctan ((1:ℝ)/4/(1+β))) + fA β * Real.arctan ((1:ℝ)/4/(2-β)) + fQ1 β := by
      linarith
    have hL1 : Real.log (2*(2-β)) ≤ (1.323:ℝ) := by
      have h : Real.log (2*(2-β)) ≤ Real.log ((15:ℝ)/4) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith [h, log_15_4_upper]
    have hL3 : ((1:ℝ)/4)^3/(12*(2-β)^2) ≤ (1:ℝ)/2352 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hLbeta : β*(Real.log 2 + 13/12) ≤ β*((0.6931471808:ℝ) + 13/12) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.log_two_lt_d9]) (le_of_lt hβ0)
    have hQ : ((1:ℝ)/4*(Real.log (2*(2-β)) - Real.log ((1:ℝ)/4) + 1) + ((1:ℝ)/4)^3/(12*(2-β)^2))
        + (β*(Real.log 2 + 13/12) + β*Real.log (((1:ℝ)/4)/β))
        ≤ (1:ℝ)/4*((1.323:ℝ) + (1.3862943616:ℝ) + 1) + (1:ℝ)/2352
          + β*((0.6931471808:ℝ) + 13/12) + ((1:ℝ)/4 - β) := by
      linarith [hL1, hL42, hL3, hL4, hLbeta]
    linarith [hP, hQ, hβlt.le]

/-- Single-`t` lower bound at `t = 1/4`: `W (1/4) ≥ -43/150`. -/
lemma WJ_quarter_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (let W : ℝ → ℝ := fun t : ℝ => (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β)) + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*(t)/((2-β)^2+(t)^2))/(2*(2-β)^3)) + ((2-β)^2-β^2)^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5) + (t)*(5*(2-β)^2+3*(t)^2)/(8*(2-β)^4*((2-β)^2+(t)^2)^2)) - ((t)*(Real.log (2*(2-β)) - Real.log (t) + 1) + (t)^3/(12*(2-β)^2)) - (if (t) ≤ β then (t)*(Real.log (2*β) - Real.log (t) + 1) + (t)^3/(12*β^2) else β*(Real.log 2 + 13/12) + β*Real.log ((t)/β));
    -(43:ℝ)/150 ≤ W (1/4)) := by
  simp only []
  by_cases h : (1:ℝ)/4 ≤ β
  · rw [if_pos h]
    rw [← Ef_eq_pos h (le_of_lt hβ1)]
    exact Ef_ge_of_ge_quarter h (le_of_lt hβ1)
  · rw [if_neg h]
    exact W_quarter_else_lower hβ0 (not_le.mp h)

theorem WJ_pair_quarter_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (let W : ℝ → ℝ := fun t : ℝ => (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β)) + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*(t)/((2-β)^2+(t)^2))/(2*(2-β)^3)) + ((2-β)^2-β^2)^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5) + (t)*(5*(2-β)^2+3*(t)^2)/(8*(2-β)^4*((2-β)^2+(t)^2)^2)) - ((t)*(Real.log (2*(2-β)) - Real.log (t) + 1) + (t)^3/(12*(2-β)^2)) - (if (t) ≤ β then (t)*(Real.log (2*β) - Real.log (t) + 1) + (t)^3/(12*β^2) else β*(Real.log 2 + 13/12) + β*Real.log ((t)/β));
    (1:ℝ)/30 ≤ W (1/4) + W (3/4)) := by
  have h1 : -(43:ℝ)/150 ≤
      (let W : ℝ → ℝ := fun t : ℝ => (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β)) + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*(t)/((2-β)^2+(t)^2))/(2*(2-β)^3)) + ((2-β)^2-β^2)^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5) + (t)*(5*(2-β)^2+3*(t)^2)/(8*(2-β)^4*((2-β)^2+(t)^2)^2)) - ((t)*(Real.log (2*(2-β)) - Real.log (t) + 1) + (t)^3/(12*(2-β)^2)) - (if (t) ≤ β then (t)*(Real.log (2*β) - Real.log (t) + 1) + (t)^3/(12*β^2) else β*(Real.log 2 + 13/12) + β*Real.log ((t)/β));
      W (1/4)) := WJ_quarter_lower hβ0 hβ1
  have h3 : (8:ℝ)/25 ≤
      (let W : ℝ → ℝ := fun t : ℝ => (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β)) + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*(t)/((2-β)^2+(t)^2))/(2*(2-β)^3)) + ((2-β)^2-β^2)^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5) + (t)*(5*(2-β)^2+3*(t)^2)/(8*(2-β)^4*((2-β)^2+(t)^2)^2)) - ((t)*(Real.log (2*(2-β)) - Real.log (t) + 1) + (t)^3/(12*(2-β)^2)) - (if (t) ≤ β then (t)*(Real.log (2*β) - Real.log (t) + 1) + (t)^3/(12*β^2) else β*(Real.log 2 + 13/12) + β*Real.log ((t)/β));
      W (3/4)) := by
    simp only []
    exact Commons.Analysis.Real.WJ_threequarter_lower hβ0 hβ1
  simp only [] at h1 ⊢
  linarith
