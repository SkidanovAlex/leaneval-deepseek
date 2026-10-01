import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
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
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-! ## Derivative helpers -/

private lemma hd_csub (c β : ℝ) : HasDerivAt (fun x : ℝ => c - x) (-1) β :=
  HasDerivAt.const_sub c (hasDerivAt_id β)

private lemma hd_sub (c β : ℝ) : HasDerivAt (fun x : ℝ => x - c) 1 β :=
  (hasDerivAt_id β).sub_const c

private lemma hd_twom (β : ℝ) : HasDerivAt (fun x : ℝ => 2-x) (-1) β := hd_csub 2 β
private lemma hd_onem (β : ℝ) : HasDerivAt (fun x : ℝ => 1-x) (-1) β := hd_csub 1 β

private lemma hd_sq (β : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*β) β := by
  have h := (hasDerivAt_id β).pow 2
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

/-- Derivative of `log (c/x)` for `c ≠ 0`, `x ≠ 0`. -/
private lemma hd_log_div {c : ℝ} {β : ℝ} (hc : c ≠ 0) (hβ : β ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (c/x)) (-(1/β)) β := by
  have hd : HasDerivAt (fun x : ℝ => c/x) (-(c/β^2)) β := by
    have h2 := hd_div_const (c := c) (hasDerivAt_id β) hβ
    refine h2.congr_deriv ?_
    simp only [id_eq]
    ring
  have hpos : c/β ≠ 0 := div_ne_zero hc hβ
  have h3 := (Real.hasDerivAt_log hpos).comp β hd
  refine h3.congr_deriv ?_
  field_simp
  try ring


/-! ## arctan atoms -/

private def at1 (β : ℝ) : ℝ := Real.arctan (((3:ℝ)/4)/(3/2-β))
private def dat1 (β : ℝ) : ℝ := ((3:ℝ)/4)/((3/2-β)^2+((3:ℝ)/4)^2)
private def d2at1 (β : ℝ) : ℝ := 2*((3:ℝ)/4)*(3/2-β)/(((3/2-β)^2+((3:ℝ)/4)^2)^2)

private def at2 (β : ℝ) : ℝ := Real.arctan (((3:ℝ)/4)/(1+β))
private def dat2 (β : ℝ) : ℝ := -(((3:ℝ)/4))/((1+β)^2+((3:ℝ)/4)^2)
private def d2at2 (β : ℝ) : ℝ := 2*((3:ℝ)/4)*(1+β)/(((1+β)^2+((3:ℝ)/4)^2)^2)

private def at3 (β : ℝ) : ℝ := Real.arctan (((3:ℝ)/4)/(2-β))
private def dat3 (β : ℝ) : ℝ := ((3:ℝ)/4)/((2-β)^2+((3:ℝ)/4)^2)
private def d2at3 (β : ℝ) : ℝ := 2*((3:ℝ)/4)*(2-β)/(((2-β)^2+((3:ℝ)/4)^2)^2)

private lemma hasDerivAt_at1 {β : ℝ} (h : β ≠ 3/2) : HasDerivAt at1 (dat1 β) β :=
  hd_arctan_csub (a := (3:ℝ)/2) (k := (3:ℝ)/4) (β := β) (by
    intro hc; exact h (by linarith [hc]))

private lemma hasDerivAt_at2 {β : ℝ} (h : β ≠ -1) : HasDerivAt at2 (dat2 β) β := by
  have hh := hd_arctan_add (a := (1:ℝ)) (k := (3:ℝ)/4) (β := β) (by
    intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat2]; try ring

private lemma hasDerivAt_at3 {β : ℝ} (h : β ≠ 2) : HasDerivAt at3 (dat3 β) β :=
  hd_arctan_csub (a := (2:ℝ)) (k := (3:ℝ)/4) (β := β) (by
    intro hc; exact h (by linarith [hc]))

private lemma hasDerivAt_dat1 (β : ℝ) : HasDerivAt dat1 (d2at1 β) β := by
  unfold dat1
  have hq : HasDerivAt (fun x : ℝ => ((3/2:ℝ)-x)^2+(((3:ℝ)/4)^2)) (-2*((3/2:ℝ)-β)) β := by
    have h2 := ((hd_csub (3/2) β).pow 2).add_const (((3:ℝ)/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((3/2:ℝ)-β)^2+(((3:ℝ)/4)^2) ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((3:ℝ)/4)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at1]
  field_simp
  try ring

private lemma hasDerivAt_dat2 (β : ℝ) : HasDerivAt dat2 (d2at2 β) β := by
  unfold dat2
  have hq : HasDerivAt (fun x : ℝ => ((1:ℝ)+x)^2+(((3:ℝ)/4)^2)) (2*((1:ℝ)+β)) β := by
    have h2 := (((hasDerivAt_id β).const_add (1:ℝ)).pow 2).add_const (((3:ℝ)/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]
    ring
  have hq0 : ((1:ℝ)+β)^2+(((3:ℝ)/4)^2) ≠ 0 := by positivity
  have h3 := hd_div_const (c := (-((3:ℝ)/4))) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at2]
  field_simp
  try ring

private lemma hasDerivAt_dat3 (β : ℝ) : HasDerivAt dat3 (d2at3 β) β := by
  unfold dat3
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^2+(((3:ℝ)/4)^2)) (-2*((2:ℝ)-β)) β := by
    have h2 := ((hd_csub (2) β).pow 2).add_const (((3:ℝ)/4)^2 : ℝ)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hq0 : ((2:ℝ)-β)^2+(((3:ℝ)/4)^2) ≠ 0 := by positivity
  have h3 := hd_div_const (c := ((3:ℝ)/4)) hq hq0
  refine h3.congr_deriv ?_
  rw [d2at3]
  field_simp
  try ring

/-! ## prefactors -/

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

private def fQ1 (β : ℝ) : ℝ :=
  (1-β)^2*((3:ℝ)/4)/((2-β)^2*((2-β)^2+((3:ℝ)/4)^2))
    + (1-β)^3*((3:ℝ)/4)*(5*(2-β)^2+3*((3:ℝ)/4)^2)/(2*(2-β)^4*((2-β)^2+((3:ℝ)/4)^2)^2)

private def dfQ1 (β : ℝ) : ℝ :=
  (6*(β-1)*(1024*β^7 - 16128*β^6 + 96576*β^5 - 292192*β^4 + 475200*β^3 - 386895*β^2 + 105853*β + 19062))
    / ((2-β)^5*4096*((2-β)^2+((3:ℝ)/4)^2)^3)

private def d2fQ1 (β : ℝ) : ℝ :=
  (12*(24576*β^10 - 516096*β^9 + 4342784*β^8 - 19632896*β^7 + 51998432*β^6 - 78830144*β^5
      + 51790016*β^4 + 28058761*β^3 - 78600019*β^2 + 54870298*β - 13474462))
    / ((2-β)^6*65536*((2-β)^2+((3:ℝ)/4)^2)^4)

private lemma hasDerivAt_fQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt fQ1 (dfQ1 β) β := by
  unfold fQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((3:ℝ)/4)^2 ≠ 0 := by positivity
  have ht1 := (((hd_onem β).pow 2).mul_const ((3:ℝ)/4)).div
      (((hd_twom β).pow 2).mul (((hd_twom β).pow 2).add_const (((3:ℝ)/4)^2 : ℝ)))
      (by
        apply mul_ne_zero (pow_ne_zero 2 hne)
        exact hq1d)
  have ht2 := ((((hd_onem β).pow 3).mul_const ((3:ℝ)/4)).mul
        ((((hd_twom β).pow 2).const_mul (5:ℝ)).add_const (3*((3:ℝ)/4)^2 : ℝ))).div
      ((((hd_twom β).pow 4).const_mul (2:ℝ)).mul ((((hd_twom β).pow 2).add_const (((3:ℝ)/4)^2 : ℝ)).pow 2))
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
  have hq1d : ((2:ℝ)-β)^2+((3:ℝ)/4)^2 ≠ 0 := by positivity
  have hA : HasDerivAt (fun x : ℝ => 1024*x^7 - 16128*x^6 + 96576*x^5 - 292192*x^4 + 475200*x^3 - 386895*x^2 + 105853*x + 19062)
      (7168*β^6 - 96768*β^5 + 482880*β^4 - 1168768*β^3 + 1425600*β^2 - 773790*β + 105853) β := by
    have h7 := hd_mono 7 (1024:ℝ) β
    have h6 := hd_mono 6 (16128:ℝ) β
    have h5 := hd_mono 5 (96576:ℝ) β
    have h4 := hd_mono 4 (292192:ℝ) β
    have h3 := hd_mono 3 (475200:ℝ) β
    have h2 := hd_mono 2 (386895:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 105853*x) (105853:ℝ) β := by simpa using (hasDerivAt_id β).const_mul (105853:ℝ)
    have h0 := hasDerivAt_const β (19062:ℝ)
    have hs := (((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := ((hd_sub 1 β).const_mul (6:ℝ)).mul hA
  have hq := (((hd_twom β).pow 5).mul_const (4096:ℝ)).mul
      ((((hd_twom β).pow 2).add_const (((3:ℝ)/4)^2 : ℝ)).pow 3)
  have hd := hn.div hq (by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hne) (by norm_num))
    exact pow_ne_zero 3 hq1d)
  refine hd.congr_deriv ?_
  rw [d2fQ1]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d]
  ring_nf


/-! ## log / power atoms -/

private def Kc : ℝ := ((3:ℝ)/4)*(-Real.log ((3:ℝ)/4) + 1)
private def C3 : ℝ := ((3:ℝ)/4)^3/12

private def lg1 (β : ℝ) : ℝ := Real.log (2*(2-β))
private def dlg1 (β : ℝ) : ℝ := -(1/(2-β))
private def d2lg1 (β : ℝ) : ℝ := -(1/(2-β)^2)
private def lg2 (β : ℝ) : ℝ := Real.log (2*β)
private def dlg2 (β : ℝ) : ℝ := 1/β
private def d2lg2 (β : ℝ) : ℝ := -1/β^2

private def n2 (β : ℝ) : ℝ := 1/(2-β)^2
private def n3 (β : ℝ) : ℝ := 1/(2-β)^3
private def n4 (β : ℝ) : ℝ := 1/(2-β)^4
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

private def T5 (β : ℝ) : ℝ := ((3:ℝ)/4)*(lg1 β) + Kc + C3*(n2 β)
private def dT5 (β : ℝ) : ℝ := ((3:ℝ)/4)*(dlg1 β) + C3*(2*(n3 β))
private def d2T5 (β : ℝ) : ℝ := ((3:ℝ)/4)*(d2lg1 β) + C3*(2*(3*(n4 β)))
private def T6 (β : ℝ) : ℝ := ((3:ℝ)/4)*(lg2 β) + Kc + C3*(m2 β)
private def dT6 (β : ℝ) : ℝ := ((3:ℝ)/4)*(dlg2 β) + C3*(-2*(m3 β))
private def d2T6 (β : ℝ) : ℝ := ((3:ℝ)/4)*(d2lg2 β) + C3*(-2*(-3*(m4 β)))

private lemma hasDerivAt_T5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt T5 (dT5 β) β := by
  have h1 := (hasDerivAt_lg1 h).const_mul (((3:ℝ)/4))
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_n2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT5] <;> ring

private lemma hasDerivAt_dT5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt dT5 (d2T5 β) β := by
  rw [show dT5 = (fun x : ℝ => ((3:ℝ)/4)*(dlg1 x) + C3*(2*(n3 x))) from rfl]
  have h1 := (hasDerivAt_dlg1 h).const_mul (((3:ℝ)/4))
  have h2 := ((hasDerivAt_n3 h).const_mul (2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T5] <;> ring

private lemma hasDerivAt_T6 {β : ℝ} (h : β ≠ 0) : HasDerivAt T6 (dT6 β) β := by
  have h1 := (hasDerivAt_lg2 h).const_mul (((3:ℝ)/4))
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_m2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT6] <;> ring

private lemma hasDerivAt_dT6 {β : ℝ} (h : β ≠ 0) : HasDerivAt dT6 (d2T6 β) β := by
  rw [show dT6 = (fun x : ℝ => ((3:ℝ)/4)*(dlg2 x) + C3*(-2*(m3 x))) from rfl]
  have h1 := (hasDerivAt_dlg2 h).const_mul (((3:ℝ)/4))
  have h2 := ((hasDerivAt_m3 h).const_mul (-2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T6] <;> ring

/-! ## the `else`-branch log term `G` -/

private def G (β : ℝ) : ℝ := β*(Real.log 2 + 13/12) + β*(Real.log (((3:ℝ)/4)/β))
private def dG (β : ℝ) : ℝ := Real.log 2 + 13/12 + Real.log (((3:ℝ)/4)/β) - 1
private def d2G (β : ℝ) : ℝ := -(1/β)

private lemma hasDerivAt_G {β : ℝ} (h : β ≠ 0) : HasDerivAt G (dG β) β := by
  unfold G
  have h1 : HasDerivAt (fun x : ℝ => x*(Real.log 2 + 13/12)) (Real.log 2 + 13/12) β := by
    simpa using (hasDerivAt_id (x := β)).mul_const (Real.log 2 + 13/12)
  have h2 : HasDerivAt (fun x : ℝ => x*(Real.log (((3:ℝ)/4)/x))) (Real.log (((3:ℝ)/4)/β) - 1) β := by
    have hd := (hasDerivAt_id β).mul (hd_log_div (c := (3:ℝ)/4) (by norm_num) h)
    refine hd.congr_deriv ?_
    simp only [id_eq, one_mul]
    rw [one_div, mul_neg, mul_inv_cancel₀ h]
    ring
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [dG]; ring

private lemma hasDerivAt_dG {β : ℝ} (h : β ≠ 0) : HasDerivAt dG (d2G β) β := by
  unfold dG
  have h1 : HasDerivAt (fun x : ℝ => Real.log 2 + 13/12 + Real.log (((3:ℝ)/4)/x) - 1) (0 + (-(1/β)) - 0) β :=
    ((hasDerivAt_const β (Real.log 2 + 13/12)).add
      (hd_log_div (c := (3:ℝ)/4) (by norm_num) h)).sub (hasDerivAt_const β 1)
  refine h1.congr_deriv ?_
  rw [d2G]; ring

/-! ## the functions, their two derivatives -/

private def Ef1 (β : ℝ) : ℝ := ((13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)) - (T5 β + T6 β)

private def Df1 (β : ℝ) : ℝ :=
  ((13/5)*(dat1 β + dat2 β) + ((dfA β * at3 β + fA β * dat3 β) + dfQ1 β)) - (dT5 β + dT6 β)

private def E2f1 (β : ℝ) : ℝ :=
  ((13/5)*(d2at1 β + d2at2 β)
    + (((d2fA β * at3 β + 2*(dfA β * dat3 β)) + fA β * d2at3 β) + d2fQ1 β))
  - (d2T5 β + d2T6 β)

private def Ef2 (β : ℝ) : ℝ := ((13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)) - (T5 β + G β)

private def Df2 (β : ℝ) : ℝ :=
  ((13/5)*(dat1 β + dat2 β) + ((dfA β * at3 β + fA β * dat3 β) + dfQ1 β)) - (dT5 β + dG β)

private def E2f2 (β : ℝ) : ℝ :=
  ((13/5)*(d2at1 β + d2at2 β)
    + (((d2fA β * at3 β + 2*(dfA β * dat3 β)) + fA β * d2at3 β) + d2fQ1 β))
  - (d2T5 β + d2G β)

private lemma hasDerivAt_Ef1 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1) (h2 : β ≠ 2) (h0 : β ≠ 0) :
    HasDerivAt Ef1 (Df1 β) β := by
  have hE : Ef1 = fun x : ℝ => ((13/5)*(at1 x + at2 x) + (fA x * at3 x + fQ1 x)) - (T5 x + T6 x) :=
    funext (fun x => rfl)
  rw [hE]
  have h1 := ((hasDerivAt_at1 h32).add (hasDerivAt_at2 hm1)).const_mul (13/5)
  have h2' := ((hasDerivAt_fA h2).mul (hasDerivAt_at3 h2)).add (hasDerivAt_fQ1 h2)
  have h3' := (hasDerivAt_T5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_T6 h0)
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [Df1] <;> ring

private lemma hasDerivAt_Df1 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1) (h2 : β ≠ 2) (h0 : β ≠ 0) :
    HasDerivAt Df1 (E2f1 β) β := by
  have hD : Df1 = fun x : ℝ =>
      ((13/5)*(dat1 x + dat2 x) + ((dfA x * at3 x + fA x * dat3 x) + dfQ1 x)) - (dT5 x + dT6 x) :=
    funext (fun x => rfl)
  rw [hD]
  have h1 := ((hasDerivAt_dat1 β).add (hasDerivAt_dat2 β)).const_mul (13/5)
  have h2' := (((hasDerivAt_dfA h2).mul (hasDerivAt_at3 h2)).add
      ((hasDerivAt_fA h2).mul (hasDerivAt_dat3 β))).add (hasDerivAt_dfQ1 h2)
  have h3' := ((hasDerivAt_dT5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_dT6 h0))
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [E2f1] <;> ring

private lemma hasDerivAt_Ef2 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1) (h2 : β ≠ 2) (h0 : β ≠ 0) :
    HasDerivAt Ef2 (Df2 β) β := by
  have hE : Ef2 = fun x : ℝ => ((13/5)*(at1 x + at2 x) + (fA x * at3 x + fQ1 x)) - (T5 x + G x) :=
    funext (fun x => rfl)
  rw [hE]
  have h1 := ((hasDerivAt_at1 h32).add (hasDerivAt_at2 hm1)).const_mul (13/5)
  have h2' := ((hasDerivAt_fA h2).mul (hasDerivAt_at3 h2)).add (hasDerivAt_fQ1 h2)
  have h3' := (hasDerivAt_T5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_G h0)
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [Df2] <;> ring

private lemma hasDerivAt_Df2 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1) (h2 : β ≠ 2) (h0 : β ≠ 0) :
    HasDerivAt Df2 (E2f2 β) β := by
  have hD : Df2 = fun x : ℝ =>
      ((13/5)*(dat1 x + dat2 x) + ((dfA x * at3 x + fA x * dat3 x) + dfQ1 x)) - (dT5 x + dG x) :=
    funext (fun x => rfl)
  rw [hD]
  have h1 := ((hasDerivAt_dat1 β).add (hasDerivAt_dat2 β)).const_mul (13/5)
  have h2' := (((hasDerivAt_dfA h2).mul (hasDerivAt_at3 h2)).add
      ((hasDerivAt_fA h2).mul (hasDerivAt_dat3 β))).add (hasDerivAt_dfQ1 h2)
  have h3' := ((hasDerivAt_dT5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_dG h0))
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [E2f2] <;> ring


/-! ## convexity of `Ef1` and `Ef2` -/

private def P1f (β : ℝ) : ℝ := (13/5)*(d2at1 β + d2at2 β)
private def ARred (β : ℝ) : ℝ := 2*(dfA β * dat3 β) + fA β * d2at3 β + d2fQ1 β + d2fA β * (((3:ℝ)/4)/(2-β))
private def LG1f (β : ℝ) : ℝ := -(d2T5 β + d2T6 β)
private def LG2f (β : ℝ) : ℝ := -(d2T5 β + d2G β)

private lemma P1f_lower {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) : 2 ≤ P1f β := by
  have hq1 : ((3/2:ℝ)-β)^2+((3:ℝ)/4)^2 ≠ 0 := by positivity
  have hq2 : ((1:ℝ)+β)^2+((3:ℝ)/4)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < (((3/2:ℝ)-β)^2+((3:ℝ)/4)^2)^2 * (((1:ℝ)+β)^2+((3:ℝ)/4)^2)^2 := by positivity
  have hkey : (P1f β - 2) * ((((3/2:ℝ)-β)^2+((3:ℝ)/4)^2)^2 * (((1:ℝ)+β)^2+((3:ℝ)/4)^2)^2)
      = (213255/32768)*(1-β)^6 + (239973/16384)*β*(1-β)^6 + (906393/65536)*β^2
        + (771213/65536)*β^2*(1-β)^6 + (290101/65536)*β^3 + (1937285/65536)*β^3*(1-β)
        + (197059/16384)*β^5*(1-β) + (1222675/65536)*β^5*(1-β)^2 + (902285/65536)*β^5*(1-β)^3 := by
    unfold P1f d2at1 d2at2
    field_simp [hq1, hq2]
    ring
  have hnum : (0:ℝ) ≤ (213255/32768)*(1-β)^6 + (239973/16384)*β*(1-β)^6 + (906393/65536)*β^2
        + (771213/65536)*β^2*(1-β)^6 + (290101/65536)*β^3 + (1937285/65536)*β^3*(1-β)
        + (197059/16384)*β^5*(1-β) + (1222675/65536)*β^5*(1-β)^2 + (902285/65536)*β^5*(1-β)^3 := by
    positivity
  have hmul : (0:ℝ) ≤ (P1f β - 2) * ((((3/2:ℝ)-β)^2+((3:ℝ)/4)^2)^2 * (((1:ℝ)+β)^2+((3:ℝ)/4)^2)^2) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma ARred_lower {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) : -(5:ℝ)/2 ≤ ARred β := by
  have hne : (2:ℝ)-β ≠ 0 := by linarith
  have hB : ((2:ℝ)-β)^2+((3:ℝ)/4)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < (2-β)^8*(((2:ℝ)-β)^2+((3:ℝ)/4)^2)^4 := by positivity
  have hkey : (ARred β + 5/2) * ((2-β)^8*(((2:ℝ)-β)^2+((3:ℝ)/4)^2)^4)
      = (1242418363817/12681216)*(1-β)^6 + (22553276779087/202899456)*(1-β)^9
        + (1810583129269/67633152)*(1-β)^11 + (4879234334857/1597833216)*β^2*(1-β)^4
        + (801124978439/228261888)*β^2*(1-β)^5 + (14119438250165/1420296192)*β^2*(1-β)^11
        + (695352660371/913047552)*β^3*(1-β)^13 + (11160086218061/202899456)*β^4*(1-β)^5
        + (864604094609/304349184)*β^6*(1-β)^10 + (1341974236681/59179008)*β^8*(1-β)^4
        + (6032699043445/1420296192)*β^8*(1-β)^5 + (1026754047887/304349184)*β^9*(1-β)^7
        + (11059375/262144)*β^11*(1-β) + (17559325/32768)*β^11*(1-β)^2
        + (545830911/131072)*β^11*(1-β)^3 + (15625/65536)*β^12 + (1184085139085/913047552)*β^12*(1-β)^4 := by
    unfold ARred dfA dat3 fA d2at3 d2fQ1 d2fA
    field_simp [hne, hB]
    ring
  have hnum : (0:ℝ) ≤ (1242418363817/12681216)*(1-β)^6 + (22553276779087/202899456)*(1-β)^9
        + (1810583129269/67633152)*(1-β)^11 + (4879234334857/1597833216)*β^2*(1-β)^4
        + (801124978439/228261888)*β^2*(1-β)^5 + (14119438250165/1420296192)*β^2*(1-β)^11
        + (695352660371/913047552)*β^3*(1-β)^13 + (11160086218061/202899456)*β^4*(1-β)^5
        + (864604094609/304349184)*β^6*(1-β)^10 + (1341974236681/59179008)*β^8*(1-β)^4
        + (6032699043445/1420296192)*β^8*(1-β)^5 + (1026754047887/304349184)*β^9*(1-β)^7
        + (11059375/262144)*β^11*(1-β) + (17559325/32768)*β^11*(1-β)^2
        + (545830911/131072)*β^11*(1-β)^3 + (15625/65536)*β^12 + (1184085139085/913047552)*β^12*(1-β)^4 := by
    positivity
  have hmul : (0:ℝ) ≤ (ARred β + 5/2) * ((2-β)^8*(((2:ℝ)-β)^2+((3:ℝ)/4)^2)^4) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma LG1f_lower {β : ℝ} (h0 : (3:ℝ)/4 ≤ β) (h1 : β ≤ 1) : 1 ≤ LG1f β := by
  have hb : β ≠ 0 := by linarith
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have hden : (0:ℝ) < β^4*(2-β)^4 := by positivity
  have hkey : (LG1f β - 1) * (β^4*(2-β)^4)
      = (3051/256)*(1-β)^4 + (722451/192512)*(β-3/4)*(1-β) + (219993/12032)*(β-3/4)*(1-β)^3
        + (1215/47)*(β-3/4)^2*(1-β)^5 + (237371/48128)*(β-3/4)^3 + (1714/47)*(β-3/4)^3*(1-β)^5
        + (3269/3008)*(β-3/4)^5 + (6007/752)*(β-3/4)^5*(1-β) + (1667/47)*(β-3/4)^6*(1-β)^2 := by
    unfold LG1f d2T5 d2T6 C3 d2lg1 d2lg2 n4 m4
    field_simp [hb, h2b]
    ring
  have hnum : (0:ℝ) ≤ (3051/256)*(1-β)^4 + (722451/192512)*(β-3/4)*(1-β) + (219993/12032)*(β-3/4)*(1-β)^3
        + (1215/47)*(β-3/4)^2*(1-β)^5 + (237371/48128)*(β-3/4)^3 + (1714/47)*(β-3/4)^3*(1-β)^5
        + (3269/3008)*(β-3/4)^5 + (6007/752)*(β-3/4)^5*(1-β) + (1667/47)*(β-3/4)^6*(1-β)^2 := by
    positivity
  have hmul : (0:ℝ) ≤ (LG1f β - 1) * (β^4*(2-β)^4) := by
    rw [hkey]; exact hnum
  have hfin := nonneg_of_mul_nonneg_left hmul hden
  linarith

private lemma LG2f_lower {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 3/4) : (4:ℝ)/3 ≤ LG2f β := by
  have hA : (0:ℝ) < 2-β := by linarith
  have hkey : LG2f β = ((3:ℝ)/4)*(2*(2-β)^2-((3:ℝ)/4)^2)/(2*(2-β)^4) + 1/β := by
    unfold LG2f d2T5 d2lg1 n4 C3 d2G
    field_simp
    ring
  rw [hkey]
  have hp : (0:ℝ) ≤ ((3:ℝ)/4)*(2*(2-β)^2-((3:ℝ)/4)^2)/(2*(2-β)^4) := by
    apply div_nonneg
    · apply mul_nonneg (by norm_num)
      nlinarith [h1]
    · positivity
  have hb : (4:ℝ)/3 ≤ 1/β := by
    rw [le_div_iff₀ h0]; linarith
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

private lemma at3_le {β : ℝ} (h : β ≤ 1) : at3 β ≤ ((3:ℝ)/4)/(2-β) := by
  unfold at3
  apply Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
  apply div_nonneg (by norm_num); linarith

private lemma E2f1_nonneg {β : ℝ} (h0 : (3:ℝ)/4 ≤ β) (h1 : β ≤ 1) : (0:ℝ) ≤ E2f1 β := by
  have hP1 : (2:ℝ) ≤ P1f β := P1f_lower (by linarith) h1
  have hAR : -(5:ℝ)/2 ≤ ARred β := ARred_lower (by linarith) h1
  have hLG := LG1f_lower h0 h1
  have hsplit : E2f1 β = P1f β + ARred β + LG1f β + d2fA β * (at3 β - ((3:ℝ)/4)/(2-β)) := by
    unfold E2f1 P1f ARred LG1f; ring
  have hd2 : d2fA β ≤ 0 := d2fA_nonpos h1
  have hat : at3 β - ((3:ℝ)/4)/(2-β) ≤ 0 := by have := at3_le h1; linarith
  have hprod : 0 ≤ d2fA β * (at3 β - ((3:ℝ)/4)/(2-β)) := mul_nonneg_of_nonpos_of_nonpos hd2 hat
  rw [hsplit]; linarith

private lemma E2f2_nonneg {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 3/4) : (0:ℝ) ≤ E2f2 β := by
  have hP1 : (2:ℝ) ≤ P1f β := P1f_lower (by linarith) (by linarith)
  have hAR : -(5:ℝ)/2 ≤ ARred β := ARred_lower (by linarith) (by linarith)
  have hLG := LG2f_lower h0 h1
  have hsplit : E2f2 β = P1f β + ARred β + LG2f β + d2fA β * (at3 β - ((3:ℝ)/4)/(2-β)) := by
    unfold E2f2 P1f ARred LG2f; ring
  have hd2 : d2fA β ≤ 0 := d2fA_nonpos (by linarith)
  have hat : at3 β - ((3:ℝ)/4)/(2-β) ≤ 0 := by have := at3_le (show β ≤ 1 by linarith); linarith
  have hprod : 0 ≤ d2fA β * (at3 β - ((3:ℝ)/4)/(2-β)) := mul_nonneg_of_nonpos_of_nonpos hd2 hat
  rw [hsplit]; linarith

private lemma hasDerivAt_Ef1_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/2:ℝ) (9/8)) :
    HasDerivAt Ef1 (Df1 x) x :=
  hasDerivAt_Ef1 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_Df1_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/2:ℝ) (9/8)) :
    HasDerivAt Df1 (E2f1 x) x :=
  hasDerivAt_Df1 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_Ef2_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (9/8)) :
    HasDerivAt Ef2 (Df2 x) x :=
  hasDerivAt_Ef2 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_Df2_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (9/8)) :
    HasDerivAt Df2 (E2f2 x) x :=
  hasDerivAt_Df2 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma nbd_Ioo_I {x : ℝ} (hx : x ∈ Set.Ioo (3/4:ℝ) 1) : Set.Ioo (1/2:ℝ) (9/8) ∈ 𝓝 x := by
  apply isOpen_Ioo.mem_nhds
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private lemma nbd_Ioo_II {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (3/4)) : Set.Ioo (0:ℝ) (9/8) ∈ 𝓝 x := by
  apply isOpen_Ioo.mem_nhds
  exact ⟨hx.1, by linarith [hx.2]⟩

private lemma differentiableOn_Ef1 : DifferentiableOn ℝ Ef1 (Set.Icc (3/4:ℝ) 1) := by
  intro x hx
  exact (hasDerivAt_Ef1_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt

private lemma differentiableOn_deriv_Ef1 : DifferentiableOn ℝ (deriv Ef1) (Set.Ioo (3/4:ℝ) 1) := by
  intro x hx
  have hev : deriv Ef1 =ᶠ[𝓝 x] Df1 := by
    filter_upwards [nbd_Ioo_I hx] with y hy
    exact (hasDerivAt_Ef1_Ioo hy).deriv
  have h1 : DifferentiableAt ℝ (deriv Ef1) x := by
    rw [hev.differentiableAt_iff]
    exact (hasDerivAt_Df1_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt
  exact h1.differentiableWithinAt

private lemma second_deriv_Ef1_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (3/4:ℝ) 1) : 0 ≤ deriv^[2] Ef1 x := by
  have hev : deriv Ef1 =ᶠ[𝓝 x] Df1 := by
    filter_upwards [nbd_Ioo_I hx] with y hy
    exact (hasDerivAt_Ef1_Ioo hy).deriv
  have hdd : deriv (deriv Ef1) x = E2f1 x := by
    rw [hev.deriv_eq]
    exact (hasDerivAt_Df1_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).deriv
  change 0 ≤ deriv (deriv Ef1) x
  rw [hdd]
  exact E2f1_nonneg (le_of_lt hx.1) (le_of_lt hx.2)

private lemma convexOn_Ef1 : ConvexOn ℝ (Set.Icc (3/4:ℝ) 1) Ef1 := by
  refine convexOn_of_deriv2_nonneg (convex_Icc _ _) differentiableOn_Ef1.continuousOn ?_ ?_ ?_
  · rw [interior_Icc]; exact differentiableOn_Ef1.mono Set.Ioo_subset_Icc_self
  · rw [interior_Icc]; exact differentiableOn_deriv_Ef1
  · intro x hx
    rw [interior_Icc] at hx
    exact second_deriv_Ef1_nonneg hx

private lemma differentiableOn_deriv_Ef2 : DifferentiableOn ℝ (deriv Ef2) (Set.Ioo (0:ℝ) (3/4)) := by
  intro x hx
  have hev : deriv Ef2 =ᶠ[𝓝 x] Df2 := by
    filter_upwards [nbd_Ioo_II hx] with y hy
    exact (hasDerivAt_Ef2_Ioo hy).deriv
  have h1 : DifferentiableAt ℝ (deriv Ef2) x := by
    rw [hev.differentiableAt_iff]
    exact (hasDerivAt_Df2_Ioo ⟨hx.1, by linarith [hx.2]⟩).differentiableAt
  exact h1.differentiableWithinAt

private lemma second_deriv_Ef2_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (3/4)) : 0 ≤ deriv^[2] Ef2 x := by
  have hev : deriv Ef2 =ᶠ[𝓝 x] Df2 := by
    filter_upwards [nbd_Ioo_II hx] with y hy
    exact (hasDerivAt_Ef2_Ioo hy).deriv
  have hdd : deriv (deriv Ef2) x = E2f2 x := by
    rw [hev.deriv_eq]
    exact (hasDerivAt_Df2_Ioo ⟨hx.1, by linarith [hx.2]⟩).deriv
  change 0 ≤ deriv (deriv Ef2) x
  rw [hdd]
  exact E2f2_nonneg hx.1 (le_of_lt hx.2)

private lemma convexOn_Ef2 : ConvexOn ℝ (Set.Ioo (0:ℝ) (3/4)) Ef2 := by
  refine convexOn_of_deriv2_nonneg (convex_Ioo _ _) ?_ ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_Ef2_Ioo ⟨hx.1, by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro x hx
    exact (hasDerivAt_Ef2_Ioo ⟨hx.1, by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]; exact differentiableOn_deriv_Ef2
  · intro x hx
    rw [interior_Ioo] at hx
    exact second_deriv_Ef2_nonneg hx


/-! ## numerical bounds -/

private lemma log_one_add_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (n : ℕ) :
    Real.log (1+y) ≤ -(∑ i ∈ Finset.range n, (-y)^(i+1)/(i+1)) + y^(n+1)/(1-y) := by
  have h1 : |(-y : ℝ)| < 1 := by rw [abs_neg, abs_of_nonneg hy0]; exact hy1
  have h := Real.abs_log_sub_add_sum_range_le h1 n
  have h2 := (abs_le.mp h).2
  rw [abs_neg, abs_of_nonneg hy0] at h2
  rw [show (1:ℝ) - -y = 1+y by ring] at h2
  linarith

private lemma log_one_add_ge {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, (-y)^(i+1)/(i+1)) - y^(n+1)/(1-y) ≤ Real.log (1+y) := by
  have h1 : |(-y : ℝ)| < 1 := by rw [abs_neg, abs_of_nonneg hy0]; exact hy1
  have h := Real.abs_log_sub_add_sum_range_le h1 n
  have h2 := (abs_le.mp h).1
  rw [abs_neg, abs_of_nonneg hy0] at h2
  rw [show (1:ℝ) - -y = 1+y by ring] at h2
  linarith

private lemma log_two_lt : Real.log 2 ≤ (0.6931471808:ℝ) := le_of_lt Real.log_two_lt_d9
private lemma log_two_gt : (0.6931471803:ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9

private lemma log_4_3_upper : Real.log ((4:ℝ)/3) ≤ (2877:ℝ)/10000 := by
  have h1 : ((4:ℝ)/3) = 1 + (1:ℝ)/3 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (1:ℝ)/3) (by norm_num) (by norm_num) 10
  have hsum : -(∑ i ∈ Finset.range 10, (-((1:ℝ)/3))^(i+1)/(i+1)) + ((1:ℝ)/3)^(10+1)/(1-(1:ℝ)/3)
      ≤ (2877:ℝ)/10000 := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_3_2_upper : Real.log ((3:ℝ)/2) ≤ (405481:ℝ)/1000000 := by
  have h1 : ((3:ℝ)/2) = 1 + (1:ℝ)/2 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (1:ℝ)/2) (by norm_num) (by norm_num) 16
  have hsum : -(∑ i ∈ Finset.range 16, (-((1:ℝ)/2))^(i+1)/(i+1)) + ((1:ℝ)/2)^(16+1)/(1-(1:ℝ)/2)
      ≤ (405481:ℝ)/1000000 := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_5_4_upper : Real.log ((5:ℝ)/4) ≤ (22315:ℝ)/100000 := by
  have h1 : ((5:ℝ)/4) = 1 + (1:ℝ)/4 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (1:ℝ)/4) (by norm_num) (by norm_num) 8
  have hsum : -(∑ i ∈ Finset.range 8, (-((1:ℝ)/4))^(i+1)/(i+1)) + ((1:ℝ)/4)^(8+1)/(1-(1:ℝ)/4)
      ≤ (22315:ℝ)/100000 := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_5_2_upper : Real.log ((5:ℝ)/2) ≤ (9163:ℝ)/10000 := by
  have hsplit : Real.log ((5:ℝ)/2) = Real.log 2 + Real.log ((5:ℝ)/4) := by
    rw [show (5:ℝ)/2 = 2*((5:ℝ)/4) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hsplit]
  have h4 := log_5_4_upper
  have h2 := log_two_lt
  linarith

private lemma log_81_250_upper : Real.log (1+(81:ℝ)/250) ≤ (28067:ℝ)/100000 := by
  have h := log_one_add_le (y := (81:ℝ)/250) (by norm_num) (by norm_num) 10
  have hsum : -(∑ i ∈ Finset.range 10, (-((81:ℝ)/250))^(i+1)/(i+1)) + ((81:ℝ)/250)^(10+1)/(1-(81:ℝ)/250)
      ≤ (28067:ℝ)/100000 := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_375_338_upper : Real.log ((375:ℝ)/338) ≤ (103881:ℝ)/1000000 := by
  have h1 : ((375:ℝ)/338) = 1 + (37:ℝ)/338 := by norm_num
  rw [h1]
  have h := log_one_add_le (y := (37:ℝ)/338) (by norm_num) (by norm_num) 6
  have hsum : -(∑ i ∈ Finset.range 6, (-((37:ℝ)/338))^(i+1)/(i+1)) + ((37:ℝ)/338)^(6+1)/(1-(37:ℝ)/338)
      ≤ (103881:ℝ)/1000000 := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_375_338_lower : (103879:ℝ)/1000000 ≤ Real.log ((375:ℝ)/338) := by
  have h1 : ((375:ℝ)/338) = 1 + (37:ℝ)/338 := by norm_num
  rw [h1]
  have h := log_one_add_ge (y := (37:ℝ)/338) (by norm_num) (by norm_num) 6
  have hsum : (103879:ℝ)/1000000 ≤
      -(∑ i ∈ Finset.range 6, (-((37:ℝ)/338))^(i+1)/(i+1)) - ((37:ℝ)/338)^(6+1)/(1-(37:ℝ)/338) := by
    norm_num [Finset.sum_range_succ]
  linarith

private lemma arctan_3_7_lower : (40489:ℝ)/100000 ≤ Real.arctan ((3:ℝ)/7) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((3:ℝ)/7) (by norm_num)
  have hpoly : (40489:ℝ)/100000 ≤ (3/7) - (3/7)^3/3 + (3/7)^5/5 - (3/7)^7/7
      + (3/7)^9/9 - (3/7)^11/11 + (3/7)^13/13 - (3/7)^15/15 := by norm_num
  linarith

private lemma arctan_3_5_lower : (5404:ℝ)/10000 ≤ Real.arctan ((3:ℝ)/5) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((3:ℝ)/5) (by norm_num)
  have hpoly : (5404:ℝ)/10000 ≤ (3/5) - (3/5)^3/3 + (3/5)^5/5 - (3/5)^7/7
      + (3/5)^9/9 - (3/5)^11/11 + (3/5)^13/13 - (3/5)^15/15 := by norm_num
  linarith

private lemma arctan_3_5_upper : Real.arctan ((3:ℝ)/5) ≤ (3:ℝ)/5 :=
  Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg (by norm_num)

private lemma arctan_37_787_upper : Real.arctan ((37:ℝ)/787) ≤ (4698:ℝ)/100000 := by
  have h := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4 ((37:ℝ)/787) (by norm_num)
  have hpoly : (37:ℝ)/787 - (37/787)^3/3 + (37/787)^5/5 - (37/787)^7/7 + (37/787)^9/9
      ≤ (4698:ℝ)/100000 := by norm_num
  linarith

private lemma arctan_375_412_lower : (73841:ℝ)/100000 ≤ Real.arctan ((375:ℝ)/412) := by
  have hid : Real.arctan ((375:ℝ)/412) = Real.pi/4 - Real.arctan ((37:ℝ)/787) := by
    have h := Real.arctan_add (x := (375:ℝ)/412) (y := (37:ℝ)/787) (by norm_num)
    rw [show ((375:ℝ)/412 + (37:ℝ)/787)/(1 - ((375:ℝ)/412)*((37:ℝ)/787)) = 1 by norm_num,
        Real.arctan_one] at h
    linarith
  rw [hid]
  have hp := Real.pi_gt_d20
  have hu := arctan_37_787_upper
  linarith

private lemma arctan_375_838_lower : (4207:ℝ)/10000 ≤ Real.arctan ((375:ℝ)/838) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((375:ℝ)/838) (by norm_num)
  have hpoly : (4207:ℝ)/10000 ≤ (375/838) - (375/838)^3/3 + (375/838)^5/5 - (375/838)^7/7
      + (375/838)^9/9 - (375/838)^11/11 + (375/838)^13/13 - (375/838)^15/15 := by norm_num
  linarith

private lemma arctan_375_662_lower : (51539:ℝ)/100000 ≤ Real.arctan ((375:ℝ)/662) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((375:ℝ)/662) (by norm_num)
  have hpoly : (51539:ℝ)/100000 ≤ (375/662) - (375/662)^3/3 + (375/662)^5/5 - (375/662)^7/7
      + (375/662)^9/9 - (375/662)^11/11 + (375/662)^13/13 - (375/662)^15/15 := by norm_num
  linarith

private lemma arctan_375_662_upper : Real.arctan ((375:ℝ)/662) ≤ (5156:ℝ)/10000 := by
  have h := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4 ((375:ℝ)/662) (by norm_num)
  have hpoly : (375:ℝ)/662 - (375/662)^3/3 + (375/662)^5/5 - (375/662)^7/7 + (375/662)^9/9
      ≤ (5156:ℝ)/10000 := by norm_num
  linarith

/-! ## point evaluations -/

private lemma Ef1_at_34_lower : (8:ℝ)/25 ≤ Ef1 (3/4) := by
  have hE : Ef1 (3/4) = (13/5)*(Real.pi/4 + Real.arctan ((3:ℝ)/7))
      + (1374:ℝ)/3125 * Real.arctan ((3:ℝ)/5) + (3462:ℝ)/180625
      - ((3:ℝ)/4*(Real.log ((5:ℝ)/2) + Real.log ((4:ℝ)/3) + 1) + (9:ℝ)/400)
      - ((3:ℝ)/4*(Real.log ((3:ℝ)/2) + Real.log ((4:ℝ)/3) + 1) + (1:ℝ)/16) := by
    unfold Ef1 at1 at2 at3 fA fQ1 T5 T6 lg1 lg2 n2 m2 Kc C3
    have hl : -Real.log ((3:ℝ)/4) = Real.log ((4:ℝ)/3) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]; ring
    rw [show (3:ℝ)/4/(3/2-3/4) = 1 by norm_num, Real.arctan_one, hl]
    norm_num
    ring
  rw [hE]
  have hp := Real.pi_gt_d20
  have ha1 := arctan_3_7_lower
  have ha3 := arctan_3_5_lower
  have hl1 := log_5_2_upper
  have hl2 := log_4_3_upper
  have hl3 := log_3_2_upper
  linarith

private lemma Df1_at_34_nonneg : (0:ℝ) ≤ Df1 (3/4) := by
  have hD : Df1 (3/4) = (86226237:ℝ)/89048125 + (-(4752:ℝ)/3125) * Real.arctan ((3:ℝ)/5) := by
    unfold Df1 at3 dat1 dat2 dat3 dfA fA dfQ1 dT5 dT6 dlg1 dlg2 C3 n3 m3
    norm_num
    ring
  rw [hD]
  have h := arctan_3_5_upper
  linarith

private lemma Ef2_at_x0_lower : (327:ℝ)/1000 ≤ Ef2 (169/250) := by
  have hE : Ef2 (169/250) = (13/5)*(Real.arctan ((375:ℝ)/412) + Real.arctan ((375:ℝ)/838))
      + (2174115284802:ℝ)/3973195810651 * Real.arctan ((375:ℝ)/662)
      + (110568087984829500000:ℝ)/4022282414152208647081
      - ((3:ℝ)/4*(Real.log 2 + Real.log (1+(81:ℝ)/250) + Real.log ((4:ℝ)/3) + 1) + (562500:ℝ)/28047616)
      - ((169:ℝ)/250*(Real.log 2 + 13/12) + (169:ℝ)/250*Real.log ((375:ℝ)/338)) := by
    unfold Ef2 at1 at2 at3 fA fQ1 T5 G lg1 n2 Kc C3
    have hl : -Real.log ((3:ℝ)/4) = Real.log ((4:ℝ)/3) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]; ring
    rw [hl]
    rw [show Real.log (2*(2-169/250)) = Real.log 2 + Real.log (1+(81:ℝ)/250) by
      rw [show (2:ℝ)*(2-169/250) = 2*(1+(81:ℝ)/250) by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]]
    norm_num
    ring
  rw [hE]
  have ha1 := arctan_375_412_lower
  have ha2 := arctan_375_838_lower
  have ha3 := arctan_375_662_lower
  have hl1 := log_two_lt
  have hl2 := log_81_250_upper
  have hl3 := log_4_3_upper
  have hl4 := log_375_338_upper
  linarith

private lemma Df2_at_x0_lower : -(1:ℝ)/100 ≤ Df2 (169/250) := by
  have hD : Df2 (169/250) =
      (14631666798122578858460358155173508217940829:ℝ)/9677440325367777163819214352612702019329552
      + (-(1823269795062500:ℝ)/1315127813325481) * Real.arctan ((375:ℝ)/662)
      - Real.log 2 - Real.log ((375:ℝ)/338) := by
    unfold Df2 at3 dat1 dat2 dat3 dfA fA dfQ1 dT5 dG dlg1 C3 n3
    norm_num
    ring
  rw [hD]
  have ha3 := arctan_375_662_upper
  have hl1 := log_two_lt
  have hl4 := log_375_338_upper
  linarith

private lemma Df2_at_x0_upper : Df2 (169/250) ≤ (1:ℝ)/100 := by
  have hD : Df2 (169/250) =
      (14631666798122578858460358155173508217940829:ℝ)/9677440325367777163819214352612702019329552
      + (-(1823269795062500:ℝ)/1315127813325481) * Real.arctan ((375:ℝ)/662)
      - Real.log 2 - Real.log ((375:ℝ)/338) := by
    unfold Df2 at3 dat1 dat2 dat3 dfA fA dfQ1 dT5 dG dlg1 C3 n3
    norm_num
    ring
  rw [hD]
  have ha3 := arctan_375_662_lower
  have hl1 := log_two_gt
  have hl4 := log_375_338_lower
  linarith

theorem WJ_threequarter_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (8:ℝ)/25 ≤
      ( (13/5)*(Real.arctan ((3/4)/(3/2-β)) + Real.arctan ((3/4)/(1+β)))
        + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan ((3/4)/(2-β))
        + ((2-β)^2-β^2)^2/8 * ((Real.arctan ((3/4)/(2-β)) + (2-β)*(3/4)/((2-β)^2+(3/4)^2))/(2*(2-β)^3))
        + ((2-β)^2-β^2)^3/16 * (3*Real.arctan ((3/4)/(2-β))/(8*(2-β)^5) + (3/4)*(5*(2-β)^2+3*(3/4)^2)/(8*(2-β)^4*((2-β)^2+(3/4)^2)^2)) )
      - ((3/4)*(Real.log (2*(2-β)) - Real.log (3/4) + 1) + (3/4)^3/(12*(2-β)^2))
      - (if (3/4 : ℝ) ≤ β then (3/4)*(Real.log (2*β) - Real.log (3/4) + 1) + (3/4)^3/(12*β^2)
          else β*(Real.log 2 + 13/12) + β*Real.log ((3/4)/β)) := by
  rcases lt_or_ge β ((3:ℝ)/4) with hlt | hge
  · have hkey : (8:ℝ)/25 ≤ Ef2 β := by
      have hx0 : (169/250:ℝ) ∈ Set.Ioo (0:ℝ) (3/4) := by norm_num
      have hβmem : β ∈ Set.Ioo (0:ℝ) (3/4) := ⟨hβ0, hlt⟩
      have hdx : (169/250:ℝ) ∈ Set.Ioo (0:ℝ) (9/8) := by norm_num
      have hdiff : DifferentiableAt ℝ Ef2 (169/250) := (hasDerivAt_Ef2_Ioo hdx).differentiableAt
      have hderiv : deriv Ef2 (169/250) = Df2 (169/250) := (hasDerivAt_Ef2_Ioo hdx).deriv
      have htang : Ef2 (169/250) + Df2 (169/250) * (β - 169/250) ≤ Ef2 β := by
        rcases lt_trichotomy β (169/250) with hlt2 | heq2 | hgt2
        · have hsl := convexOn_Ef2.slope_le_deriv hβmem hx0 hlt2 hdiff
          rw [slope_def_field] at hsl
          rw [hderiv] at hsl
          have hpos : (0:ℝ) < (169/250:ℝ) - β := by linarith
          have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
          rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
          nlinarith
        · subst heq2; simp
        · have hsl := convexOn_Ef2.deriv_le_slope hx0 hβmem hgt2 hdiff
          rw [slope_def_field] at hsl
          rw [hderiv] at hsl
          have hpos : (0:ℝ) < β - 169/250 := by linarith
          have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
          rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
          nlinarith
      have habs1 : |Df2 (169/250)| ≤ (1:ℝ)/100 := by
        rw [abs_le]
        constructor <;> linarith [Df2_at_x0_lower, Df2_at_x0_upper]
      have habs2 : |β - 169/250| ≤ (169:ℝ)/250 := by
        rw [abs_le]; exact ⟨by linarith, by linarith⟩
      have habs3 : |Df2 (169/250) * (β - 169/250)| ≤ (1:ℝ)/100 * ((169:ℝ)/250) := by
        rw [abs_mul]
        exact mul_le_mul habs1 habs2 (abs_nonneg _) (by norm_num)
      have hprod : -(1:ℝ)/100 * ((169:ℝ)/250) ≤ Df2 (169/250) * (β - 169/250) := by
        have h := (abs_le.mp habs3).1
        linarith
      linarith [htang, hprod, Ef2_at_x0_lower]
    rw [if_neg (not_le.mpr hlt)]
    convert hkey using 1
    unfold Ef2 at1 at2 at3 fA fQ1 T5 G lg1 n2 Kc C3
    have hb0 : β ≠ 0 := by linarith
    have h2b : (2:ℝ)-β ≠ 0 := by linarith
    have h32 : (3:ℝ)/2-β ≠ 0 := by linarith
    have hm1 : (1:ℝ)+β ≠ 0 := by linarith
    field_simp
    ring
  · have hkey : (8:ℝ)/25 ≤ Ef1 β := by
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [← heq]; exact Ef1_at_34_lower
      · have hx : (3/4:ℝ) ∈ Set.Icc (3/4:ℝ) 1 := ⟨le_refl _, by norm_num⟩
        have hy : β ∈ Set.Icc (3/4:ℝ) 1 := ⟨hge, le_of_lt hβ1⟩
        have hd3 : (3/4:ℝ) ∈ Set.Ioo (1/2:ℝ) (9/8) := by norm_num
        have hdiff : DifferentiableAt ℝ Ef1 (3/4) := (hasDerivAt_Ef1_Ioo hd3).differentiableAt
        have hsl := convexOn_Ef1.deriv_le_slope hx hy hgt hdiff
        rw [slope_def_field] at hsl
        rw [(hasDerivAt_Ef1_Ioo hd3).deriv] at hsl
        have hpos : (0:ℝ) < β - 3/4 := by linarith
        have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
        rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
        have hprod : (0:ℝ) ≤ Df1 (3/4) * (β - 3/4) :=
          mul_nonneg Df1_at_34_nonneg (le_of_lt hpos)
        linarith [hmul, hprod, Ef1_at_34_lower]
    rw [if_pos hge]
    convert hkey using 1
    unfold Ef1 at1 at2 at3 fA fQ1 T5 T6 lg1 lg2 n2 m2 Kc C3
    have hb0 : β ≠ 0 := by linarith
    have h2b : (2:ℝ)-β ≠ 0 := by linarith
    have h32 : (3:ℝ)/2-β ≠ 0 := by linarith
    have hm1 : (1:ℝ)+β ≠ 0 := by linarith
    field_simp
    ring

end
end Commons.Analysis.Real