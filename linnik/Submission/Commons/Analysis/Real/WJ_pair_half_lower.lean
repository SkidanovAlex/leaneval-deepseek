import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_poly_bounds_on_unit
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_five_ninths_lower

namespace Commons.Analysis.Real

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

/-! ## Derivative helpers (generic) -/

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

/-- second derivative helper for `atan (k/(a-x))` -/
private lemma hd_at_csub_second {a k β : ℝ} (hk : k ≠ 0) :
    HasDerivAt (fun x : ℝ => k/((a-x)^2+k^2)) (2*k*(a-β)/(((a-β)^2+k^2)^2)) β := by
  have hq : HasDerivAt (fun x : ℝ => (a-x)^2+k^2) (-2*(a-β)) β := by
    have h2 := ((hd_csub a β).pow 2).add_const (k^2)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]; ring
  have hq0 : ((a:ℝ)-β)^2+k^2 ≠ 0 := by
    have hk2 : (0:ℝ) < k^2 := sq_pos_of_ne_zero hk
    have : (0:ℝ) < ((a:ℝ)-β)^2+k^2 := by nlinarith [sq_nonneg ((a:ℝ)-β)]
    exact ne_of_gt this
  have h := hd_div_const (c:=k) hq hq0
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- second derivative helper for `atan (k/(a+x))` -/
private lemma hd_at_add_second {a k β : ℝ} (hk : k ≠ 0) :
    HasDerivAt (fun x : ℝ => k/((a+x)^2+k^2)) (-2*k*(a+β)/(((a+β)^2+k^2)^2)) β := by
  have hq : HasDerivAt (fun x : ℝ => (a+x)^2+k^2) (2*(a+β)) β := by
    have h2 := (((hasDerivAt_id β).const_add a).pow 2).add_const (k^2)
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq]; ring
  have hq0 : ((a:ℝ)+β)^2+k^2 ≠ 0 := by
    have hk2 : (0:ℝ) < k^2 := sq_pos_of_ne_zero hk
    have : (0:ℝ) < ((a:ℝ)+β)^2+k^2 := by nlinarith [sq_nonneg ((a:ℝ)+β)]
    exact ne_of_gt this
  have h := hd_div_const (c:=k) hq hq0
  refine h.congr_deriv ?_
  field_simp
  try ring

private lemma hd_sq (β : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*β) β := by
  have h := (hasDerivAt_id β).pow 2
  refine h.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq]; ring

private lemma hd_mono (n : ℕ) (c β : ℝ) :
    HasDerivAt (fun x : ℝ => c * x^n) (c * (n:ℝ) * β^(n-1)) β := by
  have h := ((hasDerivAt_id β).pow n).const_mul c
  refine h.congr_deriv ?_
  simp only [id_eq, mul_one]; ring

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
    simp only [Nat.reduceSub, pow_one]; ring
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

private lemma hd_inv2sub3 (β : ℝ) (h : (2:ℝ) - β ≠ 0) :
    HasDerivAt (fun x : ℝ => 1/(2-x)^3) (3/(2-β)^4) β := by
  have hq : HasDerivAt (fun x : ℝ => ((2:ℝ)-x)^3) (3*((2:ℝ)-β)^2*(-1)) β := by
    have h2 := (hd_csub (2:ℝ) β).pow 3
    refine h2.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]; ring
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

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
    simp only [Nat.reduceSub, pow_one, id_eq]; ring
  have h2 := hd_div_const (c := (1:ℝ)) hq (by positivity)
  refine h2.congr_deriv ?_
  field_simp <;> ring

/-! ## The atoms -/

private def at1 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/2)/(3/2-β))
private def dat1 (β : ℝ) : ℝ := ((1:ℝ)/2)/((3/2-β)^2+((1:ℝ)/2)^2)
private def d2at1 (β : ℝ) : ℝ := 2*((1:ℝ)/2)*(3/2-β)/(((3/2-β)^2+((1:ℝ)/2)^2)^2)

private def at2 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/2)/(1+β))
private def dat2 (β : ℝ) : ℝ := -(((1:ℝ)/2)/((1+β)^2+((1:ℝ)/2)^2))
private def d2at2 (β : ℝ) : ℝ := 2*((1:ℝ)/2)*(1+β)/(((1+β)^2+((1:ℝ)/2)^2)^2)

private def at3 (β : ℝ) : ℝ := Real.arctan (((1:ℝ)/2)/(2-β))
private def dat3 (β : ℝ) : ℝ := ((1:ℝ)/2)/((2-β)^2+((1:ℝ)/2)^2)
private def d2at3 (β : ℝ) : ℝ := 2*((1:ℝ)/2)*(2-β)/(((2-β)^2+((1:ℝ)/2)^2)^2)

private lemma hasDerivAt_at1 {β : ℝ} (h : β ≠ 3/2) : HasDerivAt at1 (dat1 β) β := by
  have hh := hd_arctan_csub (a := (3:ℝ)/2) (k := (1:ℝ)/2) (β := β) (by
    intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat1]; try ring

private lemma hasDerivAt_at2 {β : ℝ} (h : β ≠ -1) : HasDerivAt at2 (dat2 β) β := by
  have hh := hd_arctan_add (a := (1:ℝ)) (k := (1:ℝ)/2) (β := β) (by
    intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat2]; try ring

private lemma hasDerivAt_at3 {β : ℝ} (h : β ≠ 2) : HasDerivAt at3 (dat3 β) β := by
  have hh := hd_arctan_csub (a := (2:ℝ)) (k := (1:ℝ)/2) (β := β) (by
    intro hc; exact h (by linarith [hc]))
  refine hh.congr_deriv ?_
  rw [dat3]; try ring

private lemma hasDerivAt_dat1 (β : ℝ) : HasDerivAt dat1 (d2at1 β) β := by
  have h := hd_at_csub_second (a := (3:ℝ)/2) (k := (1:ℝ)/2) (β := β) (by norm_num)
  refine h.congr_deriv ?_
  rw [d2at1]

private lemma hasDerivAt_dat2 (β : ℝ) : HasDerivAt dat2 (d2at2 β) β := by
  have h := hd_at_add_second (a := (1:ℝ)) (k := (1:ℝ)/2) (β := β) (by norm_num)
  refine h.neg.congr_deriv ?_
  rw [d2at2]; ring

private lemma hasDerivAt_dat3 (β : ℝ) : HasDerivAt dat3 (d2at3 β) β := by
  have h := hd_at_csub_second (a := (2:ℝ)) (k := (1:ℝ)/2) (β := β) (by norm_num)
  refine h.congr_deriv ?_
  rw [d2at3]

/-! ## Prefactors -/

private def fA (β : ℝ) : ℝ := 2*(1-β)/(2-β) + (1-β)^2/(2-β)^3 + 3*(1-β)^3/(2*(2-β)^5)
private def dfA (β : ℝ) : ℝ :=
  -(2*β^4-18*β^3+81*β^2-136*β+75)/(2*(2-β)^6)
private def d2fA (β : ℝ) : ℝ :=
  -(2*β^4-19*β^3+108*β^2-178*β+89)/(2-β)^7

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
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply,
    Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
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
    have h1 : HasDerivAt (fun x : ℝ => 136*x) (136:ℝ) β := by
      simpa using (hasDerivAt_id β).const_mul (136:ℝ)
    have h0 := hasDerivAt_const β (75:ℝ)
    have hs := ((((h4.sub h3).add h2).sub h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := hp.neg
  have hq := ((hd_twom β).pow 6).const_mul (2:ℝ)
  have hd := hn.div hq (by exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hne))
  refine hd.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply,
    Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  rw [d2fA]
  field_simp [hne] <;> ring

private def fQ1 (β : ℝ) : ℝ :=
  (1-β)^2*((1:ℝ)/2)/((2-β)^2*((2-β)^2+((1:ℝ)/2)^2))
    + (1-β)^3*((1:ℝ)/2)*(5*(2-β)^2+3*((1:ℝ)/2)^2)
        /(2*(2-β)^4*((2-β)^2+((1:ℝ)/2)^2)^2)
private def dfQ1 (β : ℝ) : ℝ :=
  (β-1)*(64*β^7-1008*β^6+6016*β^5-18072*β^4+29200*β^3-23975*β^2+7373*β+502)
    /((2-β)^5*64*((2-β)^2+((1:ℝ)/2)^2)^3)
private def d2fQ1 (β : ℝ) : ℝ :=
  2*(384*β^10-8064*β^9+67776*β^8-305904*β^7+811848*β^6-1254416*β^5+927344*β^4
      +166829*β^3-899831*β^2+656522*β-162238)
    /((2-β)^6*256*((2-β)^2+((1:ℝ)/2)^2)^4)

private lemma qpos : ∀ β : ℝ, ((2:ℝ)-β)^2+((1:ℝ)/2)^2 ≠ 0 := fun β => by
  have : (0:ℝ) < ((2:ℝ)-β)^2+((1:ℝ)/2)^2 := by positivity
  exact ne_of_gt this

private lemma hasDerivAt_fQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt fQ1 (dfQ1 β) β := by
  unfold fQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/2)^2 ≠ 0 := qpos β
  have hQ : (4:ℝ)*β^2-16*β+17 ≠ 0 := by nlinarith [sq_nonneg (2*β-4)]
  have ht1 := (((hd_onem β).pow 2).mul_const ((1:ℝ)/2)).div
      (((hd_twom β).pow 2).mul (((hd_twom β).pow 2).add_const (((1:ℝ)/2)^2 : ℝ)))
      (by apply mul_ne_zero (pow_ne_zero 2 hne); exact hq1d)
  have ht2 := ((((hd_onem β).pow 3).mul_const ((1:ℝ)/2)).mul
        ((((hd_twom β).pow 2).const_mul (5:ℝ)).add_const (3*((1:ℝ)/2)^2 : ℝ))).div
      ((((hd_twom β).pow 4).const_mul (2:ℝ)).mul
        ((((hd_twom β).pow 2).add_const (((1:ℝ)/2)^2 : ℝ)).pow 2))
      (by apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hne));
          exact pow_ne_zero 2 hq1d)
  have hsum := ht1.add ht2
  refine hsum.congr_deriv ?_
  rw [dfQ1]
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply,
    Pi.neg_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d, hQ]
  ring

private lemma hasDerivAt_dfQ1 {β : ℝ} (h : β ≠ 2) : HasDerivAt dfQ1 (d2fQ1 β) β := by
  unfold dfQ1
  have hne : (2:ℝ)-β ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/2)^2 ≠ 0 := qpos β
  have hQ : (4:ℝ)*β^2-16*β+17 ≠ 0 := by nlinarith [sq_nonneg (2*β-4)]
  have hA : HasDerivAt
      (fun x : ℝ => 64*x^7 - 1008*x^6 + 6016*x^5 - 18072*x^4 + 29200*x^3 - 23975*x^2 + 7373*x + 502)
      (448*β^6 - 6048*β^5 + 30080*β^4 - 72288*β^3 + 87600*β^2 - 47950*β + 7373) β := by
    have h7 := hd_mono 7 (64:ℝ) β
    have h6 := hd_mono 6 (1008:ℝ) β
    have h5 := hd_mono 5 (6016:ℝ) β
    have h4 := hd_mono 4 (18072:ℝ) β
    have h3 := hd_mono 3 (29200:ℝ) β
    have h2 := hd_mono 2 (23975:ℝ) β
    have h1 : HasDerivAt (fun x : ℝ => 7373*x) (7373:ℝ) β := by
      simpa using (hasDerivAt_id β).const_mul (7373:ℝ)
    have h0 := hasDerivAt_const β (502:ℝ)
    have hs := (((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add h1).add h0)
    refine hs.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, pow_zero, mul_one]
    ring
  have hn := (hd_sub 1 β).mul hA
  have hq := ((((hd_twom β).pow 5).mul_const (64:ℝ))).mul
      ((((hd_twom β).pow 2).add_const (((1:ℝ)/2)^2 : ℝ)).pow 3)
  have hd := hn.div hq (by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hne) (by norm_num))
    exact pow_ne_zero 3 hq1d)
  refine hd.congr_deriv ?_
  rw [d2fQ1]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply,
    Pi.neg_apply, Pi.inv_apply, Nat.reduceSub, pow_one, id_eq]
  field_simp [hne, hq1d, hQ]
  ring_nf

/-! ## log / power atoms -/

private def Kc : ℝ := ((1:ℝ)/2)*(-Real.log ((1:ℝ)/2) + 1)
private def C3 : ℝ := ((1:ℝ)/2)^3/12

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

private def T5 (β : ℝ) : ℝ := ((1:ℝ)/2)*(lg1 β) + Kc + C3*(n2 β)
private def dT5 (β : ℝ) : ℝ := ((1:ℝ)/2)*(dlg1 β) + C3*(2*(n3 β))
private def d2T5 (β : ℝ) : ℝ := ((1:ℝ)/2)*(d2lg1 β) + C3*(2*(3*(n4 β)))
private def T6a (β : ℝ) : ℝ := ((1:ℝ)/2)*(lg2 β) + Kc + C3*(m2 β)
private def dT6a (β : ℝ) : ℝ := ((1:ℝ)/2)*(dlg2 β) + C3*(-2*(m3 β))
private def d2T6a (β : ℝ) : ℝ := ((1:ℝ)/2)*(d2lg2 β) + C3*(-2*(-3*(m4 β)))

private def T6b (β : ℝ) : ℝ := β*(13/12 - Real.log β)
private def dT6b (β : ℝ) : ℝ := 1/12 - Real.log β
private def d2T6b (β : ℝ) : ℝ := -(β⁻¹)

private lemma hasDerivAt_T5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt T5 (dT5 β) β := by
  have h1 := (hasDerivAt_lg1 h).const_mul ((1:ℝ)/2)
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_n2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT5] <;> ring

private lemma hasDerivAt_dT5 {β : ℝ} (h : (2:ℝ)-β ≠ 0) : HasDerivAt dT5 (d2T5 β) β := by
  rw [show dT5 = (fun x : ℝ => ((1:ℝ)/2)*(dlg1 x) + C3*(2*(n3 x))) from rfl]
  have h1 := (hasDerivAt_dlg1 h).const_mul ((1:ℝ)/2)
  have h2 := ((hasDerivAt_n3 h).const_mul (2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T5] <;> ring

private lemma hasDerivAt_T6a {β : ℝ} (h : β ≠ 0) : HasDerivAt T6a (dT6a β) β := by
  have h1 := (hasDerivAt_lg2 h).const_mul ((1:ℝ)/2)
  have h3 : HasDerivAt (fun _ : ℝ => Kc) 0 β := hasDerivAt_const β Kc
  have h2 := (hasDerivAt_m2 h).const_mul C3
  have hsum := (h1.add h3).add h2
  refine hsum.congr_deriv ?_
  rw [dT6a] <;> ring

private lemma hasDerivAt_dT6a {β : ℝ} (h : β ≠ 0) : HasDerivAt dT6a (d2T6a β) β := by
  rw [show dT6a = (fun x : ℝ => ((1:ℝ)/2)*(dlg2 x) + C3*(-2*(m3 x))) from rfl]
  have h1 := (hasDerivAt_dlg2 h).const_mul ((1:ℝ)/2)
  have h2 := ((hasDerivAt_m3 h).const_mul (-2:ℝ)).const_mul C3
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [d2T6a] <;> ring

private lemma hasDerivAt_T6b {β : ℝ} (h : β ≠ 0) : HasDerivAt T6b (dT6b β) β := by
  unfold T6b dT6b
  have hlog : HasDerivAt Real.log β⁻¹ β := Real.hasDerivAt_log h
  have h1 : HasDerivAt (fun x : ℝ => (13:ℝ)/12 - Real.log x) (-(β⁻¹)) β := by
    simpa using hlog.const_sub ((13:ℝ)/12)
  have h2 := (hasDerivAt_id β).mul h1
  have hfun : (fun x : ℝ => x * ((13:ℝ)/12 - Real.log x))
      = id * (fun x : ℝ => (13:ℝ)/12 - Real.log x) := by
    ext x; rfl
  have hderiv : (1:ℝ) * ((13:ℝ)/12 - Real.log β) + id β * (-(β⁻¹))
      = (1:ℝ)/12 - Real.log β := by
    rw [one_mul, id]; field_simp; ring
  rw [← hfun, hderiv] at h2
  exact h2

private lemma hasDerivAt_dT6b {β : ℝ} (h : β ≠ 0) : HasDerivAt dT6b (d2T6b β) β := by
  unfold dT6b d2T6b
  have hlog : HasDerivAt Real.log β⁻¹ β := Real.hasDerivAt_log h
  have h1 : HasDerivAt (fun x : ℝ => (1:ℝ)/12 - Real.log x) (-(β⁻¹)) β := by
    simpa using hlog.const_sub ((1:ℝ)/12)
  simpa using h1

/-! ## The main functions and their derivatives -/

private def E1 (β : ℝ) : ℝ :=
  ((13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)) - (T5 β + T6a β)
private def Df1 (β : ℝ) : ℝ :=
  ((13/5)*(dat1 β + dat2 β) + ((dfA β * at3 β + fA β * dat3 β) + dfQ1 β))
    - (dT5 β + dT6a β)
private def E2f1 (β : ℝ) : ℝ :=
  ((13/5)*(d2at1 β + d2at2 β)
    + (((d2fA β * at3 β + 2*(dfA β * dat3 β)) + fA β * d2at3 β) + d2fQ1 β))
  - (d2T5 β + d2T6a β)

private def E2f0 (β : ℝ) : ℝ :=
  ((13/5)*(d2at1 β + d2at2 β)
    + (((d2fA β * at3 β + 2*(dfA β * dat3 β)) + fA β * d2at3 β) + d2fQ1 β))
  - (d2T5 β + d2T6b β)

private def E0 (β : ℝ) : ℝ :=
  ((13/5)*(at1 β + at2 β) + (fA β * at3 β + fQ1 β)) - (T5 β + T6b β)
private def Df0 (β : ℝ) : ℝ :=
  ((13/5)*(dat1 β + dat2 β) + ((dfA β * at3 β + fA β * dat3 β) + dfQ1 β))
    - (dT5 β + dT6b β)

private lemma hasDerivAt_E1 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1)
    (h2 : β ≠ 2) (h0 : β ≠ 0) : HasDerivAt E1 (Df1 β) β := by
  have hE : E1 = fun x : ℝ =>
      ((13/5)*(at1 x + at2 x) + (fA x * at3 x + fQ1 x)) - (T5 x + T6a x) :=
    funext (fun x => rfl)
  rw [hE]
  have h1 := ((hasDerivAt_at1 h32).add (hasDerivAt_at2 hm1)).const_mul (13/5)
  have h2' := ((hasDerivAt_fA h2).mul (hasDerivAt_at3 h2)).add (hasDerivAt_fQ1 h2)
  have h3' := (hasDerivAt_T5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_T6a h0)
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [Df1] <;> ring

private lemma hasDerivAt_Df1 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1)
    (h2 : β ≠ 2) (h0 : β ≠ 0) : HasDerivAt Df1 (E2f1 β) β := by
  have hD : Df1 = fun x : ℝ =>
      ((13/5)*(dat1 x + dat2 x) + ((dfA x * at3 x + fA x * dat3 x) + dfQ1 x))
        - (dT5 x + dT6a x) := funext (fun x => rfl)
  rw [hD]
  have h1 := ((hasDerivAt_dat1 β).add (hasDerivAt_dat2 β)).const_mul (13/5)
  have h2' := (((hasDerivAt_dfA h2).mul (hasDerivAt_at3 h2)).add
      ((hasDerivAt_fA h2).mul (hasDerivAt_dat3 β))).add (hasDerivAt_dfQ1 h2)
  have h3' := ((hasDerivAt_dT5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_dT6a h0))
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [E2f1] <;> ring

private lemma hasDerivAt_E0 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1)
    (h2 : β ≠ 2) (h0 : β ≠ 0) : HasDerivAt E0 (Df0 β) β := by
  have hE : E0 = fun x : ℝ =>
      ((13/5)*(at1 x + at2 x) + (fA x * at3 x + fQ1 x)) - (T5 x + T6b x) :=
    funext (fun x => rfl)
  rw [hE]
  have h1 := ((hasDerivAt_at1 h32).add (hasDerivAt_at2 hm1)).const_mul (13/5)
  have h2' := ((hasDerivAt_fA h2).mul (hasDerivAt_at3 h2)).add (hasDerivAt_fQ1 h2)
  have h3' := (hasDerivAt_T5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_T6b h0)
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [Df0] <;> ring

private lemma hasDerivAt_Df0 {β : ℝ} (h32 : β ≠ 3/2) (hm1 : β ≠ -1)
    (h2 : β ≠ 2) (h0 : β ≠ 0) : HasDerivAt Df0 (E2f0 β) β := by
  have hD : Df0 = fun x : ℝ =>
      ((13/5)*(dat1 x + dat2 x) + ((dfA x * at3 x + fA x * dat3 x) + dfQ1 x))
        - (dT5 x + dT6b x) := funext (fun x => rfl)
  rw [hD]
  have h1 := ((hasDerivAt_dat1 β).add (hasDerivAt_dat2 β)).const_mul (13/5)
  have h2' := (((hasDerivAt_dfA h2).mul (hasDerivAt_at3 h2)).add
      ((hasDerivAt_fA h2).mul (hasDerivAt_dat3 β))).add (hasDerivAt_dfQ1 h2)
  have h3' := ((hasDerivAt_dT5 (sub_ne_zero.mpr (Ne.symm h2))).add (hasDerivAt_dT6b h0))
  have hall := (h1.add h2').sub h3'
  refine hall.congr_deriv ?_
  rw [E2f0] <;> ring

/-! ## Decomposition of the second derivative -/

private def P1f (β : ℝ) : ℝ := (13/5)*(d2at1 β + d2at2 β)
private def ARred (β : ℝ) : ℝ :=
  2*(dfA β * dat3 β) + fA β * d2at3 β + d2fQ1 β
    + d2fA β * (((1:ℝ)/2)/(2-β))
private def LGf1 (β : ℝ) : ℝ := -(d2T5 β + d2T6a β)
private def LGf0 (β : ℝ) : ℝ := -(d2T5 β + d2T6b β)

private lemma E2f1_decomp (β : ℝ) :
    E2f1 β = P1f β + ARred β + LGf1 β + d2fA β * (at3 β - ((1:ℝ)/2)/(2-β)) := by
  unfold E2f1 P1f ARred LGf1; ring

private lemma E2f0_decomp (β : ℝ) :
    E2f0 β = P1f β + ARred β + LGf0 β + d2fA β * (at3 β - ((1:ℝ)/2)/(2-β)) := by
  unfold E2f0 P1f ARred LGf0; ring

/-! ## Polynomial certificates -/

private def DEN (β : ℝ) : ℝ :=
  2*(β-2)^8*(2*β^2-6*β+5)^2*(4*β^2-16*β+17)^4*(4*β^2+8*β+5)^2

private def NUM (β : ℝ) : ℝ :=
  ((54665749735 : ℝ)/1)*(1-β)^21
  + ((679834334689 : ℝ)/1)*β^1*(1-β)^20
  + ((4000664841054 : ℝ)/1)*β^2*(1-β)^19
  + ((14867163218317 : ℝ)/1)*β^3*(1-β)^18
  + ((39232059214707 : ℝ)/1)*β^4*(1-β)^17
  + ((78315547610246 : ℝ)/1)*β^5*(1-β)^16
  + ((122972785036424 : ℝ)/1)*β^6*(1-β)^15
  + ((155884670714976 : ℝ)/1)*β^7*(1-β)^14
  + ((162398153044138 : ℝ)/1)*β^8*(1-β)^13
  + ((140731356071350 : ℝ)/1)*β^9*(1-β)^12
  + ((102204960862204 : ℝ)/1)*β^10*(1-β)^11
  + ((62413171329562 : ℝ)/1)*β^11*(1-β)^10
  + ((32029816095954 : ℝ)/1)*β^12*(1-β)^9
  + ((13751808930328 : ℝ)/1)*β^13*(1-β)^8
  + ((4897335889592 : ℝ)/1)*β^14*(1-β)^7
  + ((1427544286264 : ℝ)/1)*β^15*(1-β)^6
  + ((334127434639 : ℝ)/1)*β^16*(1-β)^5
  + ((61084155185 : ℝ)/1)*β^17*(1-β)^4
  + ((8370633446 : ℝ)/1)*β^18*(1-β)^3
  + ((804864065 : ℝ)/1)*β^19*(1-β)^2
  + ((48110875 : ℝ)/1)*β^20*(1-β)^1
  + ((1332250 : ℝ)/1)*β^21

private lemma DEN_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < DEN β := by
  have h2ne : β - 2 ≠ 0 := by linarith
  have h4 : (0:ℝ) < (β-2)^8 := by
    have he : (β-2)^8 = ((β-2)^2)^4 := by ring
    rw [he]; exact pow_pos (sq_pos_of_ne_zero h2ne) 4
  have hq1 : (0:ℝ) < 2*β^2-6*β+5 := by nlinarith [sq_nonneg (β - 3/2)]
  have hq2 : (0:ℝ) < 4*β^2-16*β+17 := by nlinarith [sq_nonneg (2*β-4)]
  have hq3 : (0:ℝ) < 4*β^2+8*β+5 := by nlinarith [sq_nonneg (2*β+2)]
  unfold DEN
  positivity

private lemma P1_ARred_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ P1f β + ARred β := by
  have hDEN := DEN_pos hβ0 hβ1
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have h32b : ((3:ℝ)/2-β)^2+((1:ℝ)/2)^2 ≠ 0 := by
    have : (0:ℝ) < ((3:ℝ)/2-β)^2+((1:ℝ)/2)^2 := by positivity
    exact ne_of_gt this
  have h1pb : ((1:ℝ)+β)^2+((1:ℝ)/2)^2 ≠ 0 := by
    have : (0:ℝ) < ((1:ℝ)+β)^2+((1:ℝ)/2)^2 := by positivity
    exact ne_of_gt this
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/2)^2 ≠ 0 := qpos β
  have hQ : (4:ℝ)*β^2-16*β+17 ≠ 0 := by nlinarith [sq_nonneg (2*β-4)]
  have hkey : (P1f β + ARred β) * DEN β = NUM β := by
    unfold P1f ARred DEN NUM fA dfA d2fA d2fQ1 d2at1 d2at2 dat3 d2at3
    field_simp [h2b, h32b, h1pb, hq1d, hQ]
    ring
  have hb : (0:ℝ) ≤ β := le_of_lt hβ0
  have h1b : (0:ℝ) ≤ 1-β := by linarith
  have hNUM : 0 ≤ NUM β := by unfold NUM; positivity
  have hNUM' : 0 ≤ (P1f β + ARred β) * DEN β := by rw [hkey]; exact hNUM
  exact nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hNUM') hDEN

private def DEN2 (β : ℝ) : ℝ :=
  1200*(β-2)^6*(2*β^2-6*β+5)*(4*β^2-16*β+17)^3*(4*β^2+8*β+5)

private def NUM2 (β : ℝ) : ℝ :=
  ((9230666200 : ℝ)/1)*(1-2*β)^16
  + ((112083311850 : ℝ)/1)*(2*β)^1*(1-2*β)^15
  + ((1269210654195 : ℝ)/2)*(2*β)^2*(1-2*β)^14
  + ((17781534848491 : ℝ)/8)*(2*β)^3*(1-2*β)^13
  + ((10772752262759 : ℝ)/2)*(2*β)^4*(1-2*β)^12
  + ((153090430303875 : ℝ)/16)*(2*β)^5*(1-2*β)^11
  + ((205972232826315 : ℝ)/16)*(2*β)^6*(1-2*β)^10
  + ((213790689039707 : ℝ)/16)*(2*β)^7*(1-2*β)^9
  + ((86334678020583 : ℝ)/8)*(2*β)^8*(1-2*β)^8
  + ((13571967304321 : ℝ)/2)*(2*β)^9*(1-2*β)^7
  + ((13191845062797 : ℝ)/4)*(2*β)^10*(1-2*β)^6
  + ((1218373849989 : ℝ)/1)*(2*β)^11*(1-2*β)^5
  + ((664318884195 : ℝ)/2)*(2*β)^12*(1-2*β)^4
  + ((63492350375 : ℝ)/1)*(2*β)^13*(1-2*β)^3
  + ((7746364350 : ℝ)/1)*(2*β)^14*(1-2*β)^2
  + ((491351625 : ℝ)/1)*(2*β)^15*(1-2*β)^1
  + ((7830000 : ℝ)/1)*(2*β)^16

private lemma DEN2_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < DEN2 β := by
  have h2ne : β - 2 ≠ 0 := by linarith
  have h4 : (0:ℝ) < (β-2)^6 := by
    have he : (β-2)^6 = ((β-2)^2)^3 := by ring
    rw [he]; exact pow_pos (sq_pos_of_ne_zero h2ne) 3
  have hq1 : (0:ℝ) < 2*β^2-6*β+5 := by nlinarith [sq_nonneg (β - 3/2)]
  have hq2 : (0:ℝ) < 4*β^2-16*β+17 := by nlinarith [sq_nonneg (2*β-4)]
  have hq3 : (0:ℝ) < 4*β^2+8*β+5 := by nlinarith [sq_nonneg (2*β+2)]
  unfold DEN2; positivity

private lemma S_le_seven_tenths {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) :
    (13/5)*(dat1 β + dat2 β) + fA β * dat3 β + dfQ1 β - dT5 β + (6/25)*dfA β ≤ 7/10 := by
  have hDEN := DEN2_pos hβ0 (by linarith)
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have h32b : ((3:ℝ)/2-β)^2+((1:ℝ)/2)^2 ≠ 0 := by
    have : (0:ℝ) < ((3:ℝ)/2-β)^2+((1:ℝ)/2)^2 := by positivity
    exact ne_of_gt this
  have h1pb : ((1:ℝ)+β)^2+((1:ℝ)/2)^2 ≠ 0 := by
    have : (0:ℝ) < ((1:ℝ)+β)^2+((1:ℝ)/2)^2 := by positivity
    exact ne_of_gt this
  have hq1d : ((2:ℝ)-β)^2+((1:ℝ)/2)^2 ≠ 0 := qpos β
  have hQ : (4:ℝ)*β^2-16*β+17 ≠ 0 := by nlinarith [sq_nonneg (2*β-4)]
  have hkey : ((13/5)*(dat1 β + dat2 β) + fA β * dat3 β + dfQ1 β - dT5 β
      + (6/25)*dfA β - 7/10) * DEN2 β = - NUM2 β := by
    unfold DEN2 NUM2 dat1 dat2 dat3 fA dfA dfQ1 dT5 dlg1 n3 C3
    field_simp [h2b, h32b, h1pb, hq1d, hQ]
    ring_nf
  have hb : (0:ℝ) ≤ 2*β := by linarith
  have h1b : (0:ℝ) ≤ 1-2*β := by linarith
  have hNUM : 0 ≤ NUM2 β := by unfold NUM2; positivity
  have hle : ((13/5)*(dat1 β + dat2 β) + fA β * dat3 β + dfQ1 β - dT5 β
      + (6/25)*dfA β - 7/10) * DEN2 β ≤ 0 := by rw [hkey]; linarith
  have := nonpos_of_mul_nonpos_left hle hDEN
  linarith

/-! ## Elementary sign facts -/

private lemma d2fA_nonpos {β : ℝ} (h : β ≤ 1) : d2fA β ≤ 0 := by
  unfold d2fA
  have h1 : (0:ℝ) ≤ 1-β := by linarith
  have h2 : (0:ℝ) ≤ 2*β^2-15*β+76 := by nlinarith [sq_nonneg (4*β-15)]
  have h3 : (0:ℝ) ≤ 11 + (1-β)*(2*β^2-15*β+76) := by
    nlinarith [mul_nonneg h1 h2]
  have hp : (0:ℝ) < 2*β^4-19*β^3+108*β^2-178*β+89 := by
    have hkey : 2*β^4-19*β^3+108*β^2-178*β+89 = 2 + (1-β)*(11+(1-β)*(2*β^2-15*β+76)) := by ring
    nlinarith [mul_nonneg h1 h3]
  have hd : (0:ℝ) < (2-β)^7 := pow_pos (by linarith) 7
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hd)

private lemma dfA_neg {β : ℝ} (h : β ≤ 1) : dfA β < 0 := by
  unfold dfA
  have hu : (0:ℝ) ≤ 1-β := by linarith
  have hp : (0:ℝ) < 2*β^4-18*β^3+81*β^2-136*β+75 := by
    have hkey : 2*β^4-18*β^3+81*β^2-136*β+75
        = 2*(1-β)^4 + 10*(1-β)^3 + 39*(1-β)^2 + 20*(1-β) + 4 := by ring
    rw [hkey]; positivity
  have hd : (0:ℝ) < 2*(2-β)^6 := by
    have : (0:ℝ) < 2-β := by linarith
    positivity
  exact div_neg_of_neg_of_pos (by linarith) hd

private lemma at3_le {β : ℝ} (h : β ≤ 1) : at3 β ≤ ((1:ℝ)/2)/(2-β) := by
  unfold at3
  apply Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg
  apply div_nonneg (by norm_num); linarith

private lemma at3_ge {β : ℝ} (hβ0 : 0 < β) (h : β ≤ 1/2) : (6:ℝ)/25 ≤ at3 β := by
  unfold at3
  have hx : (1:ℝ)/4 ≤ ((1:ℝ)/2)/(2-β) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2-β)]; linarith
  have h14 : (6:ℝ)/25 ≤ Real.arctan ((1:ℝ)/4) := by
    have hp := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_lower_poly_of_nonneg
      (x := (1:ℝ)/4) (by norm_num)
    have h2 : (6:ℝ)/25 ≤ (1:ℝ)/4 - ((1:ℝ)/4)^3/3 := by norm_num
    linarith
  exact le_trans h14 (Real.arctan_mono hx)

private lemma LGf1_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : (1:ℝ)/2 ≤ β) (hβ2 : β < 1) : 0 ≤ LGf1 β := by
  have h2 : (0:ℝ) < 2-β := by linarith
  have hkey : LGf1 β = (8*(2-β)^2-1)/(16*(2-β)^4) + (8*β^2-1)/(16*β^4) := by
    unfold LGf1 d2T5 d2T6a C3 d2lg1 d2lg2 n4 m4
    field_simp
    ring
  rw [hkey]
  have h1 : (0:ℝ) < 8*(2-β)^2-1 := by nlinarith [sq_nonneg (2-β)]
  have h2' : (0:ℝ) < 8*β^2-1 := by nlinarith [sq_nonneg β]
  have h3 : (0:ℝ) < 16*(2-β)^4 := by positivity
  have h4 : (0:ℝ) < 16*β^4 := by positivity
  positivity

private lemma LGf0_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 1) : 0 ≤ LGf0 β := by
  have h2 : (0:ℝ) < 2-β := by linarith
  have hkey : LGf0 β = (8*(2-β)^2-1)/(16*(2-β)^4) + 1/β := by
    unfold LGf0 d2T5 d2T6b C3 d2lg1 n4
    field_simp
    ring
  rw [hkey]
  have h1 : (0:ℝ) < 8*(2-β)^2-1 := by nlinarith [sq_nonneg (2-β)]
  have h3 : (0:ℝ) < 16*(2-β)^4 := by positivity
  positivity

private lemma E2f1_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : (1:ℝ)/2 ≤ β) (hβ2 : β < 1) :
    0 ≤ E2f1 β := by
  have hPA := P1_ARred_nonneg hβ0 hβ2
  have hLG := LGf1_nonneg hβ0 hβ1 hβ2
  have hd2 : d2fA β ≤ 0 := d2fA_nonpos (le_of_lt hβ2)
  have hat := at3_le (le_of_lt hβ2)
  have hprod : 0 ≤ d2fA β * (at3 β - ((1:ℝ)/2)/(2-β)) :=
    mul_nonneg_of_nonpos_of_nonpos hd2 (by linarith)
  rw [E2f1_decomp]; linarith

private lemma E2f0_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ E2f0 β := by
  have hPA := P1_ARred_nonneg hβ0 hβ1
  have hLG := LGf0_nonneg hβ0 hβ1
  have hd2 : d2fA β ≤ 0 := d2fA_nonpos (le_of_lt hβ1)
  have hat := at3_le (le_of_lt hβ1)
  have hprod : 0 ≤ d2fA β * (at3 β - ((1:ℝ)/2)/(2-β)) :=
    mul_nonneg_of_nonpos_of_nonpos hd2 (by linarith)
  rw [E2f0_decomp]; linarith

/-! ## Convexity of `E1` -/

private lemma nbd_Ioo {a b x : ℝ} (hx : x ∈ Set.Ioo a b) : Set.Ioo a b ∈ 𝓝 x :=
  isOpen_Ioo.mem_nhds hx

private lemma hasDerivAt_E1_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/2:ℝ) (9/8)) :
    HasDerivAt E1 (Df1 x) x :=
  hasDerivAt_E1 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_Df1_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1/2:ℝ) (9/8)) :
    HasDerivAt Df1 (E2f1 x) x :=
  hasDerivAt_Df1 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma hasDerivAt_E0_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) (1/2)) :
    HasDerivAt E0 (Df0 x) x :=
  hasDerivAt_E0 (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.1])

private lemma differentiableOn_E1 : DifferentiableOn ℝ E1 (Set.Icc (1/2:ℝ) 1) := by
  intro x hx
  exact (hasDerivAt_E1 (by linarith [hx.2]) (by linarith [hx.1])
    (by linarith [hx.2]) (by linarith [hx.1])).differentiableAt.differentiableWithinAt

private lemma differentiableOn_deriv_E1 : DifferentiableOn ℝ (deriv E1) (Set.Ioo (1/2:ℝ) 1) := by
  intro x hx
  have hev : deriv E1 =ᶠ[𝓝 x] Df1 := by
    filter_upwards [nbd_Ioo (a := (1/2:ℝ)) (b := (9/8:ℝ))
      ⟨by linarith [hx.1], by linarith [hx.2]⟩] with y hy
    exact (hasDerivAt_E1_Ioo hy).deriv
  have h1 : DifferentiableAt ℝ (deriv E1) x := by
    rw [hev.differentiableAt_iff]
    exact (hasDerivAt_Df1_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt
  exact h1.differentiableWithinAt

private lemma second_deriv_E1_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (1/2:ℝ) 1) :
    0 ≤ deriv^[2] E1 x := by
  have hev : deriv E1 =ᶠ[𝓝 x] Df1 := by
    filter_upwards [nbd_Ioo (a := (1/2:ℝ)) (b := (9/8:ℝ))
      ⟨by linarith [hx.1], by linarith [hx.2]⟩] with y hy
    exact (hasDerivAt_E1_Ioo hy).deriv
  have hdd : deriv (deriv E1) x = E2f1 x := by
    rw [hev.deriv_eq]
    exact (hasDerivAt_Df1_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).deriv
  change 0 ≤ deriv (deriv E1) x
  rw [hdd]
  exact E2f1_nonneg (by linarith [hx.1]) (le_of_lt hx.1) hx.2

private lemma convexOn_E1 : ConvexOn ℝ (Set.Icc (1/2:ℝ) 1) E1 := by
  refine convexOn_of_deriv2_nonneg (convex_Icc _ _) differentiableOn_E1.continuousOn ?_ ?_ ?_
  · rw [interior_Icc]; exact differentiableOn_E1.mono Set.Ioo_subset_Icc_self
  · rw [interior_Icc]; exact differentiableOn_deriv_E1
  · intro x hx
    rw [interior_Icc] at hx
    exact second_deriv_E1_nonneg hx

private lemma deriv_E1_at_35 : deriv E1 (3/5) = Df1 (3/5) :=
  (hasDerivAt_E1_Ioo (by norm_num)).deriv

private lemma E1_tangent {β : ℝ} (h1 : (1:ℝ)/2 ≤ β) (h2 : β ≤ 1) :
    E1 (3/5) + Df1 (3/5) * (β - 3/5) ≤ E1 β := by
  have hmem : β ∈ Set.Icc (1/2:ℝ) 1 := ⟨h1, h2⟩
  have hmem2 : (3/5:ℝ) ∈ Set.Icc (1/2:ℝ) 1 := by norm_num
  have hdiff : DifferentiableAt ℝ E1 (3/5) := (hasDerivAt_E1_Ioo (by norm_num)).differentiableAt
  rcases lt_trichotomy β (3/5) with hlt | heq | hgt
  · have hsl := convexOn_E1.slope_le_deriv hmem hmem2 hlt hdiff
    rw [slope_def_field, deriv_E1_at_35] at hsl
    have hpos : (0:ℝ) < 3/5 - β := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith
  · subst heq; simp
  · have hsl := convexOn_E1.deriv_le_slope hmem2 hmem hgt hdiff
    rw [slope_def_field, deriv_E1_at_35] at hsl
    have hpos : (0:ℝ) < β - 3/5 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsl (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    linarith

/-! ## Numeric bounds -/

private lemma log_seven_fifths_le : Real.log ((7:ℝ)/5) ≤ (33654/100000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-2:ℝ)/5)) (by norm_num) 10
  have heq : Real.log ((7:ℝ)/5) = Real.log (1 - ((-2:ℝ)/5)) := by congr 1; norm_num
  rw [heq]
  have hub : Real.log ((7:ℝ)/5) ≤
      -(∑ i ∈ Finset.range 10, ((-2:ℝ)/5)^(i+1)/(i+1)) + (2/5)^11/(1-2/5) := by
    have h2 := (abs_le.mp h).2; linarith
  have hkey : -(∑ i ∈ Finset.range 10, ((-2:ℝ)/5)^(i+1)/(i+1)) + (2/5)^11/(1-2/5)
      ≤ (33654/100000:ℝ) := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_six_fifths_le : Real.log ((6:ℝ)/5) ≤ (1824/10000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-1:ℝ)/5)) (by norm_num) 8
  have heq : Real.log ((6:ℝ)/5) = Real.log (1 - ((-1:ℝ)/5)) := by congr 1; norm_num
  rw [heq]
  have hub : Real.log ((6:ℝ)/5) ≤
      -(∑ i ∈ Finset.range 8, ((-1:ℝ)/5)^(i+1)/(i+1)) + (1/5)^9/(1-1/5) := by
    have h2 := (abs_le.mp h).2; linarith
  have hkey : -(∑ i ∈ Finset.range 8, ((-1:ℝ)/5)^(i+1)/(i+1)) + (1/5)^9/(1-1/5)
      ≤ (1824/10000:ℝ) := by norm_num [Finset.sum_range_succ]
  linarith

private lemma log_fourteen_fifths_le : Real.log ((14:ℝ)/5) ≤ (10297/10000:ℝ) := by
  have h1 : Real.log ((14:ℝ)/5) = Real.log 2 + Real.log ((7:ℝ)/5) := by
    rw [show (14:ℝ)/5 = 2*((7:ℝ)/5) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h1]
  have h2 : Real.log 2 ≤ (0.6931471808:ℝ) := le_of_lt Real.log_two_lt_d9
  have h3 := log_seven_fifths_le
  linarith

private lemma arctan_five_sixteenths_lower : (3028/10000:ℝ) ≤ Real.arctan (5/16) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((5:ℝ)/16) (by norm_num)
  have hpoly : (3028/10000:ℝ) ≤
      (5/16 : ℝ) - (5/16)^3/3 + (5/16)^5/5 - (5/16)^7/7 + (5/16)^9/9 - (5/16)^11/11
        + (5/16)^13/13 - (5/16)^15/15 := by norm_num
  linarith

private lemma arctan_five_fourteenths_lower : (3430/10000:ℝ) ≤ Real.arctan (5/14) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 ((5:ℝ)/14) (by norm_num)
  have hpoly : (3430/10000:ℝ) ≤
      (5/14 : ℝ) - (5/14)^3/3 + (5/14)^5/5 - (5/14)^7/7 + (5/14)^9/9 - (5/14)^11/11
        + (5/14)^13/13 - (5/14)^15/15 := by norm_num
  linarith

private lemma arctan_five_fourteenths_upper : Real.arctan (5/14) ≤ (3431/10000:ℝ) := by
  have h := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le4 ((5:ℝ)/14) (by norm_num)
  have hpoly : (5/14 : ℝ) - (5/14)^3/3 + (5/14)^5/5 - (5/14)^7/7 + (5/14)^9/9
      ≤ (3431/10000:ℝ) := by norm_num
  linarith

private lemma E1_at_35_lower : (1:ℝ)/50 ≤ E1 (3/5) := by
  have ha1 : at1 (3/5) = Real.arctan (5/9) := by unfold at1; norm_num
  have ha2 : at2 (3/5) = Real.arctan (5/16) := by unfold at2; norm_num
  have ha3 : at3 (3/5) = Real.arctan (5/14) := by unfold at3; norm_num
  have hfA : fA (3/5) = (10884:ℝ)/16807 := by unfold fA; norm_num
  have hfQ1 : fQ1 (3/5) = (3220800:ℝ)/117267241 := by unfold fQ1; norm_num
  have hl1 : lg1 (3/5) = Real.log (14/5) := by unfold lg1; norm_num
  have hl2 : lg2 (3/5) = Real.log (6/5) := by unfold lg2; norm_num
  have hn2 : n2 (3/5) = (25:ℝ)/49 := by unfold n2; norm_num
  have hm2 : m2 (3/5) = (25:ℝ)/9 := by unfold m2; norm_num
  have hE : E1 (3/5) = (13/5)*(Real.arctan (5/9) + Real.arctan (5/16))
      + ((10884:ℝ)/16807)*Real.arctan (5/14) + (3220800:ℝ)/117267241
      - ((1:ℝ)/2)*Real.log (14/5) - ((1:ℝ)/2)*Real.log (6/5)
      - (1 + Real.log 2) - ((1:ℝ)/96)*((25:ℝ)/49 + (25:ℝ)/9) := by
    unfold E1 T5 T6a Kc C3
    rw [ha1, ha2, ha3, hfA, hfQ1, hl1, hl2, hn2, hm2]
    have hl12 : Real.log ((1:ℝ)/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hl12]; ring
  rw [hE]
  have hA1 := Commons.Analysis.SpecialFunctions.Trigonometric.arctan_five_ninths_lower
  have hA2 := arctan_five_sixteenths_lower
  have hA3 := arctan_five_fourteenths_lower
  have hL1 := log_fourteen_fifths_le
  have hL2 := log_six_fifths_le
  have hL0 : Real.log 2 ≤ (0.6931471808:ℝ) := le_of_lt Real.log_two_lt_d9
  linarith

private lemma Df1_at_35_bounds : 0 ≤ Df1 (3/5) ∧ Df1 (3/5) ≤ (1:ℝ)/50 := by
  have hd1 : dat1 (3/5) = (25:ℝ)/53 := by unfold dat1; norm_num
  have hd2 : dat2 (3/5) = -(50:ℝ)/281 := by unfold dat2; norm_num
  have hd3 : dat3 (3/5) = (50:ℝ)/221 := by unfold dat3; norm_num
  have hfA : fA (3/5) = (10884:ℝ)/16807 := by unfold fA; norm_num
  have hdfA : dfA (3/5) = -(147900:ℝ)/117649 := by unfold dfA; norm_num
  have hdfQ1 : dfQ1 (3/5) = -(13328814500:ℝ)/181412421827 := by unfold dfQ1; norm_num
  have hdT5 : dT5 (3/5) = -(5755:ℝ)/16464 := by unfold dT5 dlg1 n3 C3; norm_num
  have hdT6a : dT6a (3/5) = (955:ℝ)/1296 := by unfold dT6a dlg2 m3 C3; norm_num
  have ha3 : at3 (3/5) = Real.arctan (5/14) := by unfold at3; norm_num
  have hE : Df1 (3/5) = (13/5)*((25:ℝ)/53 - (50:ℝ)/281) + (-(147900:ℝ)/117649)*Real.arctan (5/14)
      + ((10884:ℝ)/16807)*((50:ℝ)/221) + (-(13328814500:ℝ)/181412421827)
      - (-(5755:ℝ)/16464) - (955:ℝ)/1296 := by
    unfold Df1
    rw [hd1, hd2, hd3, hfA, hdfA, hdfQ1, hdT5, hdT6a, ha3]
    ring
  rw [hE]
  have hA3lo := arctan_five_fourteenths_lower
  have hA3hi := arctan_five_fourteenths_upper
  constructor <;> linarith

/-! ## Monotonicity of `E0` on `(0,1/2]` -/

private lemma Df0_nonpos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) : Df0 β ≤ 0 := by
  have hS := S_le_seven_tenths hβ0 hβ1
  have hdfA : dfA β < 0 := dfA_neg (by linarith)
  have hat3 := at3_ge hβ0 hβ1
  have hstep : dfA β * at3 β ≤ dfA β * ((6:ℝ)/25) :=
    mul_le_mul_of_nonpos_left hat3 (le_of_lt hdfA)
  have hlog : Real.log β ≤ -(0.6931471803:ℝ) := by
    have h1 : Real.log β ≤ Real.log ((1:ℝ)/2) := Real.log_le_log hβ0 hβ1
    have h2 : Real.log ((1:ℝ)/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    have h3 : (0.6931471803:ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
    linarith
  have hD0 : Df0 β = ((13/5)*(dat1 β + dat2 β) + fA β * dat3 β + dfQ1 β - dT5 β)
      + dfA β * at3 β + Real.log β - 1/12 := by
    unfold Df0 dT6b; ring
  rw [hD0]; linarith

private lemma antitoneOn_E0 : AntitoneOn E0 (Set.Ioc (0:ℝ) (1/2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) ?_ ?_ ?_
  · intro x hx
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · exact (hasDerivAt_E0_Ioo ⟨hx.1, hlt⟩).continuousAt.continuousWithinAt
    · subst heq
      exact (hasDerivAt_E0 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_E0_Ioo hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hasDerivAt_E0_Ioo hx).deriv]
    exact Df0_nonpos (by linarith [hx.1]) (le_of_lt hx.2)

theorem WJ_pair_half_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (let W : ℝ → ℝ := fun t : ℝ => (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β)) + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*(t)/((2-β)^2+(t)^2))/(2*(2-β)^3)) + ((2-β)^2-β^2)^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5) + (t)*(5*(2-β)^2+3*(t)^2)/(8*(2-β)^4*((2-β)^2+(t)^2)^2)) - ((t)*(Real.log (2*(2-β)) - Real.log (t) + 1) + (t)^3/(12*(2-β)^2)) - (if (t) ≤ β then (t)*(Real.log (2*β) - Real.log (t) + 1) + (t)^3/(12*β^2) else β*(Real.log 2 + 13/12) + β*Real.log ((t)/β));
    (1:ℝ)/30 ≤ W (1/2) + W (1/2)) := by
  let Wf : ℝ → ℝ := fun t : ℝ => (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β)) + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*(t)/((2-β)^2+(t)^2))/(2*(2-β)^3)) + ((2-β)^2-β^2)^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5) + (t)*(5*(2-β)^2+3*(t)^2)/(8*(2-β)^4*((2-β)^2+(t)^2)^2)) - ((t)*(Real.log (2*(2-β)) - Real.log (t) + 1) + (t)^3/(12*(2-β)^2)) - (if (t) ≤ β then (t)*(Real.log (2*β) - Real.log (t) + 1) + (t)^3/(12*β^2) else β*(Real.log 2 + 13/12) + β*Real.log ((t)/β))
  change (1:ℝ)/30 ≤ Wf (1/2) + Wf (1/2)
  have hWfn : (1:ℝ)/60 ≤ (if (1/2:ℝ) ≤ β then E1 β else E0 β) := by
    by_cases hb : (1/2:ℝ) ≤ β
    · rw [if_pos hb]
      have htan := E1_tangent hb (le_of_lt hβ1)
      have h35 := E1_at_35_lower
      have hslo := Df1_at_35_bounds.1
      have hshi := Df1_at_35_bounds.2
      have hb2 : -(1:ℝ)/10 ≤ β - 3/5 := by linarith
      nlinarith [htan, h35, hslo, hshi, hb2]
    · rw [if_neg hb]
      have hlt : β < 1/2 := not_le.mp hb
      have hanti : E0 (1/2) ≤ E0 β :=
        antitoneOn_E0 ⟨hβ0, le_of_lt hlt⟩ ⟨by norm_num, le_refl _⟩ (le_of_lt hlt)
      have hhalf : (1:ℝ)/60 ≤ E1 (1/2) := by
        have htan := E1_tangent (β := (1:ℝ)/2) (by norm_num) (by norm_num)
        have h35 := E1_at_35_lower
        have hslo := Df1_at_35_bounds.1
        have hshi := Df1_at_35_bounds.2
        nlinarith [htan, h35, hslo, hshi]
      have heq : E0 (1/2) = E1 (1/2) := by
        have h : T6a (1/2) = T6b (1/2) := by
          unfold T6a T6b lg2 Kc C3 m2
          have hlog : Real.log (2*(1/2:ℝ)) = 0 := by
            rw [show (2:ℝ)*(1/2) = 1 by norm_num, Real.log_one]
          rw [hlog]; ring
        unfold E0 E1
        rw [h]
      linarith [hanti, hhalf, heq]
  have hkey : Wf (1/2) = (if (1/2:ℝ) ≤ β then E1 β else E0 β) := by
    have h2b : (2:ℝ)-β ≠ 0 := by linarith
    have h32b : (3:ℝ)/2-β ≠ 0 := by linarith
    have h1pb : (1:ℝ)+β ≠ 0 := by linarith
    have hb0 : β ≠ 0 := by linarith
    have hqd : ((2:ℝ)-β)^2+((1:ℝ)/2)^2 ≠ 0 := qpos β
    by_cases hb : (1/2:ℝ) ≤ β
    · dsimp only [Wf]
      simp only [if_pos hb]
      unfold E1 at1 at2 at3 fA fQ1 T5 T6a lg1 lg2 n2 m2 Kc C3
      field_simp [h2b, h32b, h1pb, hb0, hqd]
      ring
    · dsimp only [Wf]
      simp only [if_neg hb]
      unfold E0 at1 at2 at3 fA fQ1 T5 T6b lg1 n2 Kc C3
      rw [Real.log_div (by norm_num) hb0]
      rw [show Real.log ((1:ℝ)/2) = -Real.log 2 by rw [one_div, Real.log_inv]]
      field_simp [h2b, h32b, h1pb, hb0, hqd]
      ring
  rw [hkey]
  linarith [hWfn]

end

end Commons.Analysis.Real
