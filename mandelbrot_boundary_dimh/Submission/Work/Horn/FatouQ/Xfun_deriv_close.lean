import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.FatouQ.chartdict
import Submission.Work.Horn.FatouQ.zBranch_contDiff
import Submission.Work.Horn.FatouQ.hasDerivAt_zBranch
import Submission.Work.Horn.FatouQ.hasDerivAt_lbranch_zBranch
import Submission.Work.Horn.FatouQ.norm_zBranch_inv_pow_le

/-!
# The derivative of the approximate Fatou coordinate `Xfun` at the far end

`Xfun f q a j w = Acorr f q a (zBranch q a j w)` is the approximate Fatou coordinate of the
parabolic germ expressed in the chart `w = cc q a / z^q`.  On the `j`-th petal the chart is a
biholomorphism onto the half plane `{Re w > M}` and the leading term of `Acorr` is exactly the
chart itself, so

  `Xfun f q a j w = w + (lower order terms)`

with the lower order terms of size `O (‖w‖ ^ (1 - 1/q))`.  Differentiating, the correction to the
derivative is `O (‖w‖ ^ (-1/q))`, whence `deriv (Xfun f q a j) w → 1` as `Re w → ∞`.

The proof computes the derivative explicitly.  With `z = zBranch q a j w` (so `z^q = cc q a / w`)
the chain rule gives `(zBranch)' w = -z/(q w)` and

  `deriv (Xfun f q a j) w - 1
     = (1/(q w)) * (∑_{i=1}^{q-1} (q-i) (g_i/(i-q)) z^{-(q-i)} - (g_q + (q+1)/2))`,

and each summand is `O (‖w‖ ^ (-i/q))` since `‖z‖^q = ‖cc‖ / ‖w‖`.
-/

namespace Work.Horn.FatouQ

open Work.Horn.Flower Filter
open scoped Topology

noncomputable section

/-- The derivative of the `m`-th power of the reciprocal of `zBranch`: with `z = zBranch q a j w`
and `(zBranch)' w = -z/((q:ℂ)*w)` one has `((zBranch)⁻¹)^m ' w = m (z⁻¹)^m / ((q:ℂ)*w)`. -/
private lemma hasDerivAt_inv_pow {q : ℕ} {a : ℂ} {j : Fin q} {w : ℂ} (hq : 1 ≤ q)
    (hz : zBranch q a j w ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hzB : HasDerivAt (zBranch q a j) (-(zBranch q a j w) / ((q:ℂ)*w)) w) :
    HasDerivAt (fun w' : ℂ => ((zBranch q a j w')⁻¹)^m)
      ((m:ℂ) * ((zBranch q a j w)⁻¹)^m / ((q:ℂ)*w)) w := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hinv := hzB.inv hz
  have hpow := hinv.pow m
  have hpow_id : ((zBranch q a j w)⁻¹)^(m-1) * (zBranch q a j w)⁻¹
      = ((zBranch q a j w)⁻¹)^m := by
    rw [← pow_succ]; congr 1; omega
  have hval : -(-(zBranch q a j w) / ((q:ℂ)*w))/(zBranch q a j w)^2
      = 1/((q:ℂ)*w*(zBranch q a j w)) := by
    field_simp
  refine hpow.congr_deriv ?_
  simp only [Pi.inv_apply]
  rw [hval, ← hpow_id]
  field_simp

/-- Per-term estimate: for `‖z‖^q = ‖c‖/‖w‖` and `1 ≤ m ≤ q-1` the `m`-th term of the defect is
`O (‖w‖^(-1/q))`. -/
private lemma term_norm_le {q : ℕ} {c z w : ℂ} (hq : 1 ≤ q) (hc : c ≠ 0) (hzq : z ^ q = c / w)
    (hw : 1 ≤ w.re) {m : ℕ} (hm1 : 1 ≤ m) (hmq : m ≤ q - 1) (g : ℂ) :
    ‖g * ((m : ℂ) * (z⁻¹) ^ m / ((q : ℂ) * w))‖ ≤
      ‖g‖ * ((m : ℝ) * ‖c‖ ^ (-((m : ℝ) / (q : ℝ)))
        * (w.re ^ (-(1 : ℝ) / (q : ℝ)) / (q : ℝ))) := by
  have hqR : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
  have hwr : 0 < w.re := lt_of_lt_of_le zero_lt_one hw
  have hstep1 : ‖g * ((m : ℂ) * (z⁻¹) ^ m / ((q : ℂ) * w))‖
      = ‖g‖ * ((m : ℝ) * (‖z‖⁻¹) ^ m / ((q : ℝ) * ‖w‖)) := by
    rw [norm_mul, norm_div, norm_mul, norm_natCast, norm_pow, norm_inv, norm_mul, norm_natCast]
  rw [hstep1]
  have hD2 : ‖w‖⁻¹ * (‖z‖⁻¹) ^ m ≤ ‖w‖ ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ))) := by
    have h := norm_zBranch_inv_pow_le hq hc hzq hw hm1 hmq
    have hEq : ‖c‖ ^ (-(m:ℝ)/(q:ℝ)) = ‖c‖ ^ (-((m:ℝ)/(q:ℝ))) := by rw [neg_div]
    rwa [hEq] at h
  have hnn1 : (0:ℝ) ≤ (m:ℝ) * ‖g‖ / (q:ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg m) (norm_nonneg g)) hqR.le
  have hstep2 : ((m:ℝ) * ‖g‖ / (q:ℝ)) * (‖w‖⁻¹ * (‖z‖⁻¹)^m)
      ≤ ((m:ℝ) * ‖g‖ / (q:ℝ)) * (‖w‖ ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ)))) :=
    mul_le_mul_of_nonneg_left hD2 hnn1
  have hrpow_le : ‖w‖ ^ (-(1:ℝ)/(q:ℝ)) ≤ w.re ^ (-(1:ℝ)/(q:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hwr (Complex.re_le_norm w) (by
      rw [neg_div]; exact neg_nonpos.mpr (div_nonneg zero_le_one hqR.le))
  have hstep3 : ((m:ℝ) * ‖g‖ / (q:ℝ)) * (‖w‖ ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ))))
      ≤ ((m:ℝ) * ‖g‖ / (q:ℝ)) * (w.re ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ)))) := by
    have h1 : ‖w‖ ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ)))
        ≤ w.re ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ))) :=
      mul_le_mul_of_nonneg_right hrpow_le (Real.rpow_nonneg (norm_nonneg c) _)
    exact mul_le_mul_of_nonneg_left h1 hnn1
  calc ‖g‖ * ((m : ℝ) * (‖z‖⁻¹) ^ m / ((q : ℝ) * ‖w‖))
      = ((m:ℝ) * ‖g‖ / (q:ℝ)) * (‖w‖⁻¹ * (‖z‖⁻¹)^m) := by
        rw [inv_eq_one_div]; ring
    _ ≤ ((m:ℝ) * ‖g‖ / (q:ℝ)) * (w.re ^ (-(1:ℝ)/(q:ℝ)) * ‖c‖ ^ (-((m:ℝ)/(q:ℝ)))) :=
        le_trans hstep2 hstep3
    _ = ‖g‖ * ((m : ℝ) * ‖c‖ ^ (-((m : ℝ) / (q : ℝ)))
          * (w.re ^ (-(1 : ℝ) / (q : ℝ)) / (q : ℝ))) := by
        ring

/-- The constant term of the defect is also `O (‖w‖^(-1/q))`. -/
private lemma kappa_bound {q : ℕ} (hq : 1 ≤ q) {w : ℂ} (hw : 1 ≤ w.re) (κ : ℂ) :
    ‖κ / ((q:ℂ)*w)‖ ≤ ‖κ‖ * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
  have hwr : 0 < w.re := lt_of_lt_of_le zero_lt_one hw
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one (le_trans hw (Complex.re_le_norm w))
  have h1 : ‖κ / ((q:ℂ)*w)‖ = ‖κ‖ / ((q:ℝ)*‖w‖) := by
    rw [norm_div, norm_mul, norm_natCast]
  rw [h1]
  have hinv : ‖w‖⁻¹ ≤ w.re ^ (-(1:ℝ)) := by
    have h3 : w.re ^ (-(1:ℝ)) = (w.re)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hwr), Real.rpow_one]
    rw [h3]
    exact (inv_le_inv₀ hwn hwr).mpr (Complex.re_le_norm w)
  have hexp : w.re ^ (-(1:ℝ)) ≤ w.re ^ (-(1:ℝ)/(q:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hw (by
      rw [neg_div]
      have h4 : (1:ℝ)/(q:ℝ) ≤ 1 := by
        rw [div_le_one hqR]; exact_mod_cast hq
      linarith)
  have h2 : ‖w‖⁻¹ ≤ w.re ^ (-(1:ℝ)/(q:ℝ)) := le_trans hinv hexp
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  have h2' := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hqR.le)
  rw [mul_comm ((↑q)⁻¹) (w.re ^ (-(1:ℝ)/(q:ℝ)))] at h2'
  exact mul_le_mul_of_nonneg_left h2' (norm_nonneg κ)

/-- The explicit derivative of the approximate coordinate in the chart. -/
theorem hasDerivAt_Xfun {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → zBranch q a j w ∈ petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → chartQ q a (zBranch q a j w) = w)
    {w : ℂ} (hw : M < w.re) :
    HasDerivAt (Xfun f q a j)
      (1 + (∑ i ∈ Finset.Icc 1 (q - 1), (gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
              (((q - i : ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w)))
        + (gcoef f q a q + ((q:ℂ)+1)/2) * (-1/((q:ℂ)*w))) w := by
  have hq : 1 ≤ q := hd.hS.hq
  have ha : a ≠ 0 := hd.hS.ha
  have hM : 0 < M := hd.hM
  have hz_ne : ∀ w : ℂ, M < w.re → zBranch q a j w ≠ 0 := fun w hw =>
    fun h => hd.hgeo.not_mem_petal_zero j (h ▸ hpetal w hw)
  have hwr : 0 < w.re := lt_trans hM hw
  have hzB : ∀ w : ℂ, 0 < w.re →
      HasDerivAt (zBranch q a j) (-(zBranch q a j w) / ((q:ℂ)*w)) w :=
    fun w hw => hasDerivAt_zBranch hq ha j hw
  have hlog : ∀ w : ℂ, M < w.re →
      HasDerivAt (fun w' : ℂ => Lbranch q a (zBranch q a j w')) (-1/((q:ℂ)*w)) w :=
    fun w hw => hasDerivAt_lbranch_zBranch hd j hpetal hchart hw
  have hterm : ∀ i ∈ Finset.Icc 1 (q-1),
      HasDerivAt (fun w' : ℂ => (gcoef f q a i / ((i:ℂ)-(q:ℂ))) * ((zBranch q a j w')⁻¹)^(q-i))
        ((gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
          (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w))) w := by
    intro i hi
    have hm1 : 1 ≤ q - i := by have := (Finset.mem_Icc.mp hi).2; omega
    exact (hasDerivAt_inv_pow hq (hz_ne w hw) hm1 (hzB w hwr)).const_mul _
  have h1 : HasDerivAt (fun w' : ℂ => cc q a / (zBranch q a j w')^q) 1 w := by
    have hev : (fun w' : ℂ => cc q a / (zBranch q a j w')^q) =ᶠ[𝓝 w] (fun w' => w') := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw]
        with w' hw'
      exact hchart w' hw'
    exact (hasDerivAt_id w).congr_of_eventuallyEq hev
  have h2 : HasDerivAt (fun w' : ℂ => ∑ i ∈ Finset.Icc 1 (q-1),
        (gcoef f q a i / ((i:ℂ)-(q:ℂ))) * ((zBranch q a j w')⁻¹)^(q-i))
      (∑ i ∈ Finset.Icc 1 (q-1), (gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
        (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w))) w := by
    have h := HasDerivAt.sum (fun i hi => hterm i hi)
    rw [show (∑ i ∈ Finset.Icc 1 (q-1), (fun w' : ℂ =>
            (gcoef f q a i / ((i:ℂ)-(q:ℂ))) * ((zBranch q a j w')⁻¹)^(q-i)))
        = (fun w' : ℂ => ∑ i ∈ Finset.Icc 1 (q-1),
            (gcoef f q a i / ((i:ℂ)-(q:ℂ))) * ((zBranch q a j w')⁻¹)^(q-i)) from by
          funext w'; rw [Finset.sum_apply]] at h
    exact h
  have h3 := (hlog w hw).const_mul (gcoef f q a q + ((q:ℂ)+1)/2)
  have hcomb := (h1.add h2).add h3
  have hfun : Xfun f q a j = (fun w' : ℂ => cc q a / (zBranch q a j w')^q
      + (∑ i ∈ Finset.Icc 1 (q-1),
          (gcoef f q a i / ((i:ℂ)-(q:ℂ))) * ((zBranch q a j w')⁻¹)^(q-i))
      + (gcoef f q a q + ((q:ℂ)+1)/2) * Lbranch q a (zBranch q a j w')) := by
    ext w'
    simp only [Xfun, Acorr]
  rw [hfun]
  exact hcomb

theorem Xfun_deriv_close {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w) :
    ∃ N : ℝ, M ≤ N ∧ ∀ w : ℂ, N < w.re →
      ‖deriv (Work.Horn.FatouQ.Xfun f q a j) w - 1‖ ≤ 1 / 4 := by
  have hq : 1 ≤ q := hd.hS.hq
  have hM : 0 < M := hd.hM
  have hcc : cc q a ≠ 0 := hd.hgeo.cc_ne_zero
  have hqR : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
  have hz_ne : ∀ w : ℂ, M < w.re → zBranch q a j w ≠ 0 := fun w hw =>
    fun h => hd.hgeo.not_mem_petal_zero j (h ▸ hpetal w hw)
  set κ : ℂ := gcoef f q a q + ((q:ℂ)+1)/2 with hκdef
  -- the constant of the estimate
  set K : ℝ := ((∑ i ∈ Finset.Icc 1 (q - 1), ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ *
        (((q - i : ℕ):ℝ) * ‖cc q a‖ ^ (-(((q - i : ℕ):ℝ)/(q:ℝ))))) + ‖κ‖) / (q:ℝ)
    with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    apply div_nonneg
    · apply add_nonneg
      · exact Finset.sum_nonneg (fun i hi => mul_nonneg (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
      · exact norm_nonneg _
    · exact hqR.le
  -- the pointwise estimate
  have hest : ∀ w : ℂ, M < w.re → 1 ≤ w.re →
      ‖deriv (Xfun f q a j) w - 1‖ ≤ K * w.re ^ (-(1:ℝ)/(q:ℝ)) := by
    intro w hw hw1
    have hwr : 0 < w.re := lt_trans hM hw
    have hzq : (zBranch q a j w)^q = cc q a / w := by
      have hz0 : zBranch q a j w ≠ 0 := hz_ne w hw
      have hw0 : w ≠ 0 := by rintro h; rw [h] at hwr; simp at hwr
      have h : cc q a / (zBranch q a j w)^q = w := hchart w hw
      rw [div_eq_iff (pow_ne_zero q hz0)] at h
      rw [eq_div_iff hw0, h]; ring
    have hder := (hasDerivAt_Xfun hd j hpetal hchart hw).deriv
    have hdiff : deriv (Xfun f q a j) w - 1
        = (∑ i ∈ Finset.Icc 1 (q-1), (gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
              (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w)))
          - κ/((q:ℂ)*w) := by
      rw [hder, hκdef]; ring
    rw [hdiff]
    have hterm : ∀ i ∈ Finset.Icc 1 (q-1),
        ‖(gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
            (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w))‖
          ≤ ‖(gcoef f q a i / ((i:ℂ)-(q:ℂ)))‖ *
              (((q-i:ℕ):ℝ) * ‖cc q a‖ ^ (-(((q-i:ℕ):ℝ)/(q:ℝ)))
                * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ))) := by
      intro i hi
      have hm1 : 1 ≤ q - i := by have := (Finset.mem_Icc.mp hi).2; omega
      have hmq : q - i ≤ q - 1 := by have := (Finset.mem_Icc.mp hi).1; omega
      exact term_norm_le hq hcc hzq hw1 hm1 hmq _
    have hκb : ‖κ / ((q:ℂ)*w)‖ ≤ ‖κ‖ * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ)) :=
      kappa_bound hq hw1 κ
    have hfac : (∑ i ∈ Finset.Icc 1 (q-1), ‖(gcoef f q a i / ((i:ℂ)-(q:ℂ)))‖ *
          (((q-i:ℕ):ℝ) * ‖cc q a‖ ^ (-(((q-i:ℕ):ℝ)/(q:ℝ)))
            * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ))))
        = (∑ i ∈ Finset.Icc 1 (q-1), ‖(gcoef f q a i / ((i:ℂ)-(q:ℂ)))‖ *
            (((q-i:ℕ):ℝ) * ‖cc q a‖ ^ (-(((q-i:ℕ):ℝ)/(q:ℝ)))))
          * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i hi => by ring)
    calc ‖(∑ i ∈ Finset.Icc 1 (q-1), (gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
              (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w))) - κ/((q:ℂ)*w)‖
        ≤ ‖(∑ i ∈ Finset.Icc 1 (q-1), (gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
              (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w)))‖
            + ‖κ/((q:ℂ)*w)‖ := norm_sub_le _ _
      _ ≤ (∑ i ∈ Finset.Icc 1 (q-1), ‖(gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
              (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w))‖)
            + ‖κ/((q:ℂ)*w)‖ := by
          exact add_le_add
            (norm_sum_le (Finset.Icc 1 (q-1)) (fun i => (gcoef f q a i / ((i:ℂ)-(q:ℂ))) *
              (((q-i:ℕ):ℂ) * ((zBranch q a j w)⁻¹)^(q-i) / ((q:ℂ)*w)))) le_rfl
      _ ≤ (∑ i ∈ Finset.Icc 1 (q-1), ‖(gcoef f q a i / ((i:ℂ)-(q:ℂ)))‖ *
              (((q-i:ℕ):ℝ) * ‖cc q a‖ ^ (-(((q-i:ℕ):ℝ)/(q:ℝ)))
                * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ))))
            + ‖κ‖ * (w.re ^ (-(1:ℝ)/(q:ℝ)) / (q:ℝ)) :=
          add_le_add (Finset.sum_le_sum (fun i hi => hterm i hi)) hκb
      _ = K * w.re ^ (-(1:ℝ)/(q:ℝ)) := by
          rw [hfac, hKdef]; ring
  -- the level `N`
  have htend : Tendsto (fun x : ℝ => K * x ^ (-(1:ℝ)/(q:ℝ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => K * x ^ (-((1:ℝ)/(q:ℝ)))) atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_neg_atTop (by positivity : (0:ℝ) < (1:ℝ)/(q:ℝ))).const_mul K
      rw [mul_zero] at h1
      exact h1
    convert h2 using 1
    rw [neg_div]
  have hev : ∀ᶠ x : ℝ in atTop, K * x ^ (-(1:ℝ)/(q:ℝ)) ≤ 1/4 := by
    have hlt : ∀ᶠ x : ℝ in atTop, K * x ^ (-(1:ℝ)/(q:ℝ)) < 1/4 :=
      (tendsto_order.1 htend).2 (1/4) (by norm_num)
    exact hlt.mono (fun x hx => le_of_lt hx)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨max M (max N₀ 1), le_max_left _ _, ?_⟩
  intro w hw
  have hlt := max_lt_iff.mp hw
  have hMw : M < w.re := hlt.1
  have hN0w : N₀ < w.re := lt_of_le_of_lt (le_max_left _ _) hlt.2
  have h1w : 1 ≤ w.re := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hlt.2)
  calc ‖deriv (Xfun f q a j) w - 1‖ ≤ K * w.re ^ (-(1:ℝ)/(q:ℝ)) := hest w hMw h1w
    _ ≤ 1/4 := hN₀ w.re hN0w.le

end

end Work.Horn.FatouQ
