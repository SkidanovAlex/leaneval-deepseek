import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.ArcsinChord

namespace Work.CNum

open Work.ANum

/-! ## `2 arcsin u ≤ 2u + u³/3 + u⁵/5` for `u ≤ 1/2`

`ArcsinChord` with the hypothesis relaxed from `u ≤ 1/4` to `u ≤ 1/2` (the proof only needs
`3y² + y⁴ + y⁶ ≤ 1`, which holds for `y ≤ 1/2`). -/

private noncomputable def Gd (y : ℝ) : ℝ := 2 * y + y ^ 3 / 3 + y ^ 5 / 5 - 2 * Real.arcsin y

private lemma continuousOn_Gd : ContinuousOn Gd (Set.Icc 0 (1 / 2)) := by
  have : Continuous Gd := by unfold Gd; fun_prop
  exact this.continuousOn

private lemma hasDerivAt_Gd (x : ℝ) (hx1 : x ≠ 1) (hxn1 : x ≠ -1) :
    HasDerivAt Gd (2 + x ^ 2 + x ^ 4 - 2 * (1 / Real.sqrt (1 - x ^ 2))) x := by
  change HasDerivAt (fun y : ℝ => 2 * y + y ^ 3 / 3 + y ^ 5 / 5 - 2 * Real.arcsin y)
    (2 + x ^ 2 + x ^ 4 - 2 * (1 / Real.sqrt (1 - x ^ 2))) x
  have ha : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hb : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
    have h : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (((3 : ℝ) * x ^ (3 - 1) * 1) / 3) x := by
      simpa using ((hasDerivAt_id x).pow 3).div_const 3
    have hv : ((3 : ℝ) * x ^ (3 - 1) * 1) / 3 = x ^ 2 := by ring_nf
    rwa [hv] at h
  have hc : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
    have h : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (((5 : ℝ) * x ^ (5 - 1) * 1) / 5) x := by
      simpa using ((hasDerivAt_id x).pow 5).div_const 5
    have hv : ((5 : ℝ) * x ^ (5 - 1) * 1) / 5 = x ^ 4 := by ring_nf
    rwa [hv] at h
  have hpoly : HasDerivAt (fun y : ℝ => 2 * y + y ^ 3 / 3 + y ^ 5 / 5) (2 + x ^ 2 + x ^ 4) x := by
    convert (ha.add hb).add hc using 1 <;> try rfl
  have harc : HasDerivAt (fun y : ℝ => 2 * Real.arcsin y)
      (2 * (1 / Real.sqrt (1 - x ^ 2))) x := by
    simpa using (Real.hasDerivAt_arcsin hxn1 hx1).const_mul 2
  convert hpoly.sub harc using 1 <;> try rfl

private lemma arcsin_growth_key' (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    2 * (1 / Real.sqrt (1 - x ^ 2)) ≤ 2 + x ^ 2 + x ^ 4 := by
  have hx2 : x ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hx4 : x ^ 4 ≤ (1 / 16 : ℝ) := by
    have h : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h]; nlinarith [sq_nonneg (x ^ 2)]
  have hx6 : x ^ 6 ≤ (1 / 64 : ℝ) := by
    have h : x ^ 6 = (x ^ 2) ^ 3 := by ring
    rw [h]; nlinarith [sq_nonneg (x ^ 2)]
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos_of_pos hpos
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hsq : (2 : ℝ) ^ 2 ≤ ((2 + x ^ 2 + x ^ 4) * Real.sqrt (1 - x ^ 2)) ^ 2 := by
    rw [mul_pow, hs2]
    have hsum : 3 * x ^ 2 + x ^ 4 + x ^ 6 ≤ 1 := by nlinarith
    have hkey : (2 + x ^ 2 + x ^ 4) ^ 2 * (1 - x ^ 2)
        = 4 + x ^ 4 * (1 - 3 * x ^ 2 - x ^ 4 - x ^ 6) := by ring
    rw [hkey]
    have : 0 ≤ x ^ 4 * (1 - 3 * x ^ 2 - x ^ 4 - x ^ 6) := by nlinarith [sq_nonneg (x ^ 2)]
    linarith
  have hAs : 0 ≤ (2 + x ^ 2 + x ^ 4) * Real.sqrt (1 - x ^ 2) := by positivity
  have h2 : (2 : ℝ) ≤ (2 + x ^ 2 + x ^ 4) * Real.sqrt (1 - x ^ 2) := by
    have habs := sq_le_sq.mp hsq
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hAs] at habs
    exact habs
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt hs
  have h3 : 2 * (Real.sqrt (1 - x ^ 2))⁻¹ ≤ (2 + x ^ 2 + x ^ 4) := by
    have h2' := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hs.le)
    rwa [mul_assoc, mul_inv_cancel₀ hsne, mul_one] at h2'
  rwa [one_div]

/-- `2 arcsin u ≤ 2u + u³/3 + u⁵/5` for `0 ≤ u ≤ 1/2`. -/
theorem arcsin_chord_half {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    2 * Real.arcsin u ≤ 2 * u + u ^ 3 / 3 + u ^ 5 / 5 := by
  have hmono : MonotoneOn Gd (Set.Icc 0 (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
    · exact continuousOn_Gd
    · rw [interior_Icc]
      intro x hx
      exact (hasDerivAt_Gd x (by linarith [hx.2]) (by linarith [hx.1])).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hasDerivAt_Gd x (by linarith [hx.2]) (by linarith [hx.1])).deriv]
      have hk := arcsin_growth_key' x (le_of_lt hx.1) (le_of_lt hx.2)
      linarith
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := ⟨le_refl 0, by norm_num⟩
  have hmemu : u ∈ Set.Icc 0 (1 / 2) := ⟨h0, h1⟩
  have hgu : Gd 0 ≤ Gd u := hmono hmem0 hmemu h0
  have hgz : Gd 0 = 0 := by simp [Gd]
  have hnonneg : 0 ≤ Gd u := by rw [← hgz]; exact hgu
  dsimp only [Gd] at hnonneg
  linarith

/-- `m2r` commutes with `min`. -/
lemma DAux_m2r_min (a b : ℤ) : m2r (min a b) = min (m2r a) (m2r b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (m2r_le h)]
  · rw [min_eq_right h, min_eq_right (m2r_le h)]

lemma norm_ofReal_daux (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

/-- `‖1 - e^{it}‖ = 2 |sin (t/2)|`. -/
lemma norm_one_sub_exp_mul_I (t : ℝ) : ‖(1 : ℂ) - Complex.exp (Complex.I * (t : ℂ))‖ =
    2 * |Real.sin (t / 2)| := by
  have h1 : Complex.exp (Complex.I * (t : ℂ)) =
      ((Real.cos t : ℂ)) + ((Real.sin t : ℂ)) * Complex.I := by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I t
  have hc : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    have hcs := Real.cos_sq' (t / 2)
    nlinarith
  have hs : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    have h := Real.sin_two_mul (t / 2)
    rwa [show 2 * (t / 2) = t by ring] at h
  have hcs := Real.cos_sq' (t / 2)
  have hnsq : Complex.normSq ((1 : ℂ) - Complex.exp (Complex.I * (t : ℂ))) =
      4 * Real.sin (t / 2) ^ 2 := by
    rw [h1, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    have e1 : (1 - Real.cos t) * (1 - Real.cos t) =
        4 * (Real.sin (t / 2)) ^ 4 := by rw [hc]; ring
    have e2 : (0 - Real.sin t) * (0 - Real.sin t) =
        4 * (Real.sin (t / 2)) ^ 2 * (Real.cos (t / 2)) ^ 2 := by rw [hs]; ring
    rw [e1, e2]
    nlinarith [hcs]
  rw [Complex.norm_def, hnsq]
  rw [show (4 : ℝ) * Real.sin (t / 2) ^ 2 = (2 * Real.sin (t / 2)) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- `‖e^{ix} - e^{iy}‖ = 2 |sin ((x-y)/2)|`. -/
lemma norm_exp_I_sub (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ =
      2 * |Real.sin ((x - y) / 2)| := by
  have hfac : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (x : ℂ)) * (1 - Complex.exp (Complex.I * ((y - x : ℝ) : ℂ))) := by
    rw [mul_sub, mul_one]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [hfac, norm_mul]
  have h1 : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [h1, one_mul, norm_one_sub_exp_mul_I]
  have h2 : Real.sin ((y - x) / 2) = - Real.sin ((x - y) / 2) := by
    rw [show (y - x) / 2 = -((x - y) / 2) by ring, Real.sin_neg]
  rw [h2, abs_neg]

/-- **Arc versus chord.**  For `0 ≤ b - a ≤ 1`,
`b - a ≤ ‖e^{ia} - e^{ib}‖ + ‖e^{ia} - e^{ib}‖³/12 + 4096/SC`. -/
theorem arc_le_chord {a b : ℝ} (h0 : 0 ≤ b - a) (h1 : b - a ≤ 1) :
    b - a ≤ ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ +
      ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ^ 3 / 12 +
      4096 / (SC : ℝ) := by
  set δ : ℝ := b - a with hδ
  set x : ℝ := ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ with hxdef
  have hsn0 : 0 ≤ Real.sin (δ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three, h0])
  have hx : x = 2 * Real.sin (δ / 2) := by
    rw [hxdef, norm_exp_I_sub]
    have h1 : (a - b) / 2 = -(δ / 2) := by rw [hδ]; ring
    rw [h1, Real.sin_neg, abs_neg, abs_of_nonneg hsn0]
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hxle : x ≤ 1 := by
    rw [hx]
    have hs := Real.sin_le (show (0 : ℝ) ≤ δ / 2 by positivity)
    linarith
  have hx2 : x / 2 ≤ 1 / 2 := by linarith
  have hmain : δ / 2 = Real.arcsin (x / 2) := by
    have hxs : x / 2 = Real.sin (δ / 2) := by rw [hx]; ring
    rw [hxs, Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])]
  have hchord := arcsin_chord_half (u := x / 2) (by linarith) hx2
  have hquad : 2 * (x / 2) + (x / 2) ^ 3 / 3 + (x / 2) ^ 5 / 5 ≤ x + x ^ 3 / 12 := by
    have h5 : (x / 2) ^ 5 / 5 = x ^ 5 / 160 := by ring
    have h3 : (x / 2) ^ 3 / 3 = x ^ 3 / 24 := by ring
    rw [h5, h3]
    have hx2le : x ^ 2 ≤ 1 := by nlinarith
    have h53 : x ^ 5 ≤ x ^ 3 := by
      have h55 : x ^ 5 = x ^ 3 * x ^ 2 := by ring
      rw [h55]
      calc x ^ 3 * x ^ 2 ≤ x ^ 3 * 1 := mul_le_mul_of_nonneg_left hx2le (pow_nonneg hx0 3)
        _ = x ^ 3 := by ring
    have h24 : x ^ 5 / 160 ≤ x ^ 3 / 24 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [h53, pow_nonneg hx0 3]
    linarith
  have hfin : δ ≤ x + x ^ 3 / 12 + 4096 / (SC : ℝ) := by
    have hd2 : δ = 2 * (δ / 2) := by ring
    have hSC : (0 : ℝ) < 4096 / (SC : ℝ) := div_pos (by norm_num) SC_posR
    rw [hd2, hmain]
    linarith [hchord, hquad, hSC]
  exact hfin

end Work.CNum
