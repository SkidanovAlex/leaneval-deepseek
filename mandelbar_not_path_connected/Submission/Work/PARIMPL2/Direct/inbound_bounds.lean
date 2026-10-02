import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth
import Submission.Work.PARIMPL2.Direct.sinh_chart_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

set_option maxHeartbeats 100000000

/-! ## Elementary facts about `Z(u) = sinh(iλu)/(iλ) = sin(λu)/λ` -/

/-- `sinh (iλu)/(iλ) = sin (λu)/λ`. -/
theorem inbound_Z_eq (lam : ℝ) (u : ℂ) :
    Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I)
      = Complex.sin ((lam : ℂ) * u) / (lam : ℂ) := by
  have h : ((lam : ℂ) * Complex.I) * u = ((lam : ℂ) * u) * Complex.I := by ring
  rw [h, Complex.sinh_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero]

theorem inbound_sin_re (lam : ℝ) (u : ℂ) :
    (Complex.sin ((lam : ℂ) * u)).re = Real.sin (lam * u.re) * Real.cosh (lam * u.im) := by
  have hdecomp : (lam : ℂ) * u = ((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hkey : Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)
      = ((Real.sin (lam * u.re) * Real.cosh (lam * u.im) : ℝ) : ℂ)
        + ((Real.cos (lam * u.re) * Real.sinh (lam * u.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have h1 : (Complex.sin ((lam : ℂ) * u)).re
      = (Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)).re := by
    rw [hdecomp]
  rw [h1, hkey]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem inbound_sin_im (lam : ℝ) (u : ℂ) :
    (Complex.sin ((lam : ℂ) * u)).im = Real.cos (lam * u.re) * Real.sinh (lam * u.im) := by
  have hdecomp : (lam : ℂ) * u = ((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hkey : Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)
      = ((Real.sin (lam * u.re) * Real.cosh (lam * u.im) : ℝ) : ℂ)
        + ((Real.cos (lam * u.re) * Real.sinh (lam * u.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have h1 : (Complex.sin ((lam : ℂ) * u)).im
      = (Complex.sin (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)).im := by
    rw [hdecomp]
  rw [h1, hkey]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem inbound_cos_re (lam : ℝ) (u : ℂ) :
    (Complex.cos ((lam : ℂ) * u)).re = Real.cos (lam * u.re) * Real.cosh (lam * u.im) := by
  have hdecomp : (lam : ℂ) * u = ((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hkey : Complex.cos (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (lam * u.re) * Real.cosh (lam * u.im) : ℝ) : ℂ)
        - ((Real.sin (lam * u.re) * Real.sinh (lam * u.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have h1 : (Complex.cos ((lam : ℂ) * u)).re
      = (Complex.cos (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)).re := by
    rw [hdecomp]
  rw [h1, hkey]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem inbound_cos_im (lam : ℝ) (u : ℂ) :
    (Complex.cos ((lam : ℂ) * u)).im = -(Real.sin (lam * u.re) * Real.sinh (lam * u.im)) := by
  have hdecomp : (lam : ℂ) * u = ((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hkey : Complex.cos (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (lam * u.re) * Real.cosh (lam * u.im) : ℝ) : ℂ)
        - ((Real.sin (lam * u.re) * Real.sinh (lam * u.im) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have h1 : (Complex.cos ((lam : ℂ) * u)).im
      = (Complex.cos (((lam * u.re : ℝ) : ℂ) + ((lam * u.im : ℝ) : ℂ) * Complex.I)).im := by
    rw [hdecomp]
  rw [h1, hkey]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Squared modulus of `sin (λu)`. -/
theorem inbound_sq_abs_sin (lam : ℝ) (u : ℂ) :
    ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2
      = Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, inbound_sin_re, inbound_sin_im]
  nlinarith [Real.cosh_sq (lam * u.im), Real.sin_sq_add_cos_sq (lam * u.re)]

/-- Squared modulus of `cos (λu)`. -/
theorem inbound_sq_abs_cos (lam : ℝ) (u : ℂ) :
    ‖Complex.cos ((lam : ℂ) * u)‖ ^ 2
      = Real.cos (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, inbound_cos_re, inbound_cos_im]
  nlinarith [Real.cosh_sq (lam * u.im), Real.sin_sq_add_cos_sq (lam * u.re)]

/-! ## The Écalle point map on the imaginary axis -/

/-- `ecalE a u - 1 = 2·sinh(a·u)·exp(a·u)`. -/
theorem inbound_ecalE_sub_one (a u : ℂ) :
    Work.Implosion.ecalE a u - 1 = 2 * Complex.sinh (a * u) * Complex.exp (a * u) := by
  rw [Work.Implosion.ecalE, show (2 : ℂ) * a * u = (a * u) + (a * u) by ring, Complex.exp_add,
    Complex.sinh, Complex.exp_neg]
  have h : Complex.exp (a * u) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem inbound_sinh_ne_zero (lam : ℝ) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1) :
    Complex.sinh (((lam : ℂ) * Complex.I) * u) ≠ 0 := by
  intro hs
  apply h
  rw [← sub_eq_zero]
  have hkey := inbound_ecalE_sub_one ((lam : ℂ) * Complex.I) u
  rw [hkey, hs]; ring

theorem inbound_sin_lam_ne_zero (lam : ℝ) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1) :
    Complex.sin ((lam : ℂ) * u) ≠ 0 := by
  intro hs
  apply inbound_sinh_ne_zero lam u h
  rw [show (((lam : ℂ) * Complex.I) * u) = ((lam : ℂ) * u) * Complex.I by ring,
    Complex.sinh_mul_I, hs, zero_mul]

/-- On the imaginary axis the Écalle point map is `λ·cos(λu)/sin(λu)`. -/
theorem inbound_ecalPt_eq (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1) :
    Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u
      = (lam : ℂ) * (Complex.cos ((lam : ℂ) * u) / Complex.sin ((lam : ℂ) * u)) := by
  have hsinh := inbound_sinh_ne_zero lam u h
  have hsin := inbound_sin_lam_ne_zero lam u h
  rw [Work.Implosion.Ecalle.ecallePt_eq_coth _ _ h, Work.Implosion.coth,
    show (((lam : ℂ) * Complex.I) * u) = ((lam : ℂ) * u) * Complex.I by ring,
    Complex.cosh_mul_I, Complex.sinh_mul_I]
  field_simp

/-- Real part of the Écalle point map on the imaginary axis. -/
theorem inbound_ecalPt_re (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1) :
    (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re
      = lam * (Real.sin (lam * u.re) * Real.cos (lam * u.re))
          / ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2 := by
  have hsin := inbound_sin_lam_ne_zero lam u h
  have hD : (0 : ℝ) < ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hsin) 2
  rw [inbound_ecalPt_eq lam hlam u h, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.div_re, inbound_sin_re, inbound_sin_im, inbound_cos_re,
    inbound_cos_im, Complex.normSq_eq_norm_sq]
  field_simp
  rw [Real.cosh_sq]
  ring

theorem inbound_Z_re (lam : ℝ) (hlam : lam ≠ 0) (u : ℂ) :
    (Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I)).re
      = Real.sin (lam * u.re) * Real.cosh (lam * u.im) / lam := by
  rw [inbound_Z_eq, Complex.div_re, inbound_sin_re, inbound_sin_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal, mul_zero, add_zero]
  field_simp
  ring

theorem inbound_Z_im (lam : ℝ) (hlam : lam ≠ 0) (u : ℂ) :
    (Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I)).im
      = Real.cos (lam * u.re) * Real.sinh (lam * u.im) / lam := by
  rw [inbound_Z_eq, Complex.div_im, inbound_sin_re, inbound_sin_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal, mul_zero, sub_zero, zero_mul]
  field_simp
  ring

/-- `ζ·Z = cos(λu)` on the imaginary axis. -/
theorem inbound_ecalPt_mul_Z (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1) :
    Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u
        * (Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I))
      = Complex.cos ((lam : ℂ) * u) := by
  have hsin : Complex.sin ((lam : ℂ) * u) ≠ 0 := inbound_sin_lam_ne_zero lam u h
  have hlam' : ((lam : ℂ)) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hlam)
  rw [Work.Implosion.Ecalle.ecallePt_eq_coth _ _ h, Work.Implosion.coth,
    show (((lam : ℂ) * Complex.I) * u) = ((lam : ℂ) * u) * Complex.I by ring,
    Complex.cosh_mul_I, Complex.sinh_mul_I]
  field_simp

/-- `(ecalPt (iλ) u).re < 0` forces `sin (2λu.re) < 0`. -/
theorem inbound_ecalPt_re_neg (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1)
    (hre : (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re < 0) :
    Real.sin (2 * (lam * u.re)) < 0 := by
  have hsin := inbound_sin_lam_ne_zero lam u h
  have hD : (0 : ℝ) < ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hsin) 2
  rw [inbound_ecalPt_re lam hlam u h] at hre
  have hprod : Real.sin (lam * u.re) * Real.cos (lam * u.re) < 0 := by
    by_contra hc
    push_neg at hc
    have h1 : 0 ≤ lam * (Real.sin (lam * u.re) * Real.cos (lam * u.re)) :=
      mul_nonneg (le_of_lt hlam) hc
    have h2 : 0 ≤ lam * (Real.sin (lam * u.re) * Real.cos (lam * u.re))
        / ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2 := div_nonneg h1 (le_of_lt hD)
    linarith
  rw [Real.sin_two_mul]
  nlinarith [hprod]

/-- Branch condition plus `Re ζ < 0` pins `λ·u.re ∈ (π/2, π)`. -/
theorem inbound_lamx_mem (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1)
    (hbranch : -(Real.pi / 2) < lam * u.re - Real.pi ∧
      lam * u.re - Real.pi ≤ Real.pi / 2)
    (hre : (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re < 0) :
    Real.pi / 2 < lam * u.re ∧ lam * u.re < Real.pi := by
  have hsin2 := inbound_ecalPt_re_neg lam hlam u h hre
  obtain ⟨hb1, hb2⟩ := hbranch
  constructor
  · linarith
  · by_contra hcon
    push_neg at hcon
    have h3 : Real.sin (2 * (lam * u.re)) = Real.sin (2 * (lam * u.re) - 2 * Real.pi) :=
      (Real.sin_sub_two_pi _).symm
    rw [h3] at hsin2
    have h0 : 0 ≤ 2 * (lam * u.re) - 2 * Real.pi := by linarith
    have hpi : 2 * (lam * u.re) - 2 * Real.pi ≤ Real.pi := by linarith
    exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi h0 hpi) (not_le.mpr hsin2)

/-- `x·cosh x - sinh x ≥ 0` for `x ≥ 0`. -/
theorem inbound_mul_cosh_sub_sinh_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x * Real.cosh x - Real.sinh x := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro y hy
      exact ((differentiableAt_id.mul Real.differentiableAt_cosh).sub
        Real.differentiableAt_sinh).differentiableWithinAt
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      have hd : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t) (y * Real.sinh y) y := by
        have h4 : HasDerivAt (fun t : ℝ => t * Real.cosh t) (1 * Real.cosh y + y * Real.sinh y) y :=
          (hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)
        have h5 : HasDerivAt Real.sinh (Real.cosh y) y := Real.hasDerivAt_sinh y
        convert h4.sub h5 using 1
        ring
      rw [hd.deriv]
      exact mul_nonneg (le_of_lt hy) (Real.sinh_nonneg_iff.mpr hy.le)
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simpa using h

/-- `sinh t ≤ (19/16)·t` for `0 ≤ t ≤ 1`. -/
theorem inbound_sinh_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sinh t ≤ 19 / 16 * t := by
  have hsinh1 : Real.sinh 1 ≤ 19 / 16 := by
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.exp_neg_one_gt_d9
    rw [Real.sinh_eq]
    linarith
  rcases eq_or_lt_of_le ht0 with rfl | hpos
  · simp
  have hmono : MonotoneOn (fun t : ℝ => Real.sinh t / t) (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact ContinuousOn.div Real.continuous_sinh.continuousOn continuous_id.continuousOn
        (fun x hx => ne_of_gt hx)
    · intro x hx
      rw [interior_Ioi] at hx
      exact (Real.differentiableAt_sinh.div differentiableAt_id (ne_of_gt hx)).differentiableWithinAt
    · intro x hx
      rw [interior_Ioi, Set.mem_Ioi] at hx
      have hd : HasDerivAt (fun s : ℝ => Real.sinh s / s)
          ((Real.cosh x * x - Real.sinh x * 1) / x ^ 2) x :=
        (Real.hasDerivAt_sinh x).div (hasDerivAt_id x) (ne_of_gt hx)
      rw [hd.deriv]
      apply div_nonneg _ (by positivity)
      have h1 := inbound_mul_cosh_sub_sinh_nonneg x hx.le
      linarith
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have ht : t ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hpos
  have hle := hmono ht h1 ht1
  rw [div_le_iff₀ hpos] at hle
  have h3 := mul_le_mul_of_nonneg_right hsinh1 ht0
  linarith [hle, h3]

/-- `exp (3/4) ≥ 2.1`. -/
theorem inbound_exp_34 : (2.1 : ℝ) ≤ Real.exp (3 / 4) := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3 / 4 by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    pow_zero, pow_one, zero_add] at h
  norm_num at h
  linarith

/-- `log R ≤ R/4 + 3` for `R ≥ 4`. -/
theorem inbound_log_le (R : ℝ) (hR : 4 ≤ R) : Real.log R ≤ R / 4 + 3 := by
  have h1 : Real.log (R / 4) ≤ R / 4 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [Real.log_div (by linarith : R ≠ 0) (by norm_num : (4:ℝ) ≠ 0)] at h1
  have h2 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  linarith

/-- `|tanh t| ≤ |t|`. -/
theorem inbound_abs_tanh_le (t : ℝ) : |Real.tanh t| ≤ |t| := by
  have hcosh : 0 < Real.cosh t := Real.cosh_pos t
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos hcosh, div_le_iff₀ hcosh]
  have h4 : Real.cosh |t| = Real.cosh t := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, Real.cosh_neg]
  have h5 : Real.sinh |t| ≤ |t| * Real.cosh |t| := by
    have := inbound_mul_cosh_sub_sinh_nonneg |t| (abs_nonneg t)
    linarith
  rw [Real.abs_sinh, ← h4]
  exact h5

/-- A `exp`-fixed-point step: if `exp x ≤ C + c·x` and the fixed point value at
`x₀ = log R + 3/4` is strictly above the affine bound, then `x ≤ x₀`. -/
theorem inbound_exp_le_fixed (R C c x : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hineq : Real.exp x ≤ C + c * x)
    (hpos : 0 < Real.exp (Real.log R + 3 / 4) - c)
    (hkey : 0 < Real.exp (Real.log R + 3 / 4) - c * (Real.log R + 3 / 4) - C) :
    x ≤ Real.log R + 3 / 4 := by
  by_contra hcon
  rw [not_le] at hcon
  have hsplit : Real.exp x
      = Real.exp (Real.log R + 3 / 4) * Real.exp (x - (Real.log R + 3 / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have hge : 1 + (x - (Real.log R + 3 / 4)) ≤ Real.exp (x - (Real.log R + 3 / 4)) := by
    have := Real.add_one_le_exp (x - (Real.log R + 3 / 4)); linarith
  have hexp0pos : 0 < Real.exp (Real.log R + 3 / 4) := Real.exp_pos _
  have h1 : Real.exp x ≥ Real.exp (Real.log R + 3 / 4) * (1 + (x - (Real.log R + 3 / 4))) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hge (le_of_lt hexp0pos)
  nlinarith [hineq, h1, hpos, hkey, hcon]
theorem inbound_bounds (lam R H : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hH : 0 ≤ H) (hHR : 8 * (H + 2) ≤ R)
    (κ : ℂ) (hκR : 64 * ‖κ‖ ≤ R) (hκI : |κ.im| ≤ 1 / 4)
    (hκlog : ‖κ‖ * (1 + Real.log R) ≤ 3 * R / 4)
    (u : ℂ)
    (hbranch : -(Real.pi / 2) < lam * u.re - Real.pi ∧ lam * u.re - Real.pi ≤ Real.pi / 2)
    (hulev : (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re ∈
      Set.Icc (Real.pi / lam - R - 2) (Real.pi / lam - R))
    (huim : |(Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).im| ≤ H)
    (hzre : (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re < 0)
    (hzn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R) :
    |u.im| ≤ 2 * H + 8 + Real.log R ∧ R / 4 ≤ u.re ∧ u.re ≤ Real.pi / lam - R / 4 := by
  have hR0 : (0:ℝ) < R := by linarith
  have hlogR_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogR1 : 0 < 1 + Real.log R := by linarith
  have hHle : H ≤ R / 8 - 2 := by linarith
  have hlogRb : Real.log R ≤ R / 4 + 3 := inbound_log_le R (by linarith)
  set Z : ℂ := Complex.sinh (((lam:ℂ)*Complex.I)*u)/((lam:ℂ)*Complex.I) with hZdef
  have hE : Work.Implosion.ecalE ((lam:ℂ)*Complex.I) u ≠ 1 := by
    intro hh
    rw [Work.Implosion.ecalPt, hh] at hzre
    simp at hzre
  have hZeq : Z = Complex.sin ((lam:ℂ)*u)/(lam:ℂ) := by rw [hZdef]; exact inbound_Z_eq lam u
  have hZre : Z.re = Real.sin (lam*u.re)*Real.cosh (lam*u.im)/lam := by
    rw [hZdef]; exact inbound_Z_re lam (ne_of_gt hlam) u
  have hZim : Z.im = Real.cos (lam*u.re)*Real.sinh (lam*u.im)/lam := by
    rw [hZdef]; exact inbound_Z_im lam (ne_of_gt hlam) u
  have hZnorm : ‖Z‖^2 = (Real.sin (lam*u.re)^2 + Real.sinh (lam*u.im)^2)/lam^2 := by
    rw [hZdef]; exact sinh_chart_norm lam u
  have hlamx := inbound_lamx_mem lam hlam u hE hbranch hzre
  have hsinx : 0 < Real.sin (lam*u.re) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hlamx.1, Real.pi_pos]) hlamx.2
  have hcosx : Real.cos (lam*u.re) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hlamx.1 (by linarith [hlamx.2, Real.pi_pos])
  have hZre_pos : 0 < Z.re := by
    rw [hZre]; exact div_pos (mul_pos hsinx (Real.cosh_pos _)) hlam
  have hargZ_lt : Z.arg < Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hZre_pos)
  have hargZ_gt : -(Real.pi/2) < Z.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hZre_pos)
  have hargZ : |Z.arg| ≤ Real.pi/2 := abs_le.mpr ⟨le_of_lt hargZ_gt, le_of_lt hargZ_lt⟩
  have hW : Work.Implosion.approxEcal ((lam:ℂ)*Complex.I) κ u = u + κ * Complex.log Z := by
    rw [hZdef, Work.Implosion.approxEcal_apply]
  have hP : (Work.Implosion.approxEcal ((lam:ℂ)*Complex.I) κ u).re
      = u.re + (κ.re * Real.log ‖Z‖ - κ.im * Z.arg) := by
    rw [hW, Complex.add_re, Complex.mul_re, Complex.log_re, Complex.log_im]
  have hQ : (Work.Implosion.approxEcal ((lam:ℂ)*Complex.I) κ u).im
      = u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖) := by
    rw [hW, Complex.add_im, Complex.mul_im, Complex.log_re, Complex.log_im]
  obtain ⟨hPlo0, hPhi0⟩ := hulev
  have hPlo : Real.pi/lam - R - 2 ≤ u.re + (κ.re * Real.log ‖Z‖ - κ.im * Z.arg) := by
    rw [← hP]; exact hPlo0
  have hPhi : u.re + (κ.re * Real.log ‖Z‖ - κ.im * Z.arg) ≤ Real.pi/lam - R := by
    rw [← hP]; exact hPhi0
  have hQabs : |u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖)| ≤ H := by rw [← hQ]; exact huim
  have hA : |κ.re| ≤ R/64 := le_trans (Complex.abs_re_le_norm κ) (by linarith)
  have hB : |κ.im| ≤ 1/4 := hκI
  have hAlog : |κ.re| * (1 + Real.log R) ≤ 3*R/4 :=
    le_trans (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm κ) (le_of_lt hlogR1)) hκlog
  have hZne : Z ≠ 0 := by
    intro h0
    have h2 : Z * (lam:ℂ) = Complex.sin ((lam:ℂ)*u) := by
      rw [hZeq, div_mul_cancel₀ _ (ofReal_ne_zero.mpr (ne_of_gt hlam))]
    rw [h0, zero_mul] at h2
    exact inbound_sin_lam_ne_zero lam u hE h2.symm
  have hZpos : 0 < ‖Z‖ := norm_pos_iff.mpr hZne
  have hmulZ : ‖Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) u‖ * ‖Z‖ = ‖Complex.cos ((lam:ℂ)*u)‖ := by
    rw [← norm_mul]
    congr 1
    rw [hZdef]
    exact inbound_ecalPt_mul_Z lam hlam u hE
  have hcos_ge : |Real.cos (lam*u.re)| ≤ ‖Complex.cos ((lam:ℂ)*u)‖ := by
    have h2 : Real.cos (lam*u.re)^2 ≤ ‖Complex.cos ((lam:ℂ)*u)‖^2 := by
      rw [inbound_sq_abs_cos]; nlinarith [sq_nonneg (Real.sinh (lam*u.im))]
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3
  have hZge_cos : (R/4) * |Real.cos (lam*u.re)| ≤ ‖Z‖ := by
    have hzeta4 : ‖Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) u‖ * (R/4) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_right hzn (by linarith : (0:ℝ) ≤ R/4)
      have h2 : (4/R)*(R/4) = 1 := by field_simp
      linarith [h1, h2]
    calc (R/4) * |Real.cos (lam*u.re)|
        ≤ (R/4) * ‖Complex.cos ((lam:ℂ)*u)‖ := mul_le_mul_of_nonneg_left hcos_ge (by linarith)
      _ = (R/4) * (‖Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) u‖ * ‖Z‖) := by rw [hmulZ]
      _ = ‖Z‖ * (‖Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) u‖ * (R/4)) := by ring
      _ ≤ ‖Z‖ * 1 := mul_le_mul_of_nonneg_left hzeta4 (norm_nonneg _)
      _ = ‖Z‖ := by ring
  have hZubcosh : ‖Z‖ ≤ Real.cosh (lam*|u.im|)/lam := by
    have h1 : ‖Z‖^2 ≤ (Real.cosh (lam*|u.im|)/lam)^2 := by
      rw [hZnorm, div_pow]
      apply div_le_div_of_nonneg_right _ (sq_nonneg lam)
      have hsin1 : Real.sin (lam*u.re)^2 ≤ 1 := Real.sin_sq_le_one _
      have hsinh2 : Real.sinh (lam*u.im)^2 = Real.sinh (lam*|u.im|)^2 := by
        rw [← sq_abs (Real.sinh (lam*u.im)), Real.abs_sinh, abs_mul,
          abs_of_nonneg (le_of_lt hlam)]
      have hc := Real.cosh_sq (lam*|u.im|)
      nlinarith [hsin1, hsinh2, hc]
    nlinarith [h1, norm_nonneg Z, div_nonneg (le_of_lt (Real.cosh_pos (lam * |u.im|))) (le_of_lt hlam)]
  have hR2sq : (16384:ℝ) ≤ R^2 := by nlinarith [hR]
  have hR4 : 1 < R^4 - 16*R^2 := by
    have h3 : (262144:ℝ) ≤ R^2 * (R^2 - 16) := by nlinarith [hR2sq, sq_nonneg (R^2 - 16)]
    nlinarith [h3]
  have hLp_nonneg : 0 ≤ Real.log ‖Z‖ := by
    by_contra hcon
    rw [not_le] at hcon
    have hZlt1 : ‖Z‖ < 1 := (Real.log_neg_iff hZpos).mp hcon
    have hcoslt : |Real.cos (lam*u.re)| < 4/R := by
      have h1 : (R/4) * |Real.cos (lam*u.re)| < 1 := lt_of_le_of_lt hZge_cos hZlt1
      have h2 : (0:ℝ) < R/4 := by linarith
      have h3 : |Real.cos (lam*u.re)| < 1/(R/4) := by rw [lt_div_iff₀ h2]; linarith [h1]
      have h4 : 1/(R/4) = 4/R := by field_simp
      linarith [h3, h4]
    have hsin2 : 1 - 16/R^2 < Real.sin (lam*u.re)^2 := by
      have h2 : Real.cos (lam*u.re)^2 < 16/R^2 := by
        have h3 : |Real.cos (lam*u.re)|^2 < (4/R)^2 :=
          pow_lt_pow_left₀ hcoslt (abs_nonneg _) (by norm_num : (2:ℕ) ≠ 0)
        rw [sq_abs] at h3
        have h4 : (4/R)^2 = 16/R^2 := by rw [div_pow]; norm_num
        linarith [h3, h4]
      have h4 := Real.sin_sq_add_cos_sq (lam*u.re)
      linarith [h4, h2]
    have hbig : 1 < ‖Z‖^2 := by
      rw [hZnorm]
      have h5 : (1 - 16/R^2)/lam^2 ≤ (Real.sin (lam*u.re)^2 + Real.sinh (lam*u.im)^2)/lam^2 := by
        apply div_le_div_of_nonneg_right
        · linarith [hsin2, sq_nonneg (Real.sinh (lam*u.im))]
        · exact sq_nonneg lam
      have h7 : R^4 ≤ 1/lam^2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < lam^2)]
        have h0 : 0 ≤ lam * R^2 := le_of_lt (mul_pos hlam (pow_pos hR0 2))
        have h1 : (lam*R^2)*(lam*R^2) ≤ 1*1 := mul_self_le_mul_self h0 hlamR
        nlinarith [h1]
      have h8 : (0:ℝ) ≤ 1 - 16/R^2 := by
        have : 16/R^2 ≤ 1 := by rw [div_le_one (by positivity : (0:ℝ) < R^2)]; nlinarith
        linarith
      have h9 : (1 - 16/R^2) * R^4 ≤ (1 - 16/R^2) * (1/lam^2) :=
        mul_le_mul_of_nonneg_left h7 h8
      have h10 : (1 - 16/R^2) * R^4 = R^4 - 16*R^2 := by field_simp
      have h11 : (1 - 16/R^2)/lam^2 = (1 - 16/R^2) * (1/lam^2) := by rw [div_eq_mul_inv, one_div]
      have h6 : R^4 - 16*R^2 ≤ (1 - 16/R^2)/lam^2 := by rw [h11]; linarith [h9, h10]
      linarith [h5, h6, hR4]
    nlinarith [hbig, hZlt1]
  have hYlam : lam * |u.im| ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hY0 : 0 < |u.im| := pos_of_mul_pos_right (by linarith) (le_of_lt hlam)
    have hYlarge : 1/lam < |u.im| := by rw [div_lt_iff₀ hlam]; linarith
    have hcoshexp : Real.cosh (lam*|u.im|) ≤ Real.exp (lam*|u.im|) := by
      rw [Real.cosh_eq]
      have h1 : Real.exp (-(lam*|u.im|)) ≤ Real.exp (lam*|u.im|) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hexp_le : Real.log ‖Z‖ ≤ lam*|u.im| + Real.log (1/lam) := by
      calc Real.log ‖Z‖ ≤ Real.log (Real.cosh (lam*|u.im|)/lam) :=
            Real.log_le_log hZpos hZubcosh
        _ ≤ Real.log (Real.exp (lam*|u.im|)/lam) := by
            apply Real.log_le_log (by positivity)
            exact div_le_div_of_nonneg_right hcoshexp (le_of_lt hlam)
        _ = lam*|u.im| - Real.log lam := by
            rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hlam), Real.log_exp]
        _ = lam*|u.im| + Real.log (1/lam) := by
            rw [one_div, Real.log_inv]; ring
    have hlog_le : Real.log (1/lam) ≤ Real.log |u.im| :=
      Real.log_le_log (by positivity) (le_of_lt hYlarge)
    have hQb : |u.im| ≤ H + (R/64)*(Real.pi/2) + (1/4)*Real.log ‖Z‖ := by
      have h1 : |u.im| ≤ |u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖)|
          + |κ.re * Z.arg + κ.im * Real.log ‖Z‖| := by
        have h2 := abs_add_le (u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖))
          (-(κ.re * Z.arg + κ.im * Real.log ‖Z‖))
        rwa [show u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖)
          + -(κ.re * Z.arg + κ.im * Real.log ‖Z‖) = u.im by ring, abs_neg] at h2
      have h3 : |κ.re * Z.arg + κ.im * Real.log ‖Z‖| ≤ (R/64)*(Real.pi/2) + (1/4)*Real.log ‖Z‖ := by
        have h4 := abs_add_le (κ.re * Z.arg) (κ.im * Real.log ‖Z‖)
        have h5 : |κ.re * Z.arg| = |κ.re| * |Z.arg| := abs_mul _ _
        have h6 : |κ.im * Real.log ‖Z‖| = |κ.im| * Real.log ‖Z‖ := by
          rw [abs_mul, abs_of_nonneg hLp_nonneg]
        have h7 : |κ.re| * |Z.arg| ≤ (R/64)*(Real.pi/2) := by
          have := mul_le_mul hA hargZ (abs_nonneg _) (by positivity : (0:ℝ) ≤ R/64)
          linarith
        have h8 : |κ.im| * Real.log ‖Z‖ ≤ (1/4)*Real.log ‖Z‖ :=
          mul_le_mul_of_nonneg_right hB hLp_nonneg
        linarith [h4, h5, h6, h7, h8]
      linarith [h1, hQabs, h3]
    have hYle : |u.im| ≤ H + (R/64)*(Real.pi/2) + (1/4)*(lam*|u.im| + Real.log |u.im|) := by
      linarith [hQb, hexp_le, hlog_le]
    have hYR2 : R^2 ≤ |u.im| := by
      have h1 : R^2 ≤ 1/lam := by rw [le_div_iff₀ hlam]; nlinarith [hlamR]
      linarith [h1, hYlarge.le]
    have hlam4 : lam / 4 ≤ 1/(4*R^2) := by
      have h1 : lam ≤ 1/R^2 := by rw [le_div_iff₀ (by positivity : (0:ℝ) < R^2)]; linarith [hlamR]
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
      have h2 : (1/(4*R^2)) * 4 = 1/R^2 := by field_simp
      rw [h2]; exact h1
    have hlogY : Real.log |u.im| ≤ |u.im| - 1 := Real.log_le_sub_one_of_pos hY0
    have hA1 : (R/64)*(Real.pi/2) ≤ 0.025*R := by nlinarith [Real.pi_lt_d2, hR]
    have hA2 : (1/4)*(lam*|u.im|) ≤ |u.im|/(4*R^2) := by
      have h := mul_le_mul_of_nonneg_right hlam4 (abs_nonneg u.im)
      have h2 : (1/(4*R^2)) * |u.im| = |u.im|/(4*R^2) := by ring
      nlinarith [h, h2]
    have hA3 : (1/4)*Real.log |u.im| ≤ |u.im|/4 - 1/4 := by linarith [hlogY]
    have hcomb : |u.im| ≤ (R/8-2) + 0.025*R + |u.im|/(4*R^2) + |u.im|/4 - 1/4 :=
      by linarith [hYle, hHle, hA1, hA2, hA3]
    have hcomb2 : |u.im| * (3/4 - 1/(4*R^2)) ≤ 0.15*R - 2.25 := by nlinarith [hcomb]
    nlinarith [hcomb2, hYR2, hR]
  set b : ℝ := Real.pi/lam - u.re with hb
  have hbpos : 0 < b := by
    rw [hb, sub_pos, lt_div_iff₀ hlam]
    linarith [hlamx.2]
  have hlb : lam * b = Real.pi - lam*u.re := by rw [hb]; field_simp
  have hlbpos : 0 < lam*b := by rw [hlb]; linarith [hlamx.1, Real.pi_pos]
  have hlblt : lam*b < Real.pi/2 := by rw [hlb]; linarith [hlamx.2]
  have hb0 : 0 ≤ b := le_of_lt hbpos
  have hsin_eq : Real.sin (lam*u.re) = Real.sin (lam*b) := by
    rw [hlb]; exact (Real.sin_pi_sub _).symm
  have hZub : ‖Z‖ ≤ b + 19/16 * |u.im| := by
    have h1 : ‖Z‖^2 ≤ (b + 19/16*|u.im|)^2 := by
      rw [hZnorm, div_le_iff₀ (by positivity : (0:ℝ) < lam^2)]
      have hsinle : Real.sin (lam*u.re)^2 ≤ (lam*b)^2 := by
        rw [hsin_eq]
        have := Real.sin_le (le_of_lt hlbpos)
        nlinarith [this, hlbpos]
      have hsinhle : Real.sinh (lam*u.im)^2 ≤ (19/16 * (lam*|u.im|))^2 := by
        have h2 : Real.sinh (lam*u.im)^2 = Real.sinh (lam*|u.im|)^2 := by
          rw [← sq_abs (Real.sinh (lam*u.im)), Real.abs_sinh, abs_mul, abs_of_nonneg (le_of_lt hlam)]
        rw [h2]
        have h3 := inbound_sinh_le (lam*|u.im|) (by positivity) hYlam
        have h4 : 0 ≤ Real.sinh (lam*|u.im|) := Real.sinh_nonneg_iff.mpr (by positivity)
        have h5 : 0 ≤ 19/16 * (lam*|u.im|) := by positivity
        nlinarith [h3, h4, h5]
      nlinarith [hsinle, hsinhle, hb0, abs_nonneg u.im, sq_nonneg lam]
    nlinarith [h1, norm_nonneg Z, hb0, abs_nonneg u.im]
  have hbub : b ≤ R + 2 + |κ.re| * Real.log ‖Z‖ + Real.pi/8 := by
    have h2 : b ≤ R + 2 + (κ.re*Real.log ‖Z‖ - κ.im*Z.arg) := by rw [hb]; linarith [hPlo]
    have h4 : κ.re*Real.log ‖Z‖ ≤ |κ.re| * Real.log ‖Z‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hLp_nonneg
    have h5 : -κ.im*Z.arg ≤ |κ.im| * |Z.arg| := by
      have := neg_le_abs (κ.im*Z.arg); rw [abs_mul] at this; linarith
    have h6 : |κ.im| * |Z.arg| ≤ Real.pi/8 := by
      have := mul_le_mul hB hargZ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
      have h7 : (1:ℝ)/4 * (Real.pi/2) = Real.pi/8 := by ring
      linarith [this, h7]
    linarith [h2, h4, h5, h6]
  have hdecomp : |u.im| ≤ H + |κ.re| * |Z.arg| + (1/4)*Real.log ‖Z‖ := by
    have h1 : |u.im| ≤ |u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖)|
        + |κ.re * Z.arg + κ.im * Real.log ‖Z‖| := by
      have h2 := abs_add_le (u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖))
        (-(κ.re * Z.arg + κ.im * Real.log ‖Z‖))
      rwa [show u.im + (κ.re * Z.arg + κ.im * Real.log ‖Z‖)
        + -(κ.re * Z.arg + κ.im * Real.log ‖Z‖) = u.im by ring, abs_neg] at h2
    have h3 : |κ.re * Z.arg + κ.im * Real.log ‖Z‖| ≤ |κ.re| * |Z.arg| + (1/4)*Real.log ‖Z‖ := by
      have h4 := abs_add_le (κ.re * Z.arg) (κ.im * Real.log ‖Z‖)
      have h5 : |κ.re * Z.arg| = |κ.re| * |Z.arg| := abs_mul _ _
      have h6 : |κ.im * Real.log ‖Z‖| = |κ.im| * Real.log ‖Z‖ := by
        rw [abs_mul, abs_of_nonneg hLp_nonneg]
      have h8 : |κ.im| * Real.log ‖Z‖ ≤ (1/4)*Real.log ‖Z‖ :=
        mul_le_mul_of_nonneg_right hB hLp_nonneg
      linarith [h4, h5, h6, h8]
    linarith [h1, hQabs, h3]
  have hYub : |u.im| ≤ H + (R/64)*(Real.pi/2) + (1/4)*Real.log ‖Z‖ := by
    have h7 : |κ.re| * |Z.arg| ≤ (R/64)*(Real.pi/2) := by
      have := mul_le_mul hA hargZ (abs_nonneg _) (by positivity : (0:ℝ) ≤ R/64)
      linarith
    linarith [hdecomp, h7]
  have hLp_le : Real.log ‖Z‖ ≤ Real.log R + 3/4 := by
    have hexpLp : Real.exp (Real.log ‖Z‖) = ‖Z‖ := Real.exp_log hZpos
    have hexp34 : (2.1:ℝ) ≤ Real.exp (3/4) := inbound_exp_34
    have hexpR : Real.exp (Real.log R + 3/4) = R * Real.exp (3/4) := by
      rw [Real.exp_add, Real.exp_log hR0]
    have hc1 : (R*1 + R*(19/128) + R*(19*Real.pi/2048)) ≤ (118/100)*R := by
      nlinarith [Real.pi_lt_d2, hR]
    have hc2 : (2 + Real.pi/8 - 19/8 : ℝ) ≤ 2/100 := by nlinarith [Real.pi_lt_d2]
    have hsum : b + 19/16*|u.im| ≤ (118/100)*R + (R/64 + 3/10)*Real.log ‖Z‖ + 2/100 := by
      have h1 : 19/16 * (|u.im|) ≤ 19/16 * (H + (R/64)*(Real.pi/2) + (1/4)*Real.log ‖Z‖) :=
        mul_le_mul_of_nonneg_left hYub (by norm_num)
      have h2 : |κ.re| * Real.log ‖Z‖ ≤ (R/64) * Real.log ‖Z‖ :=
        mul_le_mul_of_nonneg_right hA hLp_nonneg
      nlinarith [hbub, h1, h2, hHle, hc1, hc2, hLp_nonneg]
    by_cases hcase : 1 + Real.log R ≤ 48
    · have hlogR47 : Real.log R ≤ 47 := by linarith
      have hmain : Real.exp (Real.log ‖Z‖) ≤ (118/100)*R + (R/64 + 3/10)*Real.log ‖Z‖ + 2/100 := by
        rw [hexpLp]; linarith [hZub, hsum]
      have hmain' : Real.exp (Real.log ‖Z‖)
          ≤ ((118/100)*R + 2/100) + (R/64 + 3/10)*Real.log ‖Z‖ := by linarith [hmain]
      refine inbound_exp_le_fixed R ((118/100)*R + 2/100) (R/64+3/10) (Real.log ‖Z‖) (by linarith)
        (by linarith) hmain' ?_ ?_
      · rw [hexpR]; nlinarith [hexp34, hR]
      · rw [hexpR]; nlinarith [hexp34, hlogR47, hR]
    · push_neg at hcase
      have hAc : |κ.re| ≤ 3*R/(4*(1+Real.log R)) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*(1+Real.log R))]
        nlinarith [hAlog]
      have hden : 0 < 4*(1+Real.log R) := by positivity
      have hsum' : b + 19/16*|u.im|
          ≤ (118/100)*R + (3*R/(4*(1+Real.log R)) + 3/10)*Real.log ‖Z‖ + 2/100 := by
        have h1 : 19/16 * |u.im| ≤ 19/16 * (H + |κ.re| * |Z.arg| + (1/4)*Real.log ‖Z‖) :=
          mul_le_mul_of_nonneg_left hdecomp (by norm_num)
        have h2 : |κ.re| * Real.log ‖Z‖ ≤ (3*R/(4*(1+Real.log R))) * Real.log ‖Z‖ :=
          mul_le_mul_of_nonneg_right hAc hLp_nonneg
        have h3 : |κ.re| * |Z.arg| ≤ (3*R/(4*(1+Real.log R))) * (Real.pi/2) :=
          mul_le_mul hAc hargZ (abs_nonneg _) (by positivity : (0:ℝ) ≤ 3*R/(4*(1+Real.log R)))
        have h4 : 3*R/(4*(1+Real.log R)) ≤ R/64 := by
          rw [div_le_iff₀ hden]
          nlinarith [hcase]
        nlinarith [hbub, h1, h2, h3, hHle, hc1, hc2, hLp_nonneg, h4, Real.pi_lt_d2, hR]
      have hmain : Real.exp (Real.log ‖Z‖)
          ≤ (118/100)*R + (3*R/(4*(1+Real.log R)) + 3/10)*Real.log ‖Z‖ + 2/100 := by
        rw [hexpLp]; linarith [hZub, hsum']
      have hmain' : Real.exp (Real.log ‖Z‖)
          ≤ ((118/100)*R + 2/100) + (3*R/(4*(1+Real.log R)) + 3/10)*Real.log ‖Z‖ := by
        linarith [hmain]
      refine inbound_exp_le_fixed R ((118/100)*R + 2/100) (3*R/(4*(1+Real.log R))+3/10) (Real.log ‖Z‖)
        (by linarith) (by positivity) hmain' ?_ ?_
      · have h3 : 3*R/(4*(1+Real.log R)) ≤ 3*R/4 := by
          rw [div_le_iff₀ hden]
          nlinarith [hlogR1]
        rw [hexpR]; nlinarith [hexp34, h3, hR]
      · have h3 : (3*R/(4*(1+Real.log R)))*(Real.log R + 3/4) ≤ 3*R/4 - Real.pi/8 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hden]
          nlinarith [hlogRb, hR, Real.pi_lt_d2, Real.pi_pos]
        rw [hexpR]; nlinarith [hexp34, h3, hR]
  have hbge : R/4 ≤ b := by
    have h1 : R + (κ.re*Real.log ‖Z‖ - κ.im*Z.arg) ≤ b := by rw [hb]; linarith [hPhi]
    have h4 : -Real.pi/8 ≤ -κ.im*Z.arg := by
      have h2 : |κ.im| * |Z.arg| ≤ Real.pi/8 := by
        have := mul_le_mul hB hargZ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
        have h7 : (1:ℝ)/4 * (Real.pi/2) = Real.pi/8 := by ring
        linarith [this, h7]
      have h5 : κ.im*Z.arg ≤ |κ.im| * |Z.arg| := by rw [← abs_mul]; exact le_abs_self _
      linarith [h2, h5]
    have h3 : -(3*R/4 - Real.pi/8) ≤ κ.re*Real.log ‖Z‖ := by
      have h6 : |κ.re| * Real.log ‖Z‖ ≤ 3*R/4 - Real.pi/8 := by
        by_cases hcase : 1 + Real.log R ≤ 48
        · have h47 : Real.log R ≤ 47 := by linarith
          have h8 : Real.log ‖Z‖ ≤ 47 + 3/4 := by linarith [hLp_le]
          have h9 : |κ.re| * Real.log ‖Z‖ ≤ (R/64)*(47 + 3/4) :=
            mul_le_mul hA h8 hLp_nonneg (by positivity : (0:ℝ) ≤ R/64)
          nlinarith [h9, hR, Real.pi_lt_d2]
        · push_neg at hcase
          have hAc : |κ.re| ≤ 3*R/(4*(1+Real.log R)) := by
            rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*(1+Real.log R))]
            nlinarith [hAlog]
          have h9 : |κ.re| * Real.log ‖Z‖ ≤ (3*R/(4*(1+Real.log R)))*(Real.log R + 3/4) :=
            mul_le_mul hAc hLp_le hLp_nonneg (by positivity)
          have h10 : (3*R/(4*(1+Real.log R)))*(Real.log R + 3/4) ≤ 3*R/4 - Real.pi/8 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 4*(1+Real.log R))]
            nlinarith [hlogRb, hR, Real.pi_lt_d2, Real.pi_pos]
          linarith [h9, h10]
      have h7 : -(|κ.re| * Real.log ‖Z‖) ≤ κ.re*Real.log ‖Z‖ := by
        have h := mul_le_mul_of_nonneg_right (neg_abs_le κ.re) hLp_nonneg
        have h2 : -|κ.re| * Real.log ‖Z‖ = -(|κ.re| * Real.log ‖Z‖) := by ring
        linarith only [h, h2]
      linarith only [h6, h7]
    linarith only [h1, h3, h4]
  have hxge : R/4 ≤ u.re := by
    have h1 : Real.pi/(2*lam) ≤ u.re := by
      have h : Real.pi/(2*lam) < u.re := by
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*lam)]
        nlinarith [hlamx.1]
      linarith
    have h2 : R/4 ≤ Real.pi/(2*lam) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*lam)]
      have hlamR2 : lam*R ≤ 1/R := by rw [le_div_iff₀ hR0]; linarith [hlamR]
      have hlamR3 : lam*R ≤ 1 := by
        have h : 1/R ≤ 1 := by rw [div_le_one hR0]; linarith [hR]
        linarith [hlamR2, h]
      nlinarith [hlamR3, Real.pi_gt_three]
    linarith only [h1, h2]
  have hYle : |u.im| ≤ 2*H + 8 + Real.log R := by
    have harg_le : |Z.arg| ≤ Real.pi * |u.im| / (2*b) := by
      have h1 : Z.arg = Real.arctan (Z.im/Z.re) := by
        rw [← Complex.tan_arg Z]; exact (Real.arctan_tan hargZ_gt hargZ_lt).symm
      have h2 : |Z.arg| ≤ |Z.im/Z.re| := by rw [h1]; exact Real.abs_arctan_le_abs
      have h3 : |Z.im/Z.re| ≤ Real.pi * |u.im| / (2*b) := by
        have h4 : |Z.im/Z.re| = |Real.cos (lam*u.re)| * |Real.sinh (lam*u.im)|
            /(Real.sin (lam*u.re)*Real.cosh (lam*u.im)) := by
          have h4a : Z.im/Z.re = Real.cos (lam*u.re) * Real.sinh (lam*u.im)
              / (Real.sin (lam*u.re) * Real.cosh (lam*u.im)) := by
            rw [hZim, hZre]
            field_simp
          rw [h4a, abs_div, abs_of_pos (mul_pos hsinx (Real.cosh_pos (lam*u.im))), abs_mul]
        rw [h4]
        have htanh : |Real.sinh (lam*u.im)|/Real.cosh (lam*u.im) ≤ lam*|u.im| := by
          have h5 : |Real.sinh (lam*u.im)|/Real.cosh (lam*u.im) = |Real.tanh (lam*u.im)| := by
            rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos (lam*u.im))]
          rw [h5]
          have h8 := inbound_abs_tanh_le (lam*u.im)
          rwa [abs_mul, abs_of_nonneg (le_of_lt hlam)] at h8
        have h6 : |Real.cos (lam*u.re)| / Real.sin (lam*u.re) ≤ Real.pi/(2*(lam*b)) := by
          have hsin_ge : 2/Real.pi * (lam*b) ≤ Real.sin (lam*u.re) := by
            rw [hsin_eq]; exact Real.mul_le_sin (le_of_lt hlbpos) (le_of_lt hlblt)
          have h7 : |Real.cos (lam*u.re)| ≤ 1 := Real.abs_cos_le_one _
          calc |Real.cos (lam*u.re)| / Real.sin (lam*u.re) ≤ 1 / Real.sin (lam*u.re) :=
                div_le_div_of_nonneg_right h7 (le_of_lt hsinx)
            _ ≤ 1 / (2/Real.pi * (lam*b)) :=
                one_div_le_one_div_of_le (by positivity) hsin_ge
            _ = Real.pi/(2*(lam*b)) := by field_simp
        calc |Real.cos (lam*u.re)| * |Real.sinh (lam*u.im)|/(Real.sin (lam*u.re)*Real.cosh (lam*u.im))
            = (|Real.cos (lam*u.re)|/Real.sin (lam*u.re))
              * (|Real.sinh (lam*u.im)|/Real.cosh (lam*u.im)) := by field_simp
          _ ≤ (Real.pi/(2*(lam*b))) * (lam*|u.im|) :=
              mul_le_mul h6 htanh (by positivity) (by positivity)
          _ = Real.pi * |u.im|/(2*b) := by field_simp
      linarith [h2, h3]
    have h2 : |κ.re| * |Z.arg| ≤ Real.pi * |u.im|/32 := by
      have h3 : |κ.re| * |Z.arg| ≤ (R/64)*(Real.pi * |u.im|/(2*b)) :=
        mul_le_mul hA harg_le (abs_nonneg _) (by positivity : (0:ℝ) ≤ R/64)
      have h4 : (R/64)*(Real.pi * |u.im|/(2*b)) ≤ Real.pi * |u.im|/32 := by
        have hbR : 1/(2*b) ≤ 2/R := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*b) hR0]
          nlinarith [hbge, hR0]
        have hpos : 0 ≤ Real.pi * |u.im| * (R/64) := by positivity
        calc (R/64)*(Real.pi * |u.im|/(2*b)) = (Real.pi * |u.im| * (R/64)) * (1/(2*b)) := by ring
          _ ≤ (Real.pi * |u.im| * (R/64)) * (2/R) := mul_le_mul_of_nonneg_left hbR hpos
          _ = Real.pi * |u.im|/32 := by field_simp; ring
      linarith [h3, h4]
    nlinarith [hdecomp, h2, hLp_le, Real.pi_lt_d2, Real.pi_pos, hH, abs_nonneg u.im, hlogR_pos]
  exact ⟨hYle, hxge, by rw [hb] at hbge; linarith⟩

end Work.PARIMPL2.Direct
