import Mathlib
import Submission.Work.Smooth.SphereJordan.Vendored.frontierUncovered
import Submission.Work.Smooth.SphereJordan.Vendored.localArcTangency

/-!
# The tangency configuration at a frontier point

If at a frontier point `x` of `S = ⋃ w ∈ Q, closedBall w r` there is no *strictly* free unit
direction (`∃ u, ‖u‖ = 1 ∧ ∀ w ∈ Q, dist x w = r → ⟪u, w - x⟫ < 0`), then there are two
*antipodal* active centres `a`, `b` and a unit direction `u₀` perpendicular to `a - x` which is
non-positive on every active centre and strictly negative on every active centre except `a`, `b`.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

open scoped Classical

/-- **A one-sided tangency configuration is generic.**  If `u₀` is a unit direction which is
non-positive on every active centre and whose vanishing active centres all have *positive*
imaginary part, then some unit direction is strictly negative on every active centre. -/
theorem exists_free_of_oneSided {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x u₀ : ℂ} {v : ℝ}
    (hu₀ : ‖u₀‖ = 1) (hle : ∀ w ∈ actC Q r x, (star u₀ * (w - x)).re ≤ 0)
    (hv : v = 1 ∨ v = -1)
    (hpos : ∀ w ∈ actC Q r x, (star u₀ * (w - x)).re = 0 → 0 < v * (star u₀ * (w - x)).im) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ w ∈ actC Q r x, (star u * (w - x)).re < 0 := by
  classical
  have hv1 : |v| = 1 := by rcases hv with h | h <;> rw [h] <;> norm_num
  set D : Finset ℂ := (actC Q r x).filter (fun w => (star u₀ * (w - x)).re < 0) with hD
  have hDsub : ∀ w ∈ D, w ∈ actC Q r x ∧ (star u₀ * (w - x)).re < 0 := fun w hw => by
    rw [hD] at hw
    exact ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  set δ : ℝ := if h : D.Nonempty then D.inf' h (fun w => -((star u₀ * (w - x)).re)) else 1
    with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    split_ifs with h
    · refine (Finset.lt_inf'_iff h (f := fun w => -((star u₀ * (w - x)).re))).mpr ?_
      intro w hw
      have h1 : (star u₀ * (w - x)).re < 0 := (hDsub w hw).2
      linarith
    · norm_num
  have hδle : ∀ w ∈ D, δ ≤ -((star u₀ * (w - x)).re) := by
    intro w hw
    rw [hδdef]
    split_ifs with h
    · exact Finset.inf'_le (fun w => -((star u₀ * (w - x)).re)) hw
    · exact absurd ⟨w, hw⟩ h
  set ε : ℝ := min (1 / 2) (δ / (4 * r)) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hδpos (by linarith))
  have hε12 : ε ≤ 1 / 2 := min_le_left _ _
  have hεδ : ε ≤ δ / (4 * r) := min_le_right _ _
  have hsin : Real.sin ε ≤ ε := le_of_lt (Real.sin_lt hε0)
  have hcos : 1 - ε ^ 2 / 2 ≤ Real.cos ε := Real.one_sub_sq_div_two_le_cos
  have hcos34 : (3 / 4 : ℝ) ≤ Real.cos ε := by
    have h2 : ε ^ 2 / 2 ≤ (1 / 8 : ℝ) := by nlinarith [hε12, hε0]
    linarith
  have hsinpos : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε0 (by linarith [hε12, Real.pi_gt_three])
  refine ⟨u₀ * eicC (-(v * ε)), by rw [norm_mul, hu₀, norm_eicC, mul_one], fun w hw => ?_⟩
  set f : ℂ := star u₀ * (w - x) with hfdef
  have hfw : (star (u₀ * eicC (-(v * ε))) * (w - x)).re
      = Real.cos ε * f.re - v * Real.sin ε * f.im := by
    have h1 : star (u₀ * eicC (-(v * ε))) = star (eicC (-(v * ε))) * star u₀ := star_mul _ _
    have h2 : (eicC (-(v * ε))).re = Real.cos ε := by
      rw [eicC_re]
      rcases hv with h | h
      · rw [h, one_mul, Real.cos_neg]
      · rw [h, neg_one_mul, Real.cos_neg, Real.cos_neg]
    have h3 : (eicC (-(v * ε))).im = -v * Real.sin ε := by
      rw [eicC_im]
      rcases hv with h | h
      · rw [h, one_mul, Real.sin_neg]; ring
      · rw [h, neg_one_mul, neg_neg]; ring
    rw [h1, mul_assoc, ← hfdef, star_mul_re, h2, h3]
    ring
  have himr : |f.im| ≤ r := by
    have h4 := Complex.abs_im_le_norm f
    have h5 : ‖f‖ = r := by rw [hfdef]; exact norm_star_mul_sub hu₀ hw
    linarith
  rcases lt_trichotomy f.re 0 with h1 | h1 | h1
  · have hwD : w ∈ D := by rw [hD]; exact Finset.mem_filter.mpr ⟨hw, h1⟩
    have h2 : δ ≤ -f.re := by
      rw [hfdef]
      exact hδle w hwD
    have h7 : Real.sin ε * r ≤ δ / 4 := by
      have h8 : Real.sin ε ≤ δ / (4 * r) := le_trans hsin hεδ
      calc Real.sin ε * r ≤ (δ / (4 * r)) * r := mul_le_mul_of_nonneg_right h8 (le_of_lt hr)
        _ = δ / 4 := by field_simp
    have h9 : δ / 4 < Real.cos ε * δ := by
      have h10 : (3 / 4 : ℝ) * δ ≤ Real.cos ε * δ :=
        mul_le_mul_of_nonneg_right hcos34 (le_of_lt hδpos)
      linarith
    have h11 : Real.cos ε * f.re ≤ Real.cos ε * (-δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h12 : -v * f.im ≤ r := by
      have h12a : -v * f.im = -(v * f.im) := by ring
      rw [h12a]
      calc -(v * f.im) ≤ |v * f.im| := neg_le_abs _
        _ = |v| * |f.im| := by rw [abs_mul]
        _ = |f.im| := by rw [hv1, one_mul]
        _ ≤ r := himr
    have h13 : -(v * Real.sin ε * f.im) ≤ Real.sin ε * r := by
      have h14 : v * Real.sin ε * f.im = Real.sin ε * (v * f.im) := by ring
      rw [h14]
      nlinarith [h12, hsinpos, hsin]
    rw [hfw]
    have h15 : Real.cos ε * f.re - v * Real.sin ε * f.im
        = Real.cos ε * f.re + -(v * Real.sin ε * f.im) := by ring
    rw [h15]
    linarith
  · have h4 : 0 < v * f.im := hpos w hw (by rw [hfdef] at h1; exact h1)
    have him : |f.im| = r := by
      rw [hfdef]
      exact abs_im_of_re_eq_zero (by rw [hfdef] at h1; exact h1) (norm_star_mul_sub hu₀ hw)
    have h5 : v * f.im = r := by
      have h6 : |v * f.im| = r := by rw [abs_mul, hv1, one_mul, him]
      rw [← h6, abs_of_pos h4]
    have h7 : Real.cos ε * f.re - v * Real.sin ε * f.im = -(Real.sin ε * r) := by
      rw [h1, mul_zero, zero_sub]
      rw [show v * Real.sin ε * f.im = Real.sin ε * (v * f.im) from by ring, h5]
    rw [hfw, h7]
    exact neg_lt_zero.mpr (mul_pos hsinpos hr)
  · exfalso
    exact absurd h1 (not_lt.mpr (by rw [hfdef]; exact hle w hw))

/-- **The tangency configuration.** -/
theorem tangencyPair_of_not_generic {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r))
    (hgen : ¬ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ w ∈ Q, dist x w = r → (star u * (w - x)).re < 0) :
    ∃ a b u₀ : ℂ, a ∈ Q ∧ b ∈ Q ∧ dist x a = r ∧ dist x b = r ∧ b - x = -(a - x) ∧
      ‖u₀‖ = 1 ∧ u₀ = Complex.I * ((a - x) / (r : ℂ)) ∧ (star u₀ * (a - x)).re = 0 ∧
      ∀ w ∈ Q, dist x w = r → w ≠ a → w ≠ b → (star u₀ * (w - x)).re < 0 := by
  classical
  have hA : (actC Q r x).Nonempty := actC_nonempty hr hx
  obtain ⟨u₀, hu₀, hle⟩ := exists_uncovered_direction (P := Q) hr (by rwa [ballU])
  have hle' : ∀ w ∈ actC Q r x, (star u₀ * (w - x)).re ≤ 0 := fun w hw =>
    hle w (mem_actC.mp hw).1 (mem_actC.mp hw).2
  have hZne : ∃ w ∈ actC Q r x, (star u₀ * (w - x)).re = 0 := by
    by_contra hcon
    push_neg at hcon
    refine hgen ⟨u₀, hu₀, fun w hwQ hwr => ?_⟩
    exact lt_of_le_of_ne (hle w hwQ hwr) (hcon w (mem_actC.mpr ⟨hwQ, hwr⟩))
  have hneg : ∃ w ∈ actC Q r x, (star u₀ * (w - x)).re = 0 ∧ (star u₀ * (w - x)).im < 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨u, hu, hlt⟩ := exists_free_of_oneSided (v := 1) hr hu₀ hle' (Or.inl rfl)
      (fun w hw hre => by
        have h1 : 0 ≤ (star u₀ * (w - x)).im := hcon w hw hre
        have h2 : ‖star u₀ * (w - x)‖ = r := norm_star_mul_sub hu₀ hw
        have h3 : |(star u₀ * (w - x)).im| = r := abs_im_of_re_eq_zero hre h2
        have h4 : (star u₀ * (w - x)).im ≠ 0 := by
          intro h5
          rw [h5, abs_zero] at h3
          linarith
        have h6 : 0 < (star u₀ * (w - x)).im := lt_of_le_of_ne h1 (Ne.symm h4)
        simpa using h6)
    exact hgen ⟨u, hu, fun w hwQ hwr => hlt w (mem_actC.mpr ⟨hwQ, hwr⟩)⟩
  have hpos : ∃ w ∈ actC Q r x, (star u₀ * (w - x)).re = 0 ∧ 0 < (star u₀ * (w - x)).im := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨u, hu, hlt⟩ := exists_free_of_oneSided (v := -1) hr hu₀ hle' (Or.inr rfl)
      (fun w hw hre => by
        have h1 : (star u₀ * (w - x)).im ≤ 0 := hcon w hw hre
        have h2 : ‖star u₀ * (w - x)‖ = r := norm_star_mul_sub hu₀ hw
        have h3 : |(star u₀ * (w - x)).im| = r := abs_im_of_re_eq_zero hre h2
        have h4 : (star u₀ * (w - x)).im ≠ 0 := by
          intro h5
          rw [h5, abs_zero] at h3
          linarith
        have h6 : (star u₀ * (w - x)).im < 0 := lt_of_le_of_ne h1 h4
        show 0 < (-1 : ℝ) * (star u₀ * (w - x)).im
        linarith)
    exact hgen ⟨u, hu, fun w hwQ hwr => hlt w (mem_actC.mpr ⟨hwQ, hwr⟩)⟩
  have hu0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu₀
    norm_num at hu₀
  obtain ⟨a, ha, ha0, haim⟩ := hneg
  obtain ⟨b, hb, hb0, hbim⟩ := hpos
  have haQ : a ∈ Q := (mem_actC.mp ha).1
  have hbQ : b ∈ Q := (mem_actC.mp hb).1
  have har : dist x a = r := (mem_actC.mp ha).2
  have hbr : dist x b = r := (mem_actC.mp hb).2
  have hima : (star u₀ * (a - x)).im = -r := by
    have h2 : |(star u₀ * (a - x)).im| = r := abs_im_of_re_eq_zero ha0 (norm_star_mul_sub hu₀ ha)
    rw [abs_of_neg haim] at h2
    linarith
  have himb : (star u₀ * (b - x)).im = r := by
    have h2 : |(star u₀ * (b - x)).im| = r := abs_im_of_re_eq_zero hb0 (norm_star_mul_sub hu₀ hb)
    rw [abs_of_pos hbim] at h2
    exact h2
  have hfa : star u₀ * (a - x) = -((r : ℂ) * Complex.I) := by
    have hr0 : ((r : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      ring
    have hr1 : ((r : ℂ) * Complex.I).im = r := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
      ring
    refine Complex.ext ?_ ?_
    · rw [ha0, Complex.neg_re, hr0, neg_zero]
    · rw [hima, Complex.neg_im, hr1]
  have hfb : star u₀ * (b - x) = (r : ℂ) * Complex.I := by
    have hr0 : ((r : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      ring
    have hr1 : ((r : ℂ) * Complex.I).im = r := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
      ring
    refine Complex.ext ?_ ?_
    · rw [hb0, hr0]
    · rw [himb, hr1]
  have hab : b - x = -(a - x) := by
    have h1 : u₀ * star u₀ = 1 := mul_star_self hu₀
    have h2 : a - x = u₀ * (star u₀ * (a - x)) := by rw [← mul_assoc, h1, one_mul]
    have h3 : b - x = u₀ * (star u₀ * (b - x)) := by rw [← mul_assoc, h1, one_mul]
    rw [h2, h3, hfa, hfb]
    ring
  have hdir : u₀ = Complex.I * ((a - x) / (r : ℂ)) := by
    have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    have h1 : u₀ * star u₀ = 1 := mul_star_self hu₀
    have h2 : a - x = u₀ * (star u₀ * (a - x)) := by rw [← mul_assoc, h1, one_mul]
    have h3 : a - x = -((r : ℂ) * Complex.I) * u₀ := by
      rw [h2, hfa]; ring
    rw [h3]
    have h4 : -((r : ℂ) * Complex.I) * u₀ / (r : ℂ) = -(Complex.I * u₀) := by
      field_simp
    rw [h4]
    rw [show Complex.I * (-(Complex.I * u₀)) = -(Complex.I * Complex.I * u₀) from by ring,
      Complex.I_mul_I]
    ring
  refine ⟨a, b, u₀, haQ, hbQ, har, hbr, hab, hu₀, hdir, ha0, ?_⟩
  intro w hwQ hwr hwa hwb
  have hw : w ∈ actC Q r x := mem_actC.mpr ⟨hwQ, hwr⟩
  have hwle : (star u₀ * (w - x)).re ≤ 0 := hle w hwQ hwr
  rcases lt_trichotomy ((star u₀ * (w - x)).re) 0 with h | h | h
  · exact h
  · exfalso
    have h2 : |(star u₀ * (w - x)).im| = r := abs_im_of_re_eq_zero h (norm_star_mul_sub hu₀ hw)
    have h3 : (star u₀ * (w - x)).im = r ∨ (star u₀ * (w - x)).im = -r := by
      rcases le_total 0 ((star u₀ * (w - x)).im) with h4 | h4
      · left
        rw [abs_of_nonneg h4] at h2
        exact h2
      · right
        rw [abs_of_nonpos h4] at h2
        linarith
    rcases h3 with h6 | h6
    · have h7 : star u₀ * (w - x) = star u₀ * (b - x) := by
        rw [hfb]
        exact Complex.ext
          (by rw [h, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_im]; ring)
          (by rw [h6, Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re]; ring)
      have h8 : w = b := by
        have h10 : u₀ * (star u₀ * (w - x)) = u₀ * (star u₀ * (b - x)) := by rw [h7]
        rw [← mul_assoc, ← mul_assoc, mul_star_self hu₀, one_mul, one_mul] at h10
        linear_combination h10
      exact hwb h8
    · have h7 : star u₀ * (w - x) = star u₀ * (a - x) := by
        rw [hfa]
        exact Complex.ext
          (by rw [h, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_im]; ring)
          (by rw [h6, Complex.neg_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re]; ring)
      have h8 : w = a := by
        have h10 : u₀ * (star u₀ * (w - x)) = u₀ * (star u₀ * (a - x)) := by rw [h7]
        rw [← mul_assoc, ← mul_assoc, mul_star_self hu₀, one_mul, one_mul] at h10
        linear_combination h10
      exact hwa h8
  · exact absurd h (not_lt.mpr hwle)

end

end Work.Smooth.SphereJordan
