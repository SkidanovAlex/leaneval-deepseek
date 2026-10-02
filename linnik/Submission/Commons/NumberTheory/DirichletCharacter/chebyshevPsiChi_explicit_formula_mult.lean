import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_outside
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_truncatedPerron
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_tight
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.DirichletCharacter.horizontalSegment_logDeriv_bound_le_one
import Submission.Commons.NumberTheory.DirichletCharacter.horizontalGamma_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.leftEdge_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.goodHeight_separated
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInWindow_weighted_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_zeroSum_small_window_bound

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-! # Elementary contour-integral toolbox for the rectangle boundary -/

/-- The (counterclockwise) boundary integral over the axis-parallel rectangle. -/
abbrev rectInt (z w : ℂ) (f : ℂ → ℂ) : ℂ := Commons.NumberTheory.Zeta.rectInt z w f

lemma rectInt_eq_def (z w : ℂ) (f : ℂ → ℂ) :
    rectInt z w f =
      (∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I)) -
      (∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I * (∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I * (∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I)) := rfl

/-- The closed rectangle as a subset of `ℂ`. -/
def rectSet (z w : ℂ) : Set ℂ := (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)

lemma mem_rectSet {z w s : ℂ} (hre : s.re ∈ Set.uIcc z.re w.re)
    (him : s.im ∈ Set.uIcc z.im w.im) : s ∈ rectSet z w :=
  Complex.mem_reProdIm.mpr ⟨hre, him⟩

/-- The boundary of the axis-parallel rectangle. -/
def rectBoundary (z w : ℂ) : Set ℂ :=
  {s : ℂ | (s.re ∈ Set.uIcc z.re w.re ∧ (s.im = z.im ∨ s.im = w.im)) ∨
           (s.im ∈ Set.uIcc z.im w.im ∧ (s.re = z.re ∨ s.re = w.re))}

lemma rectSet_mem_nhds {z w s : ℂ}
    (h1 : z.re < s.re) (h2 : s.re < w.re) (h3 : z.im < s.im) (h4 : s.im < w.im) :
    rectSet z w ∈ 𝓝 s := by
  have h1' : (Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im) ∈ 𝓝 s := by
    apply IsOpen.mem_nhds (isOpen_Ioo.reProdIm isOpen_Ioo)
    exact Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact Filter.mem_of_superset h1' (fun t ht => by
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp ht
    exact mem_rectSet (by
        rw [Set.uIcc_of_le (le_of_lt (h1.trans h2))]
        exact Set.Ioo_subset_Icc_self hre) (by
        rw [Set.uIcc_of_le (le_of_lt (h3.trans h4))]
        exact Set.Ioo_subset_Icc_self him))

/-- A boundary point of a rectangle with `0` strictly inside is nonzero. -/
lemma ne_zero_of_mem_rectBoundary {z w s : ℂ}
    (h1 : z.re < 0) (h2 : 0 < w.re) (h3 : z.im < 0) (h4 : 0 < w.im)
    (hs : s ∈ rectBoundary z w) : s ≠ 0 := by
  intro h
  have him : s.im = 0 := by rw [h]; rfl
  have hre : s.re = 0 := by rw [h]; rfl
  rcases hs with ⟨-, him' | him'⟩ | ⟨-, hre' | hre'⟩
  · rw [him'] at him; linarith only [h3, him]
  · rw [him'] at him; linarith only [h4, him]
  · rw [hre'] at hre; linarith only [h1, hre]
  · rw [hre'] at hre; linarith only [h2, hre]

/-- A boundary point of a rectangle is different from every strictly interior point. -/
lemma ne_of_mem_rectBoundary_of_inside {z w u s : ℂ}
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im)
    (hs : s ∈ rectBoundary z w) : s ≠ u := by
  intro h
  have him : s.im = u.im := by rw [h]
  have hre : s.re = u.re := by rw [h]
  rcases hs with ⟨-, him' | him'⟩ | ⟨-, hre' | hre'⟩
  · rw [him'] at him; exact absurd him (ne_of_lt huin.2.2.1)
  · rw [him'] at him; exact absurd him (ne_of_lt huin.2.2.2).symm
  · rw [hre'] at hre; exact absurd hre (ne_of_lt huin.1)
  · rw [hre'] at hre; exact absurd hre (ne_of_lt huin.2.1).symm

lemma rectBoundary_subset_rectSet {z w s : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hs : s ∈ rectBoundary z w) : s ∈ rectSet z w := by
  rcases hs with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
  · refine mem_rectSet hre ?_
    rw [Set.uIcc_of_le (le_of_lt hzim), him]
    exact ⟨le_rfl, le_of_lt hzim⟩
  · refine mem_rectSet hre ?_
    rw [Set.uIcc_of_le (le_of_lt hzim), him]
    exact ⟨le_of_lt hzim, le_rfl⟩
  · refine mem_rectSet ?_ him
    rw [Set.uIcc_of_le (le_of_lt hzre), hre]
    exact ⟨le_rfl, le_of_lt hzre⟩
  · refine mem_rectSet ?_ him
    rw [Set.uIcc_of_le (le_of_lt hzre), hre]
    exact ⟨le_of_lt hzre, le_rfl⟩

lemma notMem_rectSet_of_outside {z w u : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) : u ∉ rectSet z w := by
  intro hu
  have hre := (Complex.mem_reProdIm.mp hu).1
  have him := (Complex.mem_reProdIm.mp hu).2
  rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
  rw [Set.uIcc_of_le (le_of_lt hzim)] at him
  rcases huout with h | h | h | h
  · linarith only [hre.1, h, hre]
  · linarith only [hre.2, h, hre]
  · linarith only [him.1, h, him]
  · linarith only [him.2, h, him]

/-! ## Cauchy–Goursat and Cauchy's formula on the rectangle -/

lemma rectInt_eq_zero_of_differentiableOn {z w : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (rectSet z w)) : rectInt z w f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf
  simp only [rectInt_eq_def]
  simpa only [smul_eq_mul] using h

lemma rectInt_congr_boundary' {z w : ℂ} {f g : ℂ → ℂ}
    (h : ∀ s ∈ rectBoundary z w, f s = g s) : rectInt z w f = rectInt z w g := by
  apply Commons.NumberTheory.Zeta.rectInt_congr_boundary <;> intro t ht
  · exact h _ (Or.inl ⟨by simpa using ht, Or.inl (by simp)⟩)
  · exact h _ (Or.inl ⟨by simpa using ht, Or.inr (by simp)⟩)
  · exact h _ (Or.inr ⟨by simpa using ht, Or.inr (by simp)⟩)
  · exact h _ (Or.inr ⟨by simpa using ht, Or.inl (by simp)⟩)

/-- The four edge integrals are interval integrable when the integrand is continuous on the
closed rectangle. -/
lemma edgeIntegrable_of_continuousOn {z w : ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (rectSet z w)) :
    (IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re) ∧
    (IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) volume z.re w.re) ∧
    (IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im) ∧
    (IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) volume z.im w.im) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun x hx =>
      mem_rectSet (by simpa using hx) (by simp [Set.left_mem_uIcc]))
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun x hx =>
      mem_rectSet (by simpa using hx) (by simp [Set.right_mem_uIcc]))
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun y hy =>
      mem_rectSet (by simp [Set.right_mem_uIcc]) (by simpa using hy))
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun y hy =>
      mem_rectSet (by simp [Set.left_mem_uIcc]) (by simpa using hy))

/-- The four edge integrals are interval integrable when the integrand is continuous away from a
point `u` strictly inside the rectangle. -/
lemma edgeIntegrable_of_continuousOn_ne {z w u : ℂ} {f : ℂ → ℂ}
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im)
    (hf : ContinuousOn f {s : ℂ | s ≠ u}) :
    (IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re) ∧
    (IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) volume z.re w.re) ∧
    (IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im) ∧
    (IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) volume z.im w.im) := by
  have hne_bottom : ∀ x ∈ Set.uIcc z.re w.re, (x + z.im * Complex.I) ≠ u := by
    intro t ht h
    have him : ((t : ℂ) + z.im * Complex.I).im = z.im := by simp
    have hzu : z.im = u.im := by
      have h' := congrArg Complex.im h
      rw [him] at h'
      exact_mod_cast h'
    exact (ne_of_lt huin.2.2.1) hzu
  have hne_top : ∀ x ∈ Set.uIcc z.re w.re, (x + w.im * Complex.I) ≠ u := by
    intro t ht h
    have him : ((t : ℂ) + w.im * Complex.I).im = w.im := by simp
    have hwu : w.im = u.im := by
      have h' := congrArg Complex.im h
      rw [him] at h'
      exact_mod_cast h'
    exact (ne_of_lt huin.2.2.2).symm hwu
  have hne_right : ∀ y ∈ Set.uIcc z.im w.im, (w.re + y * Complex.I) ≠ u := by
    intro t ht h
    have hre : ((w.re : ℂ) + (t : ℂ) * Complex.I).re = w.re := by simp
    have hwu : w.re = u.re := by
      have h' := congrArg Complex.re h
      rw [hre] at h'
      exact_mod_cast h'
    exact (ne_of_lt huin.2.1).symm hwu
  have hne_left : ∀ y ∈ Set.uIcc z.im w.im, (z.re + y * Complex.I) ≠ u := by
    intro t ht h
    have hre : ((z.re : ℂ) + (t : ℂ) * Complex.I).re = z.re := by simp
    have hzu : z.re = u.re := by
      have h' := congrArg Complex.re h
      rw [hre] at h'
      exact_mod_cast h'
    exact (ne_of_lt huin.1) hzu
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun x hx => hne_bottom x hx)
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun x hx => hne_top x hx)
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun y hy => hne_right y hy)
  · apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun y hy => hne_left y hy)

/-- Scalar multiplication for `rectInt`. -/
lemma rectInt_const_mul' {z w : ℂ} (c : ℂ) (f : ℂ → ℂ) :
    rectInt z w (fun s => c * f s) = c * rectInt z w f := by
  simp only [rectInt_eq_def]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- Additivity of `rectInt` with explicit edge integrability. -/
lemma rectInt_add'' {z w : ℂ} {f g : ℂ → ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * Complex.I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * Complex.I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * Complex.I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * Complex.I)) volume z.im w.im) :
    rectInt z w (fun s => f s + g s) = rectInt z w f + rectInt z w g := by
  simp only [rectInt_eq_def]
  rw [intervalIntegral.integral_add hf1 hg1, intervalIntegral.integral_add hf2 hg2,
      intervalIntegral.integral_add hf3 hg3, intervalIntegral.integral_add hf4 hg4]
  ring

/-- `rectInt` of `c/(s-u)` when `u` is strictly inside: `2πic`. -/
lemma rectInt_const_div_sub_inside {z w u : ℂ} (c : ℂ) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectInt z w (fun s => c / (s - u)) = c * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h1 : rectInt z w (fun s => c / (s - u)) = c * rectInt z w (fun s => (s - u)⁻¹) := by
    rw [← rectInt_const_mul' c (fun s : ℂ => (s - u)⁻¹)]
    apply Commons.NumberTheory.Zeta.rectInt_congr_boundary <;> intro t ht <;> simp [div_eq_mul_inv]
  rw [h1]
  congr 1
  change Commons.NumberTheory.Zeta.rectInt z w (fun s : ℂ => (s - u)⁻¹) =
    2 * (Real.pi : ℂ) * Complex.I
  unfold Commons.NumberTheory.Zeta.rectInt
  convert Commons.Analysis.Complex.rectIntegral_sub_inv_inside (z := z) (w := w) (u := u)
    hzre hzim huin using 1 <;> simp

/-- `rectInt` of `c/(s-u)` when `u` is strictly outside: `0`. -/
lemma rectInt_const_div_sub_outside {z w u : ℂ} (c : ℂ) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) :
    rectInt z w (fun s => c / (s - u)) = 0 := by
  have h1 : rectInt z w (fun s => c / (s - u)) = c * rectInt z w (fun s => (s - u)⁻¹) := by
    rw [← rectInt_const_mul' c (fun s : ℂ => (s - u)⁻¹)]
    apply Commons.NumberTheory.Zeta.rectInt_congr_boundary <;> intro t ht <;> simp [div_eq_mul_inv]
  rw [h1]
  have h0 : rectInt z w (fun s : ℂ => (s - u)⁻¹) = 0 := by
    change Commons.NumberTheory.Zeta.rectInt z w (fun s : ℂ => (s - u)⁻¹) = 0
    unfold Commons.NumberTheory.Zeta.rectInt
    convert Commons.Analysis.Complex.rectIntegral_sub_inv_outside (z := z) (w := w) (u := u)
      hzre hzim huout using 1 <;> simp
  rw [h0, mul_zero]

/-! ## Integrals of `1/s` and `1/s²` -/

lemma integral_inv_sq_add_const {a b : ℝ} {c : ℂ} (hc : c.im ≠ 0) :
    (∫ x : ℝ in a..b, (1 : ℂ) / ((x : ℂ) + c) ^ 2)
      = -(1 / ((b : ℂ) + c)) + (1 / ((a : ℂ) + c)) := by
  have key : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (-1 : ℂ) / ((t : ℂ) + c))
      ((1 : ℂ) / ((t : ℂ) + c) ^ 2) t := by
    intro t
    have hg : HasDerivAt (fun s : ℝ => ((s : ℂ) + c)) 1 t := by
      have h := (hasDerivAt_id (t : ℂ)).comp_ofReal
      simpa using h.add_const c
    have hne : ((t : ℂ) + c) ≠ 0 := by
      intro h
      have him : (((t : ℂ) + c)).im = c.im := by simp
      exact hc (by simpa [him] using congrArg Complex.im h)
    have hmul := (hg.inv hne).const_mul (-1 : ℂ)
    simpa [Pi.inv_apply, Pi.mul_apply, one_div, inv_pow, neg_mul, mul_neg, neg_neg, neg_div]
      using hmul
  have hcont : ContinuousOn (fun t : ℝ => (1 : ℂ) / ((t : ℂ) + c) ^ 2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro t ht
      have hne : ((t : ℂ) + c) ≠ 0 := by
        intro h
        have him : (((t : ℂ) + c)).im = c.im := by simp
        exact hc (by simpa [him] using congrArg Complex.im h)
      exact pow_ne_zero 2 hne
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => key t)
    hcont.intervalIntegrable
  rw [this]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

lemma integral_I_div_sq_add_const {a b : ℝ} {c : ℂ} (hc : c.re ≠ 0) :
    (∫ y : ℝ in a..b, (1 : ℂ) / (c + (y : ℂ) * Complex.I) ^ 2)
      = Complex.I * ((1 : ℂ) / (c + (b : ℂ) * Complex.I) - (1 : ℂ) / (c + (a : ℂ) * Complex.I)) := by
  have key : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.I / (c + (t : ℂ) * Complex.I))
      ((1 : ℂ) / (c + (t : ℂ) * Complex.I) ^ 2) t := by
    intro t
    have hg : HasDerivAt (fun s : ℝ => (c + (s : ℂ) * Complex.I)) Complex.I t := by
      have h := (hasDerivAt_id (t : ℂ)).comp_ofReal
      have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
        simpa [mul_comm] using h.mul_const Complex.I
      simpa using h2.const_add c
    have hne : (c + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hre : ((c + (t : ℂ) * Complex.I)).re = c.re := by simp
      exact hc (by simpa [hre] using congrArg Complex.re h)
    have hmul := (hg.inv hne).const_mul Complex.I
    have hderiv : Complex.I * (-(1 * ((c + (t : ℂ) * Complex.I)⁻¹) ^ 2) * Complex.I)
        = (1 : ℂ) / (c + (t : ℂ) * Complex.I) ^ 2 := by
      have h1 : Complex.I * (-(1 * ((c + (t : ℂ) * Complex.I)⁻¹) ^ 2) * Complex.I)
          = -((Complex.I * Complex.I) * ((c + (t : ℂ) * Complex.I)⁻¹) ^ 2) := by ring
      rw [h1, Complex.I_mul_I, one_div, inv_pow]
      ring
    have hII : ∀ w : ℂ, -(Complex.I * (Complex.I * w)) = w := fun w => by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    simpa [Pi.inv_apply, Pi.mul_apply, hderiv, div_eq_mul_inv, one_mul, hII] using hmul
  have hcont : ContinuousOn (fun t : ℝ => (1 : ℂ) / (c + (t : ℂ) * Complex.I) ^ 2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro t ht
      have hne : (c + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre : ((c + (t : ℂ) * Complex.I)).re = c.re := by simp
        exact hc (by simpa [hre] using congrArg Complex.re h)
      exact pow_ne_zero 2 hne
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => key t) hcont.intervalIntegrable
  rw [this]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

lemma rectInt_one_div_self {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s : ℂ => 1 / s) = 2 * (Real.pi : ℂ) * Complex.I := by
  change Commons.NumberTheory.Zeta.rectInt z w (fun s : ℂ => 1 / s) =
    2 * (Real.pi : ℂ) * Complex.I
  unfold Commons.NumberTheory.Zeta.rectInt
  convert Commons.Analysis.Complex.rectIntegral_sub_inv_inside (z := z) (w := w) (u := 0)
    hzre hzim huin using 1 <;> simp [sub_zero, one_div]

lemma rectInt_one_div_self_sq {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s : ℂ => 1 / s ^ 2) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := huin
  have hbc := integral_inv_sq_add_const (a := z.re) (b := w.re) (c := (z.im : ℂ) * Complex.I)
    (by simpa using ne_of_lt h3)
  have htc := integral_inv_sq_add_const (a := z.re) (b := w.re) (c := (w.im : ℂ) * Complex.I)
    (by simpa using ne_of_gt h4)
  have hrc := integral_I_div_sq_add_const (a := z.im) (b := w.im) (c := (w.re : ℂ))
    (by simpa using ne_of_gt h2)
  have hlc := integral_I_div_sq_add_const (a := z.im) (b := w.im) (c := (z.re : ℂ))
    (by simpa using ne_of_lt h1)
  have hII : ∀ X : ℂ, Complex.I * (Complex.I * X) = -X := fun X => by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  change Commons.NumberTheory.Zeta.rectInt z w (fun s : ℂ => 1 / s ^ 2) = 0
  unfold Commons.NumberTheory.Zeta.rectInt
  simp only [hbc, htc, hrc, hlc, smul_eq_mul, hII]
  ring

/-! ## Cauchy's formula on the rectangle -/

lemma differentiableOn_dslope_of_differentiableOn {z w : ℂ} {f : ℂ → ℂ} {c : ℂ}
    (hc : rectSet z w ∈ 𝓝 c) (hf : DifferentiableOn ℂ f (rectSet z w)) :
    DifferentiableOn ℂ (dslope f c) (rectSet z w) :=
  (Complex.differentiableOn_dslope (f := f) (c := c) (s := rectSet z w) hc).mpr hf

lemma continuousOn_one_div_self :
    ContinuousOn (fun s : ℂ => (1 : ℂ) / s) {s : ℂ | s ≠ 0} := by
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro s hs
  exact hs

/-- **Cauchy formula on the rectangle**: `∮ f(s)/s ds = 2πi f(0)` for `f` analytic on the closed
rectangle and `0` strictly inside. -/
lemma rectInt_analytic_div_self {z w : ℂ} {f : ℂ → ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hf : DifferentiableOn ℂ f (rectSet z w)) :
    rectInt z w (fun s => f s / s) = f 0 * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h0in : z.re < (0 : ℂ).re ∧ (0 : ℂ).re < w.re ∧ z.im < (0 : ℂ).im ∧ (0 : ℂ).im < w.im := by
    simpa using huin
  have hn : rectSet z w ∈ 𝓝 (0 : ℂ) :=
    rectSet_mem_nhds huin.1 huin.2.1 huin.2.2.1 huin.2.2.2
  have hds : DifferentiableOn ℂ (dslope f 0) (rectSet z w) :=
    differentiableOn_dslope_of_differentiableOn hn hf
  have hcont : ContinuousOn (fun s : ℂ => dslope f 0 s) (rectSet z w) := hds.continuousOn
  have hcont1 : ContinuousOn (fun s : ℂ => f 0 * ((1 : ℂ) / s)) {s : ℂ | s ≠ 0} :=
    continuousOn_const.mul continuousOn_one_div_self
  have hcongr : rectInt z w (fun s => f s / s) =
      rectInt z w (fun s => f 0 * ((1 : ℂ) / s) + dslope f 0 s) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsne : s ≠ 0 := ne_zero_of_mem_rectBoundary huin.1 huin.2.1 huin.2.2.1 huin.2.2.2 hs
    rw [dslope_of_ne f hsne, slope_def_module]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  obtain ⟨e1, e2, e3, e4⟩ := edgeIntegrable_of_continuousOn_ne h0in hcont1
  obtain ⟨d1, d2, d3, d4⟩ := edgeIntegrable_of_continuousOn hcont
  rw [hcongr, rectInt_add'' e1 d1 e2 d2 e3 d3 e4 d4,
      rectInt_const_mul' (f 0) (fun s : ℂ => (1 : ℂ) / s), rectInt_eq_zero_of_differentiableOn hds,
      rectInt_one_div_self hzre hzim huin]
  ring

/-! ## Powers of `x` -/

lemma cpow_differentiable_of_pos {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have heq : (fun s : ℂ => (x : ℂ) ^ s) =
      fun s : ℂ => Complex.exp (Complex.log (x:ℂ) * s) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hx0]
  rw [heq]
  fun_prop

lemma dslope_cpow_differentiable {x : ℝ} (hx : 0 < x) (u : ℂ) :
    Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) u) := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s) Set.univ :=
    fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
  have hd' : DifferentiableOn ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) u) Set.univ :=
    (Complex.differentiableOn_dslope (f := (fun s : ℂ => (x : ℂ) ^ s)) (c := u)
      (s := Set.univ) (by simp : Set.univ ∈ 𝓝 u)).mpr hd
  intro s
  exact hd'.differentiableAt (x := s) (by simp)

lemma dslope_cpow_eq {x : ℝ} {u : ℂ} {s : ℂ} (hs : s ≠ u) :
    dslope (fun w : ℂ => (x : ℂ) ^ w) u s = ((x : ℂ) ^ s - (x : ℂ) ^ u) / (s - u) := by
  rw [dslope_of_ne (fun w : ℂ => (x : ℂ) ^ w) hs, slope_def_module]
  simp only [smul_eq_mul]
  field_simp

lemma dslope_cpow_zero {x : ℝ} (hx : 0 < x) :
    dslope (fun s : ℂ => (x : ℂ) ^ s) 0 0 = (Real.log x : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have heq : (fun s : ℂ => (x : ℂ) ^ s) =
      fun s : ℂ => Complex.exp (Complex.log (x:ℂ) * s) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hx0]
  have hderiv : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) (Real.log x : ℂ) 0 := by
    rw [heq]
    have h1 : HasDerivAt (fun s : ℂ => Complex.log (x:ℂ) * s) (Complex.log (x:ℂ)) 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).const_mul (Complex.log (x:ℂ))
    have h2 := h1.cexp
    simpa [Complex.ofReal_log (le_of_lt hx)] using h2
  rw [dslope_same]
  exact hderiv.deriv

/-! ## The elementary contour integrals -/

variable {x : ℝ}

lemma rectInt_cpow_div_self {z w : ℂ} (hx : 0 < x) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s => (x : ℂ) ^ s / s) = 2 * (Real.pi : ℂ) * Complex.I := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s) (rectSet z w) :=
    fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
  have h := rectInt_analytic_div_self hzre hzim huin hd
  simpa using h

lemma rectInt_cpow_div_self_sq {z w : ℂ} (hx : 0 < x) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s => (x : ℂ) ^ s / s ^ 2) =
      (Real.log x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hφ : DifferentiableOn ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) 0) (rectSet z w) := by
    have hd : Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) 0) :=
      dslope_cpow_differentiable hx 0
    exact fun s _ => (hd s).differentiableWithinAt
  have h0in : z.re < (0 : ℂ).re ∧ (0 : ℂ).re < w.re ∧ z.im < (0 : ℂ).im ∧ (0 : ℂ).im < w.im := by
    simpa using huin
  have hcont1 : ContinuousOn (fun s : ℂ => dslope (fun t : ℂ => (x : ℂ) ^ t) 0 s / s)
      {s : ℂ | s ≠ 0} := by
    apply ContinuousOn.div
    · exact (dslope_cpow_differentiable hx 0).continuous.continuousOn
    · fun_prop
    · intro s hs; exact hs
  have hcont2 : ContinuousOn (fun s : ℂ => (1 : ℂ) / s ^ 2) {s : ℂ | s ≠ 0} := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro s hs; exact pow_ne_zero 2 hs
  have hcongr : rectInt z w (fun s => (x : ℂ) ^ s / s ^ 2) =
      rectInt z w (fun s => dslope (fun t : ℂ => (x : ℂ) ^ t) 0 s / s + (1 : ℂ) / s ^ 2) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsne : s ≠ 0 := ne_zero_of_mem_rectBoundary huin.1 huin.2.1 huin.2.2.1 huin.2.2.2 hs
    rw [dslope_of_ne (fun t : ℂ => (x : ℂ) ^ t) hsne, slope_def_module]
    simp only [sub_zero, smul_eq_mul]
    rw [Complex.cpow_zero, one_div]
    field_simp
    ring
  obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne h0in hcont1
  obtain ⟨b1, b2, b3, b4⟩ := edgeIntegrable_of_continuousOn_ne h0in hcont2
  rw [hcongr, rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4,
      rectInt_analytic_div_self hzre hzim huin hφ,
      rectInt_one_div_self_sq hzre hzim huin,
      dslope_cpow_zero hx]
  ring

lemma rectInt_cpow_div_sub_inside {z w u : ℂ} (hx : 0 < x) (hzre : z.re < w.re)
    (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectInt z w (fun s => (x : ℂ) ^ s / (s - u)) = (x : ℂ) ^ u * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hds : Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) u) :=
    dslope_cpow_differentiable hx u
  have hd : DifferentiableOn ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) u) (rectSet z w) :=
    fun s _ => (hds s).differentiableWithinAt
  have hcont : ContinuousOn (fun s : ℂ => dslope (fun t : ℂ => (x : ℂ) ^ t) u s) (rectSet z w) :=
    hd.continuousOn
  have hcont_div : ContinuousOn (fun s : ℂ => (x : ℂ) ^ u / (s - u)) {s : ℂ | s ≠ u} :=
    continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
  have hcongr : rectInt z w (fun s => (x : ℂ) ^ s / (s - u)) =
      rectInt z w (fun s => (x : ℂ) ^ u / (s - u) + dslope (fun t : ℂ => (x : ℂ) ^ t) u s) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsne : s ≠ u := ne_of_mem_rectBoundary_of_inside huin hs
    rw [dslope_cpow_eq (x := x) (u := u) (s := s) hsne]
    field_simp
    ring
  obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne huin hcont_div
  obtain ⟨d1, d2, d3, d4⟩ := edgeIntegrable_of_continuousOn hcont
  rw [hcongr, rectInt_add'' a1 d1 a2 d2 a3 d3 a4 d4,
      rectInt_eq_zero_of_differentiableOn hd,
      rectInt_const_div_sub_inside ((x : ℂ) ^ u) hzre hzim huin]
  ring

lemma rectInt_cpow_div_sub_outside {z w u : ℂ} (hx : 0 < x) (hzre : z.re < w.re)
    (hzim : z.im < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) :
    rectInt z w (fun s => (x : ℂ) ^ s / (s - u)) = 0 := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s * ((s - u)⁻¹)) (rectSet z w) := by
    apply DifferentiableOn.mul
    · exact fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
    · apply DifferentiableOn.inv
      · fun_prop
      · intro s hs hzero
        rcases huout with h | h | h | h
        · have := (Complex.mem_reProdIm.mp hs).1
          rw [Set.uIcc_of_le (le_of_lt hzre)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.1, h, this]
        · have := (Complex.mem_reProdIm.mp hs).1
          rw [Set.uIcc_of_le (le_of_lt hzre)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.2, h, this]
        · have := (Complex.mem_reProdIm.mp hs).2
          rw [Set.uIcc_of_le (le_of_lt hzim)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.1, h, this]
        · have := (Complex.mem_reProdIm.mp hs).2
          rw [Set.uIcc_of_le (le_of_lt hzim)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.2, h, this]
  have hcongr : rectInt z w (fun s => (x : ℂ) ^ s / (s - u)) =
      rectInt z w (fun s => (x : ℂ) ^ s * ((s - u)⁻¹)) := by
    apply rectInt_congr_boundary'
    intro s hs
    rw [div_eq_mul_inv]
  rw [hcongr, rectInt_eq_zero_of_differentiableOn hd]

lemma rectInt_kernel_cpow_inside {z w u : ℂ} (hx : 0 < x) (hu0 : u ≠ 0)
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectInt z w (fun s => (1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s)) =
      (x : ℂ) ^ u / u * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hds : Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) u) :=
    dslope_cpow_differentiable hx u
  have hd : DifferentiableOn ℂ (fun s : ℂ => dslope (fun t : ℂ => (x : ℂ) ^ t) u s / u)
      (rectSet z w) := by
    apply DifferentiableOn.div
    · exact fun s _ => (hds s).differentiableWithinAt
    · fun_prop
    · intro s hs; exact hu0
  have hcont : ContinuousOn (fun s : ℂ => dslope (fun t : ℂ => (x : ℂ) ^ t) u s / u)
      (rectSet z w) := hd.continuousOn
  have hcont_div : ContinuousOn (fun s : ℂ => ((x : ℂ) ^ u / u) / (s - u)) {s : ℂ | s ≠ u} :=
    continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
  have hcongr : rectInt z w (fun s => (1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s)) =
      rectInt z w (fun s => ((x : ℂ) ^ u / u) / (s - u) +
        dslope (fun t : ℂ => (x : ℂ) ^ t) u s / u) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsne : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsune : s ≠ u := ne_of_mem_rectBoundary_of_inside huin hs
    rw [dslope_cpow_eq (x := x) (u := u) (s := s) hsune]
    field_simp
    ring
  obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne huin hcont_div
  obtain ⟨d1, d2, d3, d4⟩ := edgeIntegrable_of_continuousOn hcont
  rw [hcongr, rectInt_add'' a1 d1 a2 d2 a3 d3 a4 d4,
      rectInt_eq_zero_of_differentiableOn hd,
      rectInt_const_div_sub_inside ((x : ℂ) ^ u / u) hzre hzim huin]
  ring

lemma rectInt_kernel_cpow_outside {z w u : ℂ} (hx : 0 < x) (hu0 : u ≠ 0)
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) :
    rectInt z w (fun s => (1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s)) = 0 := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => (1 / u) * ((x : ℂ) ^ s * ((s - u)⁻¹)))
      (rectSet z w) := by
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.mul
    · exact fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
    · apply DifferentiableOn.inv
      · fun_prop
      · intro s hs hzero
        rcases huout with h | h | h | h
        · have := (Complex.mem_reProdIm.mp hs).1
          rw [Set.uIcc_of_le (le_of_lt hzre)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.1, h, this]
        · have := (Complex.mem_reProdIm.mp hs).1
          rw [Set.uIcc_of_le (le_of_lt hzre)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.2, h, this]
        · have := (Complex.mem_reProdIm.mp hs).2
          rw [Set.uIcc_of_le (le_of_lt hzim)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.1, h, this]
        · have := (Complex.mem_reProdIm.mp hs).2
          rw [Set.uIcc_of_le (le_of_lt hzim)] at this
          rw [sub_eq_zero.mp hzero] at this
          linarith only [this.2, h, this]
  have hcongr : rectInt z w (fun s => (1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s)) =
      rectInt z w (fun s : ℂ => (1 / u) * ((x : ℂ) ^ s * ((s - u)⁻¹))) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsne : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsu : s - u ≠ 0 := by
      refine sub_ne_zero.mpr (fun h => ?_)
      exact notMem_rectSet_of_outside hzre hzim huout (h ▸ rectBoundary_subset_rectSet hzre hzim hs)
    rw [show (1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s) = (x : ℂ) ^ s / (u * (s - u)) by
      field_simp
      ring]
    rw [show (1 / u) * ((x : ℂ) ^ s * (s - u)⁻¹) = (x : ℂ) ^ s / (u * (s - u)) by
      field_simp]
  rw [hcongr, rectInt_eq_zero_of_differentiableOn hd]


/-! ## Finite sums of contour integrals -/

/-- Edge integrability from pointwise continuity on the boundary. -/
lemma intervalIntegrable_of_boundary_continuousAt {z w : ℂ} {f : ℂ → ℂ}
    (hf : ∀ s ∈ rectBoundary z w, ContinuousAt f s) :
    (IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re) ∧
    (IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) volume z.re w.re) ∧
    (IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im) ∧
    (IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) volume z.im w.im) := by
  have h1 : ContinuousOn (fun x : ℝ => f (x + z.im * Complex.I)) (Set.uIcc z.re w.re) :=
    fun x hx => (hf _ (Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩)).comp_continuousWithinAt
      (by fun_prop)
  have h2 : ContinuousOn (fun x : ℝ => f (x + w.im * Complex.I)) (Set.uIcc z.re w.re) :=
    fun x hx => (hf _ (Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩)).comp_continuousWithinAt
      (by fun_prop)
  have h3 : ContinuousOn (fun y : ℝ => f (w.re + y * Complex.I)) (Set.uIcc z.im w.im) :=
    fun y hy => (hf _ (Or.inr ⟨by simpa using hy, Or.inr (by simp)⟩)).comp_continuousWithinAt
      (by fun_prop)
  have h4 : ContinuousOn (fun y : ℝ => f (z.re + y * Complex.I)) (Set.uIcc z.im w.im) :=
    fun y hy => (hf _ (Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩)).comp_continuousWithinAt
      (by fun_prop)
  exact ⟨h1.intervalIntegrable, h2.intervalIntegrable, h3.intervalIntegrable, h4.intervalIntegrable⟩

/-- `rectInt` is additive over finite sums of functions continuous at every boundary point. -/
lemma rectInt_finset_sum_of_boundary {ι : Type*} {z w : ℂ} (S : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ S, ∀ s ∈ rectBoundary z w, ContinuousAt (F i) s) :
    rectInt z w (fun s => ∑ i ∈ S, F i s) = ∑ i ∈ S, rectInt z w (F i) := by
  have hint : ∀ i ∈ S,
      (IntervalIntegrable (fun x : ℝ => F i (x + z.im * Complex.I)) volume z.re w.re) ∧
      (IntervalIntegrable (fun x : ℝ => F i (x + w.im * Complex.I)) volume z.re w.re) ∧
      (IntervalIntegrable (fun y : ℝ => F i (w.re + y * Complex.I)) volume z.im w.im) ∧
      (IntervalIntegrable (fun y : ℝ => F i (z.re + y * Complex.I)) volume z.im w.im) :=
    fun i hi => intervalIntegrable_of_boundary_continuousAt (hF i hi)
  simp only [rectInt_eq_def]
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hint i hi).1),
      intervalIntegral.integral_finsetSum (fun i hi => (hint i hi).2.1),
      intervalIntegral.integral_finsetSum (fun i hi => (hint i hi).2.2.1),
      intervalIntegral.integral_finsetSum (fun i hi => (hint i hi).2.2.2)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma mem_rectSet_of_uIoc_bottom {z w : ℂ} {x : ℝ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hx : x ∈ Set.uIoc z.re w.re) : ((x : ℂ) + z.im * Complex.I) ∈ rectSet z w := by
  refine mem_rectSet ?_ ?_
  · have hx' := hx
    rw [Set.uIoc_of_le (le_of_lt hzre)] at hx'
    rw [Set.uIcc_of_le (le_of_lt hzre)]
    exact ⟨by simpa using hx'.1.le, by simpa using hx'.2⟩
  · rw [Set.uIcc_of_le (le_of_lt hzim)]
    exact ⟨by simpa using (le_rfl : z.im ≤ z.im), by simpa using (le_of_lt hzim : z.im ≤ w.im)⟩

lemma mem_rectSet_of_uIoc_top {z w : ℂ} {x : ℝ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hx : x ∈ Set.uIoc z.re w.re) : ((x : ℂ) + w.im * Complex.I) ∈ rectSet z w := by
  refine mem_rectSet ?_ ?_
  · have hx' := hx
    rw [Set.uIoc_of_le (le_of_lt hzre)] at hx'
    rw [Set.uIcc_of_le (le_of_lt hzre)]
    exact ⟨by simpa using hx'.1.le, by simpa using hx'.2⟩
  · rw [Set.uIcc_of_le (le_of_lt hzim)]
    exact ⟨by simpa using (le_of_lt hzim : z.im ≤ w.im), by simpa using (le_rfl : w.im ≤ w.im)⟩

lemma mem_rectSet_of_uIoc_right {z w : ℂ} {y : ℝ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hy : y ∈ Set.uIoc z.im w.im) : (w.re + (y : ℂ) * Complex.I) ∈ rectSet z w := by
  refine mem_rectSet ?_ ?_
  · rw [Set.uIcc_of_le (le_of_lt hzre)]
    exact ⟨by simpa using (le_of_lt hzre : z.re ≤ w.re), by simpa using (le_rfl : w.re ≤ w.re)⟩
  · have hy' := hy
    rw [Set.uIoc_of_le (le_of_lt hzim)] at hy'
    rw [Set.uIcc_of_le (le_of_lt hzim)]
    exact ⟨by simpa using hy'.1.le, by simpa using hy'.2⟩

lemma mem_rectSet_of_uIoc_left {z w : ℂ} {y : ℝ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hy : y ∈ Set.uIoc z.im w.im) : (z.re + (y : ℂ) * Complex.I) ∈ rectSet z w := by
  refine mem_rectSet ?_ ?_
  · rw [Set.uIcc_of_le (le_of_lt hzre)]
    exact ⟨by simpa using (le_rfl : z.re ≤ z.re), by simpa using (le_of_lt hzre : z.re ≤ w.re)⟩
  · have hy' := hy
    rw [Set.uIoc_of_le (le_of_lt hzim)] at hy'
    rw [Set.uIcc_of_le (le_of_lt hzim)]
    exact ⟨by simpa using hy'.1.le, by simpa using hy'.2⟩

lemma mem_uIcc_of_mem_uIoc {a b x : ℝ} (h : a < b) (hx : x ∈ Set.uIoc a b) :
    x ∈ Set.uIcc a b := by
  rw [Set.uIoc_of_le (le_of_lt h)] at hx
  rw [Set.uIcc_of_le (le_of_lt h)]
  exact ⟨hx.1.le, hx.2⟩

/-- `rectInt` of a function bounded by `M` on the boundary of the rectangle is bounded by `M`
times twice the perimeter. -/
lemma norm_rectInt_le {z w : ℂ} {f : ℂ → ℂ} {M : ℝ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hf : ∀ s ∈ rectBoundary z w, ContinuousAt f s) (hM : ∀ s ∈ rectBoundary z w, ‖f s‖ ≤ M) :
    ‖rectInt z w f‖ ≤ 2 * ((w.re - z.re) + (w.im - z.im)) * M := by
  have hb : ‖(∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I))‖ ≤ M * (w.re - z.re) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z.re) (b := w.re)
      (f := fun x : ℝ => f (x + z.im * Complex.I)) (C := M) (fun x hx =>
        hM _ (Or.inl ⟨by simpa using mem_uIcc_of_mem_uIoc hzre hx, Or.inl (by simp)⟩))
    simpa only [abs_of_pos (sub_pos.mpr hzre), mul_comm (Complex.I) ((z.im : ℂ))] using this
  have ht : ‖(∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I))‖ ≤ M * (w.re - z.re) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z.re) (b := w.re)
      (f := fun x : ℝ => f (x + w.im * Complex.I)) (C := M) (fun x hx =>
        hM _ (Or.inl ⟨by simpa using mem_uIcc_of_mem_uIoc hzre hx, Or.inr (by simp)⟩))
    simpa only [abs_of_pos (sub_pos.mpr hzre), mul_comm (Complex.I) ((w.im : ℂ))] using this
  have hr : ‖(∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I))‖ ≤ M * (w.im - z.im) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z.im) (b := w.im)
      (f := fun y : ℝ => f (w.re + y * Complex.I)) (C := M) (fun y hy =>
        hM _ (Or.inr ⟨by simpa using mem_uIcc_of_mem_uIoc hzim hy, Or.inr (by simp)⟩))
    simpa only [abs_of_pos (sub_pos.mpr hzim), mul_comm (Complex.I) (Complex.I)] using this
  have hl : ‖(∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I))‖ ≤ M * (w.im - z.im) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z.im) (b := w.im)
      (f := fun y : ℝ => f (z.re + y * Complex.I)) (C := M) (fun y hy =>
        hM _ (Or.inr ⟨by simpa using mem_uIcc_of_mem_uIoc hzim hy, Or.inl (by simp)⟩))
    simpa only [abs_of_pos (sub_pos.mpr hzim), mul_comm (Complex.I) (Complex.I)] using this
  have hnormI : ∀ c : ℂ, ‖Complex.I * c‖ = ‖c‖ := by
    intro c; rw [norm_mul, Complex.norm_I, one_mul]
  rw [rectInt_eq_def]
  set A : ℂ := ∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I) with hA
  set B : ℂ := ∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I) with hB
  set C : ℂ := ∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I) with hC
  set D : ℂ := ∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I) with hD
  have hbA : ‖A‖ ≤ M * (w.re - z.re) := by rw [hA]; exact hb
  have htB : ‖B‖ ≤ M * (w.re - z.re) := by rw [hB]; exact ht
  have hrC : ‖C‖ ≤ M * (w.im - z.im) := by rw [hC]; exact hr
  have hlD : ‖D‖ ≤ M * (w.im - z.im) := by rw [hD]; exact hl
  have h1 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
  have h2 : ‖(A - B) + Complex.I * C‖ ≤ ‖A - B‖ + ‖Complex.I * C‖ := norm_add_le _ _
  have h3 : ‖((A - B) + Complex.I * C) - Complex.I * D‖ ≤
      ‖(A - B) + Complex.I * C‖ + ‖Complex.I * D‖ := norm_sub_le _ _
  have eC := hnormI C
  have eD := hnormI D
  change ‖((A - B) + Complex.I * C) - Complex.I * D‖ ≤
    2 * ((w.re - z.re) + (w.im - z.im)) * M
  linarith only [h1, h2, h3, hbA, htB, hrC, hlD, eC, eD, hb, ht, hr, hl]

/-! ## The partial-fraction representation of `Λ'/Λ` with a uniform tail bound -/

/-- The partial-fraction expansion of `logDeriv (completedLFunction χ)` with the uniform tail
bound: for `R ≥ 2` and `‖s‖ ≤ R/4` the finite sum over the divisor in the ball of radius `R`
approximates `logDeriv Λ s - logDeriv Λ 0` up to `O(‖s‖ log(NR)/R)`. -/
lemma partialFraction_limit_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 → ∀ R : ℝ, 2 ≤ R →
      ‖s‖ ≤ R / 4 →
      ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 -
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))‖ ≤
        c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
  rcases Commons.NumberTheory.Linnik.partialFraction_tail χ hχ hχprim with ⟨c, hc⟩
  have key : ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 → ∀ R : ℝ, 2 ≤ R →
      ‖s‖ ≤ R / 4 →
      ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 -
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))‖ ≤
        c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
    intro s hs R hR hsR
    have hconv := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hs
    have hld : logDeriv (DirichletCharacter.completedLFunction χ) s =
        deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s := logDeriv_apply _ _
    have hld0 : logDeriv (DirichletCharacter.completedLFunction χ) 0 =
        deriv (DirichletCharacter.completedLFunction χ) 0 /
          DirichletCharacter.completedLFunction χ 0 := logDeriv_apply _ _
    rw [hld, hld0]
    have hlim2 : Tendsto (fun R' : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R')) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) -
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
        atTop (𝓝 ((deriv (DirichletCharacter.completedLFunction χ) s /
            DirichletCharacter.completedLFunction χ s -
            deriv (DirichletCharacter.completedLFunction χ) 0 /
              DirichletCharacter.completedLFunction χ 0) -
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))) :=
      hconv.sub_const _
    have h2 : (0 : ℝ) ≤ c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R -
        ‖(deriv (DirichletCharacter.completedLFunction χ) s /
            DirichletCharacter.completedLFunction χ s -
            deriv (DirichletCharacter.completedLFunction χ) 0 /
              DirichletCharacter.completedLFunction χ 0) -
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))‖ := by
      have hconst : Tendsto
          (fun _ : ℝ => c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) atTop
          (𝓝 (c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)) := tendsto_const_nhds
      refine ge_of_tendsto (hconst.sub hlim2.norm) ?_
      filter_upwards [eventually_ge_atTop R] with R' hR'
      have hb := hc s R R' hR hR' hsR
      have : ‖(∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R')) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) -
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))‖ ≤
          c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := hb
      linarith [norm_nonneg ((∑ᶠ u : ℂ, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R')) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) -
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))]
    simpa using h2
  refine ⟨max c 0, le_max_right c 0, fun s hs R hR hsR => ?_⟩
  have h1 : (0 : ℝ) ≤ ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
    have h0 : (0 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
      have := Real.log_nonneg (by linarith only [hR] : (1 : ℝ) ≤ R + 2)
      have hN : (0 : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
      linarith only [this, hN]
    have hR0 : 0 < R := by linarith only [hR]
    positivity
  have h2 : c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R ≤
      max c 0 * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
    have hle : c ≤ max c 0 := le_max_left c 0
    calc c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R
        = c * (‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) := by ring
      _ ≤ max c 0 * (‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) :=
          mul_le_mul_of_nonneg_right hle h1
      _ = max c 0 * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by ring
  linarith [key s hs R hR hsR, h2]


/-! ## The contour integral of `Λ'/Λ · x^s/s` -/

lemma cpow_norm_ofReal_mul (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s‖ = x ^ s.re := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.norm_exp]
  have h1 : (Complex.log (x : ℂ) * s).re = Real.log x * s.re := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le,
      Complex.norm_of_nonneg hx.le]
    ring
  rw [h1, Real.rpow_def_of_pos hx]

lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by
      rw [analyticOrderNatAt, ← hn]
      simp
    rw [h2, ← hn]
    simp

lemma eq_zero_of_divisor_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U)
    (h : MeromorphicOn.divisor f U u ≠ 0) : f u = 0 := by
  by_contra h0
  apply h
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu]
  have hord : meromorphicOrderAt f u = 0 := by
    rw [(hf u hu).meromorphicOrderAt_eq, ((hf u hu).analyticOrderAt_eq_zero).mpr h0]
    simp
  simp [hord]

lemma mem_rectBoundary_of_mem_rectSet_of_not_inside {z w u : ℂ} (hzre : z.re < w.re)
    (hzim : z.im < w.im) (hset : u ∈ rectSet z w)
    (hnot : ¬ (z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im)) :
    u ∈ rectBoundary z w := by
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hset
  rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
  rw [Set.uIcc_of_le (le_of_lt hzim)] at him
  unfold rectBoundary
  rw [Set.uIcc_of_le (le_of_lt hzre), Set.uIcc_of_le (le_of_lt hzim)]
  by_cases h1 : u.re = z.re
  · exact Or.inr ⟨him, Or.inl h1⟩
  by_cases h2 : u.re = w.re
  · exact Or.inr ⟨him, Or.inr h2⟩
  by_cases h3 : u.im = z.im
  · exact Or.inl ⟨hre, Or.inl h3⟩
  by_cases h4 : u.im = w.im
  · exact Or.inl ⟨hre, Or.inr h4⟩
  exact absurd ⟨lt_of_le_of_ne hre.1 (Ne.symm h1), lt_of_le_of_ne hre.2 h2,
    lt_of_le_of_ne him.1 (Ne.symm h3), lt_of_le_of_ne him.2 h4⟩ hnot

lemma outside_of_not_inside {z w u : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hnotin : ¬ (z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im))
    (hbound : u ∉ rectBoundary z w) :
    u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hset : u ∈ rectSet z w := mem_rectSet (by
      rw [Set.uIcc_of_le (le_of_lt hzre)]; exact ⟨h1, h2⟩)
    (by rw [Set.uIcc_of_le (le_of_lt hzim)]; exact ⟨h3, h4⟩)
  exact hbound (mem_rectBoundary_of_mem_rectSet_of_not_inside hzre hzim hset hnotin)

/-- The contour integral of a finite combination of kernels `(1/(s-u) + 1/u)`. -/
lemma rectInt_kernel_finset {x : ℝ} (hx : 0 < x) {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (S : Finset ℂ) (hS_ne : ∀ u ∈ S, u ≠ 0) (hS_nb : ∀ u ∈ S, u ∉ rectBoundary z w)
    (d : ℂ → ℂ) :
    rectInt z w (fun s => (∑ u ∈ S, d u * (1 / (s - u) + 1 / u)) * ((x : ℂ) ^ s / s)) =
      ∑ u ∈ S, d u * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
        ((x : ℂ) ^ u / u) * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
  have hcont : ∀ u ∈ S, ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      d u * ((1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s))) s := by
    intro u hu s hs
    have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb u hu (h ▸ hs))
    exact ContinuousAt.mul continuousAt_const
      ((ContinuousAt.add (ContinuousAt.div continuousAt_const
        (continuousAt_id.sub continuousAt_const) hsu) continuousAt_const).mul
      (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt continuousAt_id hs0))
  have hsplit : rectInt z w (fun s => (∑ u ∈ S, d u * (1 / (s - u) + 1 / u)) * ((x : ℂ) ^ s / s)) =
      rectInt z w (fun s => ∑ u ∈ S, d u * ((1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s))) := by
    apply rectInt_congr_boundary'
    intro s hs
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun u hu => by ring)
  rw [hsplit, rectInt_finset_sum_of_boundary S hcont]
  refine Finset.sum_congr rfl ?_
  intro u hu
  have h1 : rectInt z w (fun s : ℂ => d u * ((1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s))) =
      d u * rectInt z w (fun s : ℂ => (1 / (s - u) + 1 / u) * ((x : ℂ) ^ s / s)) :=
    rectInt_const_mul' (d u) _
  rw [h1]
  by_cases huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
  · rw [if_pos huin, rectInt_kernel_cpow_inside hx (hS_ne u hu) hzre hzim h0in huin]
  · rw [if_neg huin, rectInt_kernel_cpow_outside hx (hS_ne u hu) hzre hzim h0in
      (outside_of_not_inside hzre hzim huin (hS_nb u hu)), mul_zero]

/-- The contour integral of `logDeriv Λ · x^s/s` over the rectangle equals `2πi` times the sum
of the residues `x^ρ/ρ` at the zeros of `Λ` inside the rectangle, plus the `s = 0` term. -/
theorem rectInt_logDeriv_completed_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {x : ℝ} (hx : 0 < x)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hins : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      z.re < ρ.re ∧ ρ.re < w.re)
    (hnz : ∀ s ∈ rectBoundary z w, DirichletCharacter.completedLFunction χ s ≠ 0) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
        ((x : ℂ) ^ s / s)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
          ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
              ((x : ℂ) ^ ρ / ρ) else 0)) := by
  obtain ⟨c, hc0, hc⟩ := partialFraction_limit_bound χ hχ hχprim
  -- geometric bounds
  have hzre' : z.re < 0 := h0in.1
  have hwre' : 0 < w.re := h0in.2.1
  have hzim' : z.im < 0 := h0in.2.2.1
  have hwim' : 0 < w.im := h0in.2.2.2
  have hδ0 : 0 < min (min (-z.re) w.re) (min (-z.im) w.im) := by
    refine lt_min (lt_min (by linarith only [h0in]) hwre') (lt_min (by linarith only [h0in]) hwim')
  have hnorm_ge : ∀ s ∈ rectBoundary z w, min (min (-z.re) w.re) (min (-z.im) w.im) ≤ ‖s‖ := by
    intro s hs
    have hzim_le : min (min (-z.re) w.re) (min (-z.im) w.im) ≤ -z.im :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hwim_le : min (min (-z.re) w.re) (min (-z.im) w.im) ≤ w.im :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hzre_le : min (min (-z.re) w.re) (min (-z.im) w.im) ≤ -z.re :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hwre_le : min (min (-z.re) w.re) (min (-z.im) w.im) ≤ w.re :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rcases hs with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
    · have h : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      rw [him, abs_of_neg hzim'] at h
      exact hzim_le.trans h
    · have h : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      rw [him, abs_of_pos hwim'] at h
      exact hwim_le.trans h
    · have h : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      rw [hre, abs_of_neg hzre'] at h
      exact hzre_le.trans h
    · have h : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      rw [hre, abs_of_pos hwre'] at h
      exact hwre_le.trans h
  -- `Mnorm` bounds `‖s‖` on the closed rectangle
  have hnorm_le : ∀ s ∈ rectSet z w,
      ‖s‖ ≤ |z.re| + |w.re| + |z.im| + |w.im| + 1 := by
    intro s hs
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    rw [Set.uIcc_of_le (le_of_lt hzim)] at him
    have h1 : |s.re| ≤ |z.re| + |w.re| := by
      rw [abs_le]
      constructor
      · linarith only [neg_abs_le z.re, hre.1, abs_nonneg w.re, hre]
      · linarith only [le_abs_self w.re, hre.2, abs_nonneg z.re, hre]
    have h2 : |s.im| ≤ |z.im| + |w.im| := by
      rw [abs_le]
      constructor
      · linarith only [neg_abs_le z.im, him.1, abs_nonneg w.im, him]
      · linarith only [le_abs_self w.im, him.2, abs_nonneg z.im, him]
    have h3 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    linarith only [h1, h2, h3]
  -- `xM` bounds `‖x^s‖` on the closed rectangle
  have hnorm_cpow : ∀ s ∈ rectSet z w, ‖(x : ℂ) ^ s‖ ≤ max (x ^ z.re) (x ^ w.re) := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    rw [cpow_norm_ofReal_mul x hx s]
    by_cases h1x : 1 ≤ x
    · exact (Real.rpow_le_rpow_of_exponent_le h1x hre.2).trans (le_max_right _ _)
    · have hb : x ^ s.re ≤ x ^ z.re :=
        Real.rpow_le_rpow_of_exponent_ge hx (le_of_lt (not_le.mp h1x)) hre.1
      exact hb.trans (le_max_left _ _)
  -- bounds on the integrand `x^s/s` on the boundary
  have hnorm_hbound : ∀ s ∈ rectBoundary z w, ‖(x : ℂ) ^ s / s‖ ≤
      max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im) := by
    intro s hs
    have h1 : ‖(x : ℂ) ^ s‖ ≤ max (x ^ z.re) (x ^ w.re) :=
      hnorm_cpow s (rectBoundary_subset_rectSet hzre hzim hs)
    have h2 : min (min (-z.re) w.re) (min (-z.im) w.im) ≤ ‖s‖ := hnorm_ge s hs
    have h3 : 0 < min (min (-z.re) w.re) (min (-z.im) w.im) := hδ0
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le h3 h2)]
    calc ‖(x : ℂ) ^ s‖ ≤ max (x ^ z.re) (x ^ w.re) := h1
      _ = (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)) *
            min (min (-z.re) w.re) (min (-z.im) w.im) := by
          rw [div_mul_cancel₀]; exact ne_of_gt h3
      _ ≤ (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)) * ‖s‖ := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _)) (le_of_lt h3)
  have hMpos : (0 : ℝ) < |z.re| + |w.re| + |z.im| + |w.im| + 1 := by positivity
  have hinside_norm : ∀ ρ : ℂ, z.re < ρ.re → ρ.re < w.re → z.im < ρ.im → ρ.im < w.im →
      ‖ρ‖ ≤ |z.re| + |w.re| + |z.im| + |w.im| := by
    intro ρ h1 h2 h3 h4
    have hre : |ρ.re| ≤ |z.re| + |w.re| := by
      rw [abs_le]
      constructor
      · linarith only [neg_abs_le z.re, h1, abs_nonneg w.re]
      · linarith only [le_abs_self w.re, h2, abs_nonneg z.re]
    have him : |ρ.im| ≤ |z.im| + |w.im| := by
      rw [abs_le]
      constructor
      · linarith only [neg_abs_le z.im, h3, abs_nonneg w.im]
      · linarith only [le_abs_self w.im, h4, abs_nonneg z.im]
    have h5 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    linarith only [hre, him, h5]
  have hkey : ∀ R : ℝ, 2 ≤ R → |z.re| + |w.re| + |z.im| + |w.im| + 1 ≤ R / 4 →
      ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
          ((x : ℂ) ^ s / s)) -
        (2 * (Real.pi : ℂ) * Complex.I) *
          (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
            ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
                ((x : ℂ) ^ ρ / ρ) else 0))‖ ≤
        2 * ((w.re - z.re) + (w.im - z.im)) *
          (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
            (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)) := by
    intro R hR hR4
    let dR : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) u
    have hdRfin : dR.support.Finite := by
      simpa only [dR] using
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R)
    let S : Finset ℂ := hdRfin.toFinset
    have hS_mem : ∀ u : ℂ, u ∈ S ↔ dR u ≠ 0 := fun u => hdRfin.mem_toFinset
    have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
      (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    have hS_zero : ∀ u ∈ S, DirichletCharacter.completedLFunction χ u = 0 := by
      intro u hu
      have hnorm : ‖u‖ ≤ R := by
        by_contra hcon
        refine (hS_mem u).mp hu ?_
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem))
      refine eq_zero_of_divisor_ne_zero
        (U := Metric.closedBall 0 R)
        (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
        (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hnorm)) ?_
      simpa only [dR] using (hS_mem u).mp hu
    have hS_ne : ∀ u ∈ S, u ≠ 0 := by
      intro u hu h0
      exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
        (h0 ▸ hS_zero u hu)
    have hS_nb : ∀ u ∈ S, u ∉ rectBoundary z w := by
      intro u hu hb
      exact hnz u hb (hS_zero u hu)
    have hS_norm : ∀ u ∈ S, ‖u‖ ≤ R := by
      intro u hu
      by_contra hcon
      have h0 : dR u = 0 := by
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem))
      exact (hS_mem u).mp hu h0
    let FR : ℂ → ℂ := fun s => ∑ u ∈ S, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)
    let TR : ℂ → ℂ := fun s => logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.completedLFunction χ) 0 - FR s
    have hFR_eq : ∀ s : ℂ, FR s =
        ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) := by
      intro s
      dsimp only [FR]
      refine (finsum_eq_sum_of_support_subset _ ?_).symm
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS_mem u).mpr (fun hz => hu (by simp [hz]))
    -- the kernel integral of `FR · h`
    have hFRint : rectInt z w (fun s => FR s * ((x : ℂ) ^ s / s)) =
        ∑ u ∈ S, ((dR u : ℤ) : ℂ) * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
          ((x : ℂ) ^ u / u) * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
      have h := rectInt_kernel_finset (x := x) hx hzre hzim h0in S hS_ne hS_nb
        (fun u => ((dR u : ℤ) : ℂ))
      simpa only [FR] using h
    have hFRfin : (∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then (x : ℂ) ^ u / u else 0)) =
        ∑ u ∈ S, ((dR u : ℤ) : ℂ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then (x : ℂ) ^ u / u else 0) := by
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS_mem u).mpr (fun hz => hu (by simp [hz]))
    have hFRint' : rectInt z w (fun s => FR s * ((x : ℂ) ^ s / s)) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
            (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then (x : ℂ) ^ u / u else 0) := by
      rw [hFRint, hFRfin, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro u hu
      by_cases huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
      · rw [if_pos huin, if_pos huin]; ring
      · rw [if_neg huin, if_neg huin]; ring
    -- the divisor of the completed L-function equals the vanishing order on the rectangle
    have hdiv_eq : ∀ ρ : ℂ, (z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im) →
        ((dR ρ : ℤ) : ℂ) =
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) := by
      intro ρ hρ
      have hρR : ‖ρ‖ ≤ R := le_trans (hinside_norm ρ hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2) (by linarith only [hMpos, hR4])
      have h1 : dR ρ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℤ) := by
        dsimp only [dR]
        exact divisor_eq_analyticOrderNatAt (U := Metric.closedBall 0 R)
          (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
          (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hρR))
      rw [h1]; norm_num
    have hsum_eq : (∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then (x : ℂ) ^ u / u else 0)) =
        ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
            ((x : ℂ) ^ ρ / ρ) else 0) := by
      refine finsum_congr ?_
      intro ρ
      by_cases hρ : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
      · rw [if_pos hρ, if_pos hρ, hdiv_eq ρ hρ]
      · rw [if_neg hρ, if_neg hρ, mul_zero]
    -- pointwise decomposition of the integrand
    have hpoint : ∀ s ∈ rectBoundary z w,
        logDeriv (DirichletCharacter.completedLFunction χ) s * ((x : ℂ) ^ s / s) =
          (logDeriv (DirichletCharacter.completedLFunction χ) 0 * ((x : ℂ) ^ s / s) +
            FR s * ((x : ℂ) ^ s / s)) + TR s * ((x : ℂ) ^ s / s) := by
      intro s hs; simp only [TR]; ring
    have hcontA1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
        logDeriv (DirichletCharacter.completedLFunction χ) 0 * ((x : ℂ) ^ s / s)) s := by
      intro s hs
      have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
      exact continuousAt_const.mul (ContinuousAt.div
        ((cpow_differentiable_of_pos hx) s).continuousAt continuousAt_id hs0)
    have hcontA2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
        FR s * ((x : ℂ) ^ s / s)) s := by
      intro s hs
      have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
      have hFR : ContinuousAt FR s := by
        dsimp only [FR]
        refine tendsto_finsetSum _ ?_
        intro u hu
        have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb u hu (h ▸ hs))
        exact ContinuousAt.mul continuousAt_const
          (ContinuousAt.add (ContinuousAt.div continuousAt_const
            (continuousAt_id.sub continuousAt_const) hsu) continuousAt_const)
      exact hFR.mul (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt
        continuousAt_id hs0)
    have hcontB : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
        TR s * ((x : ℂ) ^ s / s)) s := by
      intro s hs
      have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
      have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := hnz s hs
      have han : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) s :=
        (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s
      have hlog : ContinuousAt (fun s : ℂ =>
          logDeriv (DirichletCharacter.completedLFunction χ) s) s := by
        rw [show (fun s : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) s) =
            fun s => deriv (DirichletCharacter.completedLFunction χ) s /
              DirichletCharacter.completedLFunction χ s from
          funext (fun s => logDeriv_apply _ _)]
        exact (han.deriv.continuousAt).div han.continuousAt hΛs
      have hFR : ContinuousAt FR s := by
        dsimp only [FR]
        refine tendsto_finsetSum _ ?_
        intro u hu
        have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb u hu (h ▸ hs))
        exact ContinuousAt.mul continuousAt_const
          (ContinuousAt.add (ContinuousAt.div continuousAt_const
            (continuousAt_id.sub continuousAt_const) hsu) continuousAt_const)
      exact ((hlog.sub continuousAt_const).sub hFR).mul
        (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt continuousAt_id hs0)
    obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hcontA1
    obtain ⟨a1', a2', a3', a4'⟩ := intervalIntegrable_of_boundary_continuousAt hcontA2
    obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hcontB
    have htail_bound : ‖rectInt z w (fun s => TR s * ((x : ℂ) ^ s / s))‖ ≤
        2 * ((w.re - z.re) + (w.im - z.im)) *
            (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)) := by
      rw [show 2 * ((w.re - z.re) + (w.im - z.im)) *
            (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)) =
          2 * ((w.re - z.re) + (w.im - z.im)) *
            ((c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
            (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im))) by ring]
      refine norm_rectInt_le (M := (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
        (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
        (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)))
        hzre hzim hcontB ?_
      intro s hs
      have hnorm_s : ‖s‖ ≤ |z.re| + |w.re| + |z.im| + |w.im| + 1 :=
        hnorm_le s (rectBoundary_subset_rectSet hzre hzim hs)
      have htail_le := hc s (hnz s hs) R hR (by linarith only [hnorm_s, hR4])
      have hlog0 : (0 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
        have h3 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)]
      have hnorm_h := hnorm_hbound s hs
      rw [norm_mul]
      have htr : TR s = logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0 -
          ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) := by
        simp only [TR]
        rw [hFR_eq s]
      have e1 : ‖TR s‖ ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
          (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
        rw [htr]
        calc ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
              logDeriv (DirichletCharacter.completedLFunction χ) 0 -
              ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)‖
              ≤ c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := htail_le
          _ ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
                have hmul : c * ‖s‖ ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) :=
                  mul_le_mul_of_nonneg_left hnorm_s hc0
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hmul hlog0) (by linarith only [hMpos, hR4])
      have h2 : (0 : ℝ) ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
          (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by positivity
      have h3' : (0 : ℝ) ≤ max (x ^ z.re) (x ^ w.re) /
          min (min (-z.re) w.re) (min (-z.im) w.im) := by
        apply div_nonneg
        · exact le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _)
        · exact le_of_lt hδ0
      exact mul_le_mul e1 hnorm_h (norm_nonneg _) h2
    have hcongr : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
        ((x : ℂ) ^ s / s)) =
        rectInt z w (fun s => (logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          ((x : ℂ) ^ s / s) + FR s * ((x : ℂ) ^ s / s)) + TR s * ((x : ℂ) ^ s / s)) := by
      apply rectInt_congr_boundary'
      intro s hs
      simp only [TR]
      ring
    have h1 : rectInt z w (fun s => (logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          ((x : ℂ) ^ s / s) + FR s * ((x : ℂ) ^ s / s)) + TR s * ((x : ℂ) ^ s / s)) =
        rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          ((x : ℂ) ^ s / s) + FR s * ((x : ℂ) ^ s / s)) +
        rectInt z w (fun s => TR s * ((x : ℂ) ^ s / s)) :=
      rectInt_add'' (a1.add a1') b1 (a2.add a2') b2 (a3.add a3') b3 (a4.add a4') b4
    have h2 : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          ((x : ℂ) ^ s / s) + FR s * ((x : ℂ) ^ s / s)) =
        rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          ((x : ℂ) ^ s / s)) +
        rectInt z w (fun s => FR s * ((x : ℂ) ^ s / s)) :=
      rectInt_add'' a1 a1' a2 a2' a3 a3' a4 a4'
    have htotal : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
        ((x : ℂ) ^ s / s)) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
            ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
              (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
                (x : ℂ) ^ u / u else 0)) +
        rectInt z w (fun s => TR s * ((x : ℂ) ^ s / s)) := by
      rw [hcongr, h1, h2,
        rectInt_const_mul' (logDeriv (DirichletCharacter.completedLFunction χ) 0)
          (fun s : ℂ => (x : ℂ) ^ s / s),
        rectInt_cpow_div_self hx hzre hzim h0in, hFRint']
      ring
    calc ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
          ((x : ℂ) ^ s / s)) -
        (2 * (Real.pi : ℂ) * Complex.I) *
          (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
            ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
                ((x : ℂ) ^ ρ / ρ) else 0))‖
        = ‖rectInt z w (fun s => TR s * ((x : ℂ) ^ s / s))‖ := by
          rw [htotal, hsum_eq]
          simp only [add_sub_cancel_left]
      _ ≤ 2 * ((w.re - z.re) + (w.im - z.im)) *
          (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
            (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)) := by
        exact htail_bound
  -- pass to the limit
  have hlim : Tendsto (fun R : ℝ => 2 * ((w.re - z.re) + (w.im - z.im)) *
      (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
        (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
      (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) atTop (𝓝 0) := by
      have hlog := Commons.NumberTheory.Linnik.log_add_two_div_self_tendsto_zero
      have hc2 : Tendsto (fun R : ℝ => (Real.log (N : ℝ) + 2) / R) atTop (𝓝 0) := by
        have hnum : Tendsto (fun _ : ℝ => Real.log (N : ℝ) + 2) atTop (𝓝 (Real.log (N : ℝ) + 2)) :=
          tendsto_const_nhds
        have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have := hnum.mul hinv
        simpa [div_eq_mul_inv] using this
      have := hlog.add hc2
      simpa [add_div, add_assoc] using this
    have h2 : Tendsto (fun R : ℝ => c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
        ((Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := c * (|z.re| + |w.re| + |z.im| + |w.im| + 1))).mul h1
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have h3 : Tendsto (fun R : ℝ => (2 * ((w.re - z.re) + (w.im - z.im)) *
        (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im))) *
        (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
          ((Real.log (R + 2) + Real.log (N : ℝ) + 2) / R))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := 2 * ((w.re - z.re) + (w.im - z.im)) *
        (max (x ^ z.re) (x ^ w.re) / min (min (-z.re) w.re) (min (-z.im) w.im)))).mul h2
      simpa using this
    simpa [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using h3
  have hzero : ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
      ((x : ℂ) ^ s / s)) -
      (2 * (Real.pi : ℂ) * Complex.I) *
        (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
          ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
              ((x : ℂ) ^ ρ / ρ) else 0))‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max 2 (4 * (|z.re| + |w.re| + |z.im| + |w.im| + 1)))]
      with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR4 : |z.re| + |w.re| + |z.im| + |w.im| + 1 ≤ R / 4 := by
      have := le_trans (le_max_right 2 (4 * (|z.re| + |w.re| + |z.im| + |w.im| + 1))) hR
      linarith only [this]
    exact hkey R hR2 hR4
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))


/-- Shifted form of the formula for the logarithmic derivative of `Gammaℝ`, valid down to
`Re s > -1`: the pole at `s = 0` is made explicit. -/
lemma logDeriv_Gammaℝ_add_inv {s : ℂ} (hs0 : s ≠ 0) (hsre : -(1 : ℝ) < s.re) :
    logDeriv Complex.Gammaℝ s + 1 / s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2 + 1) / 2 := by
  have hc : (Real.pi : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; exact Real.pi_pos
  have hne : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    have h2 : (s / 2 + 1).re = s.re / 2 + 1 := by simp
    have h3 : ((-(m : ℂ)) : ℂ).re = -(m : ℝ) := by simp
    rw [h2, h3] at h'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hsre, h']
  have hΓd : DifferentiableAt ℂ Complex.Gamma (s / 2 + 1) := Complex.differentiableAt_Gamma _ hne
  have hΓnz : Complex.Gamma (s / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    have h2 : (s / 2 + 1).re = s.re / 2 + 1 := by simp
    rw [h2]; linarith only [hsre])
  have h1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -(Complex.log (Real.pi : ℂ)) / 2 := by
    have hinner : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
    have hld := logDeriv_comp (f := fun w : ℂ => (Real.pi : ℂ) ^ w)
      (g := fun z : ℂ => -z / 2) (x := s)
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ w) (-s / 2)) hinner
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_const_cpow hc] at hld
    have hder : deriv (fun z : ℂ => -z / 2) s = -((2 : ℂ)⁻¹) := by
      simp; norm_num
    rw [hder, Function.comp_def] at hld
    calc logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
        = Complex.log (Real.pi : ℂ) * (-((2 : ℂ)⁻¹)) := by simpa using hld
      _ = -(Complex.log (Real.pi : ℂ)) / 2 := by rw [div_eq_mul_inv]; ring
  have h2 : logDeriv (fun z : ℂ => (2 : ℂ) / z) s = -1 / s := by
    have hfun : (fun z : ℂ => (2 : ℂ) / z) = fun z : ℂ => (2 : ℂ) * z⁻¹ := by
      funext z; rw [div_eq_mul_inv]
    rw [hfun, logDeriv_const_mul s 2 (by norm_num), logDeriv_inv]
  have h3 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2 + 1)) s =
      Complex.digamma (s / 2 + 1) / 2 := by
    have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2 + 1) s := by fun_prop
    have hld := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2 + 1) (x := s)
      hΓd hdiv
    have hder : deriv (fun z : ℂ => z / 2 + 1) s = (2 : ℂ)⁻¹ := by
      simp
    rw [hder, Function.comp_def] at hld
    rw [← Complex.digamma_def] at hld
    calc logDeriv (fun z : ℂ => Complex.Gamma (z / 2 + 1)) s =
          Complex.digamma (s / 2 + 1) * ((2 : ℂ)⁻¹) := by simpa using hld
      _ = Complex.digamma (s / 2 + 1) / 2 := by simp [div_eq_mul_inv]
  have hprod1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * ((2 : ℂ) / z)) s := by
    apply DifferentiableAt.mul
    · have hinner : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
      exact hinner.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    · exact (differentiableAt_const (c := (2 : ℂ))).div differentiableAt_id hs0
  have hpt : Complex.Gammaℝ =ᶠ[𝓝 s]
      fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * ((2 : ℂ) / z) * Complex.Gamma (z / 2 + 1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs0] with z hz
    rw [Complex.Gammaℝ_def]
    have h1z : Complex.Gamma (z / 2) = ((2 : ℂ) / z) * Complex.Gamma (z / 2 + 1) := by
      have hz0 : z ≠ 0 := by simpa using hz
      have h2z : (z / 2) * Complex.Gamma (z / 2) = Complex.Gamma (z / 2 + 1) :=
        (Complex.Gamma_add_one (z / 2) (by simpa using hz)).symm
      rw [← h2z]
      field_simp
    rw [h1z]; ring
  rw [(logDeriv_congr_nhds hpt).eq_of_nhds]
  have hmul1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * ((2 : ℂ) / z) *
      Complex.Gamma (z / 2 + 1)) s =
      logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * ((2 : ℂ) / z)) s +
        logDeriv (fun z : ℂ => Complex.Gamma (z / 2 + 1)) s :=
    logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * ((2 : ℂ) / z))
      (g := fun z : ℂ => Complex.Gamma (z / 2 + 1)) (x := s)
      (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
        (div_ne_zero (by norm_num) hs0)) hΓnz hprod1 (hΓd.comp s (by fun_prop))
  have hmul2 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * ((2 : ℂ) / z)) s =
      logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s +
        logDeriv (fun z : ℂ => (2 : ℂ) / z) s :=
    logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) (g := fun z : ℂ => (2 : ℂ) / z)
      (x := s) (Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (div_ne_zero (by norm_num) hs0)
      (by
        have hinner : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
        exact hinner.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
      ((differentiableAt_const (c := (2 : ℂ))).div differentiableAt_id hs0)
  rw [hmul1, hmul2, h1, h2, h3]
  ring

/-- The digamma function is differentiable at every point of the half-plane `Re w > 0`. -/
lemma differentiableAt_digamma_of_pos {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.digamma w := by
  have hδ : 0 < min 1 (w.re / 2) := lt_min one_pos (by linarith only [hw])
  have hne_w : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hnot : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at h'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hw, h']
  have hball : DifferentiableOn ℂ Complex.Gamma (Metric.ball w (min 1 (w.re / 2))) := by
    intro z hz
    have hzre : 0 < z.re := by
      have h1 : dist z w < min 1 (w.re / 2) := Metric.mem_ball.mp hz
      have h2 : w.re - z.re ≤ ‖w - z‖ :=
        (le_abs_self (w.re - z.re)).trans (Complex.abs_re_le_norm (w - z))
      rw [dist_eq_norm, norm_sub_rev] at h1
      linarith only [h1, h2, min_le_right (1:ℝ) (w.re / 2), hw]
    exact (Complex.differentiableAt_Gamma z (fun m h => by
      have h' := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at h'
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith only [hzre, h'])).differentiableWithinAt
  have han : AnalyticAt ℂ Complex.Gamma w := hball.analyticAt (Metric.ball_mem_nhds w hδ)
  rw [Complex.digamma_def]
  exact DifferentiableAt.div (han.deriv.differentiableAt)
    (Complex.differentiableAt_Gamma w hnot) hne_w

/-- Differentiability of a shifted digamma on the rectangle. -/
lemma differentiableOn_digamma_shift {z w : ℂ} {c : ℂ}
    (hc : ∀ s ∈ rectSet z w, 0 < ((s + c) / 2).re) :
    DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + c) / 2)) (rectSet z w) := by
  intro s hs
  exact ((differentiableAt_digamma_of_pos (hc s hs)).comp s (by fun_prop)).differentiableWithinAt

/-- Differentiability of a shifted digamma at a single point. -/
lemma differentiableAt_digamma_shift {s c : ℂ} (h : 0 < ((s + c) / 2).re) :
    DifferentiableAt ℂ (fun t : ℂ => Complex.digamma ((t + c) / 2)) s :=
  (differentiableAt_digamma_of_pos h).comp s (by fun_prop)

lemma digamma_re_shift_two {s : ℂ} (hs : -(1 : ℝ) < s.re) : 0 < ((s + 2) / 2).re := by
  have h1 : ((s + 2) / 2).re = s.re / 2 + 1 := by
    rw [show (s + 2) / 2 = s / 2 + 1 by ring]
    simp
  rw [h1]; linarith only [hs]

lemma digamma_re_shift_one {s : ℂ} (hs : -(1 : ℝ) < s.re) : 0 < ((s + 1) / 2).re := by
  have h1 : ((s + 1) / 2).re = s.re / 2 + 1 / 2 := by
    rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]
    simp
  rw [h1]; linarith only [hs]

/-- The contour integral of `γ'/γ · x^s/s` over the rectangle: only the residue at `s = 0`
contributes. -/
lemma rectInt_logDeriv_gammaFactor_eq_even {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hE : χ.Even) {x : ℝ}
    (hx : 0 < x) {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * ((x : ℂ) ^ s / s)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2) - (Real.log x : ℂ)) := by
  have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    linarith only [hre.1, hz1, hre]
  have hgf : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
    funext s; exact hE.gammaFactor_def s
  rw [hgf]
  have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 2) / 2)) (rectSet z w) :=
    differentiableOn_digamma_shift (c := 2) (fun s hs => digamma_re_shift_two (hre_ge s hs))
  have hg : DifferentiableOn ℂ (fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) * (x : ℂ) ^ s)
      (rectSet z w) := by
    apply DifferentiableOn.mul
    · exact DifferentiableOn.add (differentiableOn_const (-(Complex.log (Real.pi : ℂ)) / 2))
        (hdig.div_const 2)
    · exact fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
  have hpoint : ∀ s ∈ rectBoundary z w,
      logDeriv Complex.Gammaℝ s * ((x : ℂ) ^ s / s) =
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) *
            ((x : ℂ) ^ s / s) + (-1) * ((x : ℂ) ^ s / s ^ 2) := by
    intro s hs
    have hsne : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
    have h := logDeriv_Gammaℝ_add_inv hsne hsre
    rw [show s / 2 + 1 = (s + 2) / 2 by ring] at h
    have h' : logDeriv Complex.Gammaℝ s =
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) - 1 / s :=
      eq_sub_iff_add_eq.mpr h
    rw [h']
    field_simp
    ring
  have hcont1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) *
        ((x : ℂ) ^ s / s)) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
    have hc1 : ContinuousAt (fun t : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma ((t + 2) / 2) / 2) s := by
      have hd' : ContinuousAt (fun t : ℂ => Complex.digamma ((t + 2) / 2) / 2) s :=
        (differentiableAt_digamma_shift (s := s) (c := 2) (digamma_re_shift_two hsre)).continuousAt.div_const 2
      exact ContinuousAt.const_add hd' (-(Complex.log (Real.pi : ℂ)) / 2)
    exact hc1.mul (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt
      continuousAt_id hs0)
  have hcont2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => (x : ℂ) ^ s / s ^ 2) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    exact ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt
      (continuousAt_id.pow 2) (pow_ne_zero 2 hs0)
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hcont1
  obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hcont2
  have hcongr : rectInt z w (fun s => logDeriv Complex.Gammaℝ s * ((x : ℂ) ^ s / s)) =
      rectInt z w (fun s => (-(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma ((s + 2) / 2) / 2) * ((x : ℂ) ^ s / s) +
          (-1) * ((x : ℂ) ^ s / s ^ 2)) := by
    apply rectInt_congr_boundary'
    intro s hs
    exact hpoint s hs
  have hAn : rectInt z w (fun s => (-(Complex.log (Real.pi : ℂ)) / 2 +
      Complex.digamma ((s + 2) / 2) / 2) * ((x : ℂ) ^ s / s)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2) := by
    have h := rectInt_analytic_div_self (f := fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) * (x : ℂ) ^ s)
      hzre hzim h0in hg
    have heq : (fun s : ℂ => (-(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma ((s + 2) / 2) / 2) * (x : ℂ) ^ s / s) = (fun s : ℂ =>
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) *
          ((x : ℂ) ^ s / s)) := by
      funext s; rw [mul_div_assoc]
    rw [heq] at h
    rw [h]
    simp only [Complex.cpow_zero, mul_one]
    rw [mul_comm]
    norm_num
  have hSq : rectInt z w (fun s => (-1) * ((x : ℂ) ^ s / s ^ 2)) =
      (-1) * ((Real.log x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [rectInt_const_mul' (-1) (fun s : ℂ => (x : ℂ) ^ s / s ^ 2),
      rectInt_cpow_div_self_sq hx hzre hzim h0in]
  rw [hcongr, rectInt_add'' a1 (b1.const_mul (-1)) a2 (b2.const_mul (-1)) a3 (b3.const_mul (-1))
    a4 (b4.const_mul (-1)), hAn, hSq]
  ring

lemma rectInt_logDeriv_gammaFactor_eq_odd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hO : χ.Odd) {x : ℝ}
    (hx : 0 < x) {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * ((x : ℂ) ^ s / s)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (1 / 2 : ℂ) / 2) := by
  have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    linarith only [hre.1, hz1, hre]
  have hgf : DirichletCharacter.gammaFactor χ = fun s => Complex.Gammaℝ (s + 1) := by
    funext s; exact hO.gammaFactor_def s
  rw [hgf]
  have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 1) / 2)) (rectSet z w) :=
    differentiableOn_digamma_shift (c := 1) (fun s hs => digamma_re_shift_one (hre_ge s hs))
  have hg : DifferentiableOn ℂ (fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) * (x : ℂ) ^ s)
      (rectSet z w) := by
    apply DifferentiableOn.mul
    · exact DifferentiableOn.add (differentiableOn_const (-(Complex.log (Real.pi : ℂ)) / 2))
        (hdig.div_const 2)
    · exact fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
  have hpoint : ∀ s ∈ rectBoundary z w,
      logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s * ((x : ℂ) ^ s / s) =
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) *
          ((x : ℂ) ^ s / s) := by
    intro s hs
    have hsre : 0 < (s + 1).re := by
      have h1 : (s + 1).re = s.re + 1 := by simp
      rw [h1]
      linarith only [hre_ge s (rectBoundary_subset_rectSet hzre hzim hs), hre_ge, hzre, hzim, hs]
    have hcomp : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 1) (x := s)
        (differentiableAt_Gammaℝ (s + 1) hsre) (by fun_prop)
      simpa [Function.comp_def] using h
    rw [hcomp, logDeriv_Gammaℝ_formula (s + 1) hsre]
  have hcont1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) *
        ((x : ℂ) ^ s / s)) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
    have hc1 : ContinuousAt (fun t : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma ((t + 1) / 2) / 2) s := by
      have hd' : ContinuousAt (fun t : ℂ => Complex.digamma ((t + 1) / 2) / 2) s :=
        (differentiableAt_digamma_shift (s := s) (c := 1) (digamma_re_shift_one hsre)).continuousAt.div_const 2
      exact ContinuousAt.const_add hd' (-(Complex.log (Real.pi : ℂ)) / 2)
    exact hc1.mul (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt
      continuousAt_id hs0)
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hcont1
  have hcongr : rectInt z w (fun s => logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s *
      ((x : ℂ) ^ s / s)) =
      rectInt z w (fun s => (-(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma ((s + 1) / 2) / 2) * ((x : ℂ) ^ s / s)) := by
    apply rectInt_congr_boundary'
    intro s hs
    exact hpoint s hs
  have hAn : rectInt z w (fun s => (-(Complex.log (Real.pi : ℂ)) / 2 +
      Complex.digamma ((s + 1) / 2) / 2) * ((x : ℂ) ^ s / s)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (1 / 2 : ℂ) / 2) := by
    have h := rectInt_analytic_div_self (f := fun s : ℂ =>
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) * (x : ℂ) ^ s)
      hzre hzim h0in hg
    have heq : (fun s : ℂ => (-(Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma ((s + 1) / 2) / 2) * (x : ℂ) ^ s / s) = (fun s : ℂ =>
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) *
          ((x : ℂ) ^ s / s)) := by
      funext s; rw [mul_div_assoc]
    rw [heq] at h
    rw [h]
    simp only [Complex.cpow_zero, mul_one]
    rw [mul_comm]
    norm_num
  rw [hcongr, hAn]

/-! ## Decomposition of the logarithmic derivative of the completed `L`-function -/

lemma half_ne_neg_nat {s : ℂ} (hsre : -(1 : ℝ) < s.re) (hs0 : s ≠ 0) :
    ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, neg_zero] at h
    exact hs0 (by rw [show s = 2 * (s / 2) by ring, h, mul_zero])
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hre : (s / 2).re = s.re / 2 := by simp
    have h' := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re, hre] at h'
    linarith only [hsre, hm1, h']

lemma half_add_one_ne_neg_nat {s : ℂ} (hsre : -(1 : ℝ) < s.re) :
    ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ) := by
  intro m h
  have hre : ((s + 1) / 2).re = s.re / 2 + 1 / 2 := by
    rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]; simp
  have h' := congrArg Complex.re h
  rw [Complex.neg_re, Complex.natCast_re, hre] at h'
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith only [hsre, h']

lemma cpow_pi_ne_zero (w : ℂ) : (Real.pi : ℂ) ^ w ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

/-- The gamma factor does not vanish for `Re s > -1`, `s ≠ 0`. -/
lemma gammaFactor_ne_zero_of_re_gt_neg_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hsre : -(1 : ℝ) < s.re) (hs0 : s ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def, Complex.Gammaℝ_def]
    exact mul_ne_zero (cpow_pi_ne_zero _) (Complex.Gamma_ne_zero (half_ne_neg_nat hsre hs0))
  · rw [hO.gammaFactor_def, Complex.Gammaℝ_def]
    exact mul_ne_zero (cpow_pi_ne_zero _) (Complex.Gamma_ne_zero (half_add_one_ne_neg_nat hsre))

/-- Differentiability of `Gammaℝ` away from the poles of `Gamma (·/2)`. -/
lemma differentiableAt_Gammaℝ_of_shift {t : ℂ} (h : ∀ m : ℕ, t / 2 ≠ -(m : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ t := by
  have hfun : Complex.Gammaℝ = (fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) := by
    funext z; rw [Complex.Gammaℝ_def]
  rw [hfun]
  refine DifferentiableAt.mul ?_ ?_
  · exact ((cpow_differentiable_of_pos Real.pi_pos) (-t / 2)).comp t (by fun_prop)
  · exact (Complex.differentiableAt_Gamma (t / 2) h).comp t (by fun_prop)

/-- Differentiability of the gamma factor for `Re s > -1`. -/
lemma differentiableAt_gammaFactor_of_re_gt_neg_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hsre : -(1 : ℝ) < s.re) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact hE.gammaFactor_def z
    rw [hfun]
    exact differentiableAt_Gammaℝ_of_shift (half_ne_neg_nat hsre hs0)
  · have hfun : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
      funext z; exact hO.gammaFactor_def z
    rw [hfun]
    exact (differentiableAt_Gammaℝ_of_shift (half_add_one_ne_neg_nat hsre)).comp
      (f := fun z : ℂ => z + 1) s (by fun_prop)

/-- The completed `L`-function is the product of the gamma factor and the `L`-function. -/
lemma completedL_eq_gammaFactor_mul_L {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ≠ 0) (hsre : -(1 : ℝ) < s.re) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.gammaFactor χ s * DirichletCharacter.LFunction χ s := by
  have h1 : DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s :=
    DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs)
  have h2 : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_re_gt_neg_one χ hsre hs
  rw [h1, mul_div_cancel₀ _ h2]

/-- `logDeriv` of the completed `L`-function splits as the sum of the logarithmic derivatives
of the gamma factor and of the `L`-function. -/
lemma logDeriv_completedL_eq_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ≠ 0) (hsre : -(1 : ℝ) < s.re)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.gammaFactor χ) s +
        logDeriv (DirichletCharacter.LFunction χ) s := by
  have hγ : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_re_gt_neg_one χ hsre hs
  have hdγ : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s :=
    differentiableAt_gammaFactor_of_re_gt_neg_one χ hsre hs
  have hdL : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ) s
  have hmul : logDeriv (fun t : ℂ => DirichletCharacter.gammaFactor χ t *
      DirichletCharacter.LFunction χ t) s =
      logDeriv (DirichletCharacter.gammaFactor χ) s +
        logDeriv (DirichletCharacter.LFunction χ) s :=
    logDeriv_mul s hγ hL hdγ hdL
  have hprod : (fun t : ℂ => DirichletCharacter.gammaFactor χ t *
      DirichletCharacter.LFunction χ t) =ᶠ[𝓝 s] DirichletCharacter.completedLFunction χ := by
    filter_upwards [isOpen_ne.mem_nhds hs,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsre] with t ht htre
    exact (completedL_eq_gammaFactor_mul_L χ ht htre).symm
  have hcongr : logDeriv (fun t : ℂ => DirichletCharacter.gammaFactor χ t *
      DirichletCharacter.LFunction χ t) s =
      logDeriv (DirichletCharacter.completedLFunction χ) s :=
    (logDeriv_congr_nhds hprod).eq_of_nhds
  rw [← hcongr]
  exact hmul

/-- Pointwise bound for the logarithmic derivative of the gamma factor on the left edge. -/
lemma norm_logDeriv_gammaFactor_leftEdge {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (t : ℝ) :
    ‖logDeriv (DirichletCharacter.gammaFactor χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 + 2 := by
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hre_s : s.re = -1 / 2 := by rw [hs_def]; simp
  have him_s : s.im = t := by rw [hs_def]; simp
  have hsre : -(1 : ℝ) < s.re := by rw [hre_s]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have h0 : s.re = 0 := by rw [h]; simp
    rw [hre_s] at h0
    norm_num at h0
  have hnorm : (1 : ℝ) ≤ 2 * ‖s‖ := by
    have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    rw [hre_s] at h1
    norm_num at h1
    linarith only [h1]
  have hlog2 : Real.log (2 + |t / 2|) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log (by positivity)
    have h : |t / 2| ≤ |t| := by
      rw [abs_div]
      exact div_le_self (abs_nonneg t) (by norm_num)
    linarith only [h]
  have hlogpi : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ ≤ Real.log Real.pi / 2 := by
    have hlogpi' : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (le_of_lt Real.pi_pos)]
    rw [hlogpi', norm_div, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three]))]
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact hE.gammaFactor_def z
    rw [hfun]
    have hkey := logDeriv_Gammaℝ_add_inv (s := s) hs0 hsre
    have hval : logDeriv Complex.Gammaℝ s =
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2 + 1) / 2) - 1 / s :=
      eq_sub_iff_add_eq.mpr hkey
    rw [hval]
    have hre1 : (1 : ℝ) / 4 ≤ (s / 2 + 1).re := by
      have h : (s / 2 + 1).re = s.re / 2 + 1 := by
        rw [show s / 2 + 1 = (s + 2) / 2 by ring]; simp <;> ring
      rw [h, hre_s]; norm_num
    have hre2 : (s / 2 + 1).re ≤ 8 := by
      have h : (s / 2 + 1).re = s.re / 2 + 1 := by
        rw [show s / 2 + 1 = (s + 2) / 2 by ring]; simp <;> ring
      rw [h, hre_s]; norm_num
    have him1 : (s / 2 + 1).im = t / 2 := by
      have h : (s / 2 + 1).im = s.im / 2 := by
        rw [show s / 2 + 1 = (s + 2) / 2 by ring]; simp <;> ring
      rw [h, him_s]
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      ((s / 2 + 1).re) ((s / 2 + 1).im) hre1 hre2
    have hdg' : ‖Complex.digamma (s / 2 + 1)‖ ≤ Real.log (2 + |t|) + 8 := by
      have hcongr : ((s / 2 + 1).re : ℂ) + ((s / 2 + 1).im : ℂ) * Complex.I = s / 2 + 1 :=
        Complex.re_add_im _
      rw [← hcongr]
      refine hdg.trans ?_
      rw [him1]
      linarith only [hlog2]
    have hinv : ‖(1 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div, norm_one, div_le_iff₀ (by linarith only [hnorm] : (0 : ℝ) < ‖s‖)]
      linarith only [hnorm]
    have h2 : ‖(Complex.digamma (s / 2 + 1) / 2 : ℂ)‖ ≤ (Real.log (2 + |t|) + 8) / 2 := by
      rw [norm_div, norm_ofNat]
      exact div_le_div_of_nonneg_right hdg' (by norm_num)
    have h1 : ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2 + 1) / 2 : ℂ)‖ ≤
        Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 :=
      (norm_add_le _ _).trans (add_le_add hlogpi h2)
    calc ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2 + 1) / 2) - 1 / s‖
        ≤ ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2 + 1) / 2 : ℂ)‖ +
            ‖(1 : ℂ) / s‖ := by
          rw [sub_eq_add_neg]
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_neg]
      _ ≤ (Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2) + 2 := add_le_add h1 hinv
      _ = Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 + 2 := by ring
  · have hfun : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
      funext z; exact hO.gammaFactor_def z
    rw [hfun]
    have hs1re : 0 < (s + 1).re := by
      have h : (s + 1).re = s.re + 1 := by simp
      rw [h, hre_s]; norm_num
    have hcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s)
        (differentiableAt_Gammaℝ (s + 1) hs1re) (by fun_prop)
      simpa [Function.comp_def] using h
    rw [hcomp, logDeriv_Gammaℝ_formula (s + 1) hs1re]
    have hre1 : (1 : ℝ) / 4 ≤ ((s + 1) / 2).re := by
      have h : ((s + 1) / 2).re = s.re / 2 + 1 / 2 := by
        rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]; simp <;> ring
      rw [h, hre_s]; norm_num
    have hre2 : ((s + 1) / 2).re ≤ 8 := by
      have h : ((s + 1) / 2).re = s.re / 2 + 1 / 2 := by
        rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]; simp <;> ring
      rw [h, hre_s]; norm_num
    have him1 : ((s + 1) / 2).im = t / 2 := by
      have h : ((s + 1) / 2).im = s.im / 2 := by
        rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]; simp <;> ring
      rw [h, him_s]
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      (((s + 1) / 2).re) (((s + 1) / 2).im) hre1 hre2
    have hdg' : ‖Complex.digamma ((s + 1) / 2)‖ ≤ Real.log (2 + |t|) + 8 := by
      have hcongr : (((s + 1) / 2).re : ℂ) + (((s + 1) / 2).im : ℂ) * Complex.I = (s + 1) / 2 :=
        Complex.re_add_im _
      rw [← hcongr]
      refine hdg.trans ?_
      rw [him1]
      linarith only [hlog2]
    have h2 : ‖(Complex.digamma ((s + 1) / 2) / 2 : ℂ)‖ ≤ (Real.log (2 + |t|) + 8) / 2 := by
      rw [norm_div, norm_ofNat]
      exact div_le_div_of_nonneg_right hdg' (by norm_num)
    calc ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2 : ℂ)‖
        ≤ Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 :=
          (norm_add_le _ _).trans (add_le_add hlogpi h2)
      _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 + 2 := by linarith only []

/-! ## The Perron integral as a vertical-segment integral of `-L'/L` -/

/-- The truncated Perron integral `(1/2π) ∫_{-T}^{T} L(s, χΛ) x^s/s dt` on `Re s = 1 + 1/log x`. -/
noncomputable def perronIntegral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
    LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
      (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))

/-- The integral of `L'/L · x^s/s` over the vertical segment `Re s = σ`, `|Im s| ≤ T`. -/
noncomputable def vertSeg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x σ T : ℝ) : ℂ :=
  ∫ (t : ℝ) in -T..T,
    logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) *
      (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) / ((σ : ℂ) + Complex.I * (t : ℂ))

lemma LSeries_chiLambda_eq_neg_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
      - logDeriv (DirichletCharacter.LFunction χ) s := by
  rw [LSeries_congr (g := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      χ ((n : ℕ) : ZMod N)) (fun {n} _ => mul_comm _ _) s,
    LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs]
  ring

lemma perronIntegral_eq_vertSeg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x T : ℝ} (hx : 3 ≤ x) :
    perronIntegral χ x T = -(1 / (2 * Real.pi)) * vertSeg χ x (1 + 1 / Real.log x) T := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hpt : ∀ t : ℝ, LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
      - logDeriv (DirichletCharacter.LFunction χ)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    intro t
    apply LSeries_chiLambda_eq_neg_logDeriv
    have hre : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)).re =
        1 + 1 / Real.log x := by simp
    rw [hre]
    have : 0 < 1 / Real.log x := div_pos one_pos hlogx
    linarith only [this]
  have hint : (∫ (t : ℝ) in -T..T, LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
      (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) =
      -(∫ (t : ℝ) in -T..T,
        logDeriv (DirichletCharacter.LFunction χ) (((1 + 1 / Real.log x : ℝ) : ℂ) +
            Complex.I * (t : ℂ)) *
          (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) /
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hpt t]
    ring
  rw [perronIntegral, vertSeg, hint]
  ring

/-! ## Continuity of logarithmic derivatives on the boundary lines -/

lemma continuousOn_logDeriv_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContinuousOn (fun z : ℂ => logDeriv f z) {z : ℂ | f z ≠ 0} := by
  have hderv : ContinuousOn (deriv f) {z : ℂ | f z ≠ 0} := hf.deriv.continuous.continuousOn
  have hFc : ContinuousOn f {z : ℂ | f z ≠ 0} := hf.continuous.continuousOn
  have hdiv : ContinuousOn (fun z : ℂ => deriv f z / f z) {z : ℂ | f z ≠ 0} :=
    ContinuousOn.div hderv hFc (by intro z hz; exact hz)
  simpa [logDeriv] using hdiv

lemma continuousOn_logDeriv_completedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ContinuousOn (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
      {z : ℂ | DirichletCharacter.completedLFunction χ z ≠ 0} :=
  continuousOn_logDeriv_of_differentiable (DirichletCharacter.differentiable_completedLFunction hχ)

lemma continuousOn_logDeriv_L {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ContinuousOn (fun z : ℂ => logDeriv (DirichletCharacter.LFunction χ) z)
      {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0} :=
  continuousOn_logDeriv_of_differentiable (DirichletCharacter.differentiable_LFunction hχ)

/-- Continuity of `logDeriv Gammaℝ` on the half-plane `Re > 0`. -/
lemma continuousOn_logDeriv_Gammaℝ :
    ContinuousOn (fun z : ℂ => logDeriv Complex.Gammaℝ z) {z : ℂ | 0 < z.re} := by
  have hdiff : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (differentiableAt_Gammaℝ_of_shift (fun m h => ?_)).differentiableWithinAt
    have hzpos : 0 < z.re := by simpa using hz
    have hre : (z / 2).re = z.re / 2 := by simp
    have h' := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re, hre] at h'
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hzpos, h']
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderv : ContinuousOn (deriv Complex.Gammaℝ) {z : ℂ | 0 < z.re} :=
    (hdiff.deriv hopen).continuousOn
  have hfun : (fun z : ℂ => logDeriv Complex.Gammaℝ z) =
      fun z : ℂ => deriv Complex.Gammaℝ z / Complex.Gammaℝ z := by
    funext z; rw [logDeriv_apply]
  rw [hfun]
  exact ContinuousOn.div hderv hdiff.continuousOn
    (fun z hz => Complex.Gammaℝ_ne_zero_of_re_pos hz)

/-- Continuity of the logarithmic derivative of the gamma factor in `Re s > -1`, `s ≠ 0`. -/
lemma continuousAt_logDeriv_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hsre : -(1 : ℝ) < s.re) (hs0 : s ≠ 0) :
    ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) z) s := by
  have hshift : ContinuousAt (fun z : ℂ => logDeriv Complex.Gammaℝ (z + 2)) s := by
    have h2 : 0 < (s + 2).re := by
      have : (s + 2).re = s.re + 2 := by simp
      rw [this]; linarith only [hsre]
    have hc : ContinuousAt (fun w : ℂ => logDeriv Complex.Gammaℝ w) (s + 2) :=
      (continuousOn_logDeriv_Gammaℝ.continuousAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2))
    exact hc.comp (f := fun z : ℂ => z + 2) (x := s)
      (continuousAt_id.add continuousAt_const)
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact hE.gammaFactor_def z
    rw [hfun]
    have hcongr : (fun z : ℂ => logDeriv Complex.Gammaℝ z) =ᶠ[𝓝 s]
        (fun z : ℂ => logDeriv Complex.Gammaℝ (z + 2) - 1 / z) := by
      filter_upwards [isOpen_ne.mem_nhds hs0,
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsre] with z hz hzre
      have hkey := logDeriv_Gammaℝ_add_inv (s := z) hz hzre
      have h2 : logDeriv Complex.Gammaℝ (z + 2) = -(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (z / 2 + 1) / 2 := by
        have hz2 : 0 < (z + 2).re := by
          have : (z + 2).re = z.re + 2 := by simp
          rw [this]; linarith only [hzre]
        have h := logDeriv_Gammaℝ_formula (z + 2) hz2
        have he : (z + 2) / 2 = z / 2 + 1 := by ring
        rw [he] at h
        exact h
      rw [h2]
      linear_combination hkey
    exact ContinuousAt.congr
      (hshift.sub (continuousAt_const.div continuousAt_id hs0)) hcongr.symm
  · have hfun : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
      funext z; exact hO.gammaFactor_def z
    rw [hfun]
    have hshift1 : ContinuousAt (fun z : ℂ => logDeriv Complex.Gammaℝ (z + 1)) s := by
      have h2 : 0 < (s + 1).re := by
        have : (s + 1).re = s.re + 1 := by simp
        rw [this]; linarith only [hsre]
      have hc : ContinuousAt (fun w : ℂ => logDeriv Complex.Gammaℝ w) (s + 1) :=
        (continuousOn_logDeriv_Gammaℝ.continuousAt
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2))
      exact hc.comp (f := fun z : ℂ => z + 1) (x := s)
        (continuousAt_id.add continuousAt_const)
    have hcongr : (fun z : ℂ => logDeriv (fun w : ℂ => Complex.Gammaℝ (w + 1)) z) =ᶠ[𝓝 s]
        (fun z : ℂ => logDeriv Complex.Gammaℝ (z + 1)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsre] with z hzre
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun w : ℂ => w + 1) (x := z)
        (differentiableAt_Gammaℝ_of_shift (half_add_one_ne_neg_nat hzre)) (by fun_prop)
      simpa [Function.comp_def] using h
    exact ContinuousAt.congr hshift1 hcongr.symm

lemma continuousOn_logDeriv_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ContinuousOn (fun z : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) z)
      {z : ℂ | -(1 : ℝ) < z.re ∧ z ≠ 0} :=
  fun z hz => (continuousAt_logDeriv_gammaFactor χ hz.1 hz.2).continuousWithinAt

/-! ## Bounds for the boundary integrals of `Λ'/Λ` -/

lemma integral_one_div_one_add_abs_le {T : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ in -T..T, (1 : ℝ) / (1 + |t|)) ≤ 2 * Real.log (1 + T) := by
  have hf : ∀ t : ℝ, 0 < 1 + |t| := fun t => by positivity
  have hcont : Continuous (fun t : ℝ => (1 : ℝ) / (1 + |t|)) :=
    continuous_const.div (continuous_const.add continuous_abs) (fun t => (hf t).ne')
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (1 + |t|)) volume (-T) 0 :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (1 + |t|)) volume 0 T :=
    hcont.intervalIntegrable _ _
  have h1 : (∫ t : ℝ in -T..0, (1 : ℝ) / (1 + |t|)) = Real.log (1 + T) := by
    have hsub := intervalIntegral.integral_comp_neg (a := -T) (b := 0)
      (f := fun u : ℝ => (1 : ℝ) / (1 + u))
    simp only [neg_zero, neg_neg] at hsub
    have hcongr1 : (∫ t : ℝ in -T..0, (1 : ℝ) / (1 + |t|))
        = ∫ t : ℝ in -T..0, (1 : ℝ) / (1 + (-t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : t ≤ 0 := by
        have h2 := ht.2
        rwa [max_eq_right (by linarith only [hT] : -T ≤ 0)] at h2
      show (1 : ℝ) / (1 + |t|) = (1 : ℝ) / (1 + -t)
      rw [abs_of_nonpos ht0]
    rw [hcongr1, hsub]
    have hfun : (fun x : ℝ => (1 : ℝ) / (1 + x)) = fun x : ℝ => (fun u : ℝ => (1 : ℝ) / u) (x + 1) := by
      funext x; ring_nf
    have h := intervalIntegral.integral_comp_add_right (f := fun u : ℝ => (1 : ℝ) / u) (a := 0) (b := T) 1
    rw [hfun, h, zero_add, show T + 1 = 1 + T by ring,
      integral_one_div_of_pos (by norm_num) (by linarith only [hT]), div_one]
  have h2 : (∫ t : ℝ in 0..T, (1 : ℝ) / (1 + |t|)) = Real.log (1 + T) := by
    have hcongr2 : (∫ t : ℝ in 0..T, (1 : ℝ) / (1 + |t|))
        = ∫ t : ℝ in 0..T, (1 : ℝ) / (1 + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := by
        have h1 := ht.1
        rwa [min_eq_left hT] at h1
      show (1 : ℝ) / (1 + |t|) = (1 : ℝ) / (1 + t)
      rw [abs_of_nonneg ht0]
    rw [hcongr2]
    have hfun : (fun x : ℝ => (1 : ℝ) / (1 + x)) = fun x : ℝ => (fun u : ℝ => (1 : ℝ) / u) (x + 1) := by
      funext x; ring_nf
    have h := intervalIntegral.integral_comp_add_right (f := fun u : ℝ => (1 : ℝ) / u) (a := 0) (b := T) 1
    rw [hfun, h, zero_add, show T + 1 = 1 + T by ring,
      integral_one_div_of_pos (by norm_num) (by linarith only [hT]), div_one]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, h1, h2]
  linarith only []

/-- `‖-1/2 + it‖⁻¹ ≤ 3/(1 + |t|)`. -/
lemma inv_norm_half_add_I_le (t : ℝ) :
    (‖(((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)⁻¹ ≤ 3 / (1 + |t|) := by
  set s : ℂ := ((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have him : s.im = t := by rw [hs_def]; simp
  have hre : s.re = -1/2 := by rw [hs_def]; simp
  have hspos : 0 < ‖s‖ := by
    have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    rw [hre] at h1
    norm_num at h1
    linarith only [h1]
  have hsnorm : (1 + |t|) ≤ 3 * ‖s‖ := by
    by_cases h : (1/2 : ℝ) ≤ |t|
    · have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      rw [him] at h1
      linarith only [h, h1]
    · have h2 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      rw [hre] at h2
      norm_num at h2
      have ht : |t| < 1/2 := not_le.mp h
      linarith only [h, h2]
  rw [inv_le_comm₀ hspos (by positivity : (0 : ℝ) < 3 / (1 + |t|)), inv_div,
    div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith only [hsnorm]

lemma norm_logDeriv_completedL_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ≠ 0) (hsre : -(1 : ℝ) < s.re)
    (hΛ : DirichletCharacter.completedLFunction χ s ≠ 0) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
      ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ +
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
  have hγ : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_re_gt_neg_one χ hsre hs
  have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    exact hΛ (by rw [completedL_eq_gammaFactor_mul_L χ hs hsre, h0, mul_zero])
  rw [logDeriv_completedL_eq_add χ hχ hs hsre hL]
  exact norm_add_le _ _

lemma exists_bound_integral_logDeriv_completedL_horizontal {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T' : ℝ, 2 ≤ T' → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - T'|) →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im + T'|) →
      ((∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
            ((y : ℂ) + (T' : ℂ) * Complex.I)‖) ≤
          C * Real.log (N * (T' + 3)) * (Real.log (N * (T' + 3)) + Real.log (1 / δ))) ∧
      ((∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
            ((y : ℂ) - (T' : ℂ) * Complex.I)‖) ≤
          C * Real.log (N * (T' + 3)) * (Real.log (N * (T' + 3)) + Real.log (1 / δ))) := by
  obtain ⟨C1, hC1pos, hC1⟩ := horizontalSegment_logDeriv_bound_le_one χ hχ hχprim
  obtain ⟨C2, hC2pos, hC2⟩ := horizontalGamma_logDeriv_bound χ
  refine ⟨C1 + C2 + 1, by positivity, ?_⟩
  intro T' hT δ hδ hδ1 hs1 hs2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
  have hL1 : 1 ≤ Real.log ((N : ℝ) * (T' + 3)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 5 := by linarith only [Real.exp_one_lt_d9]
    nlinarith only [hN1, he, hT]
  have hδlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ, one_mul]; exact hδ1)
  have hLpos : 0 < Real.log ((N : ℝ) * (T' + 3)) := lt_of_lt_of_le one_pos hL1
  have hbound : ∀ (v : ℝ) (hv : v = T' ∨ v = -T')
      (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - v|),
      (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
          ((y : ℂ) + (v : ℂ) * Complex.I)‖) ≤
        (C1 + C2 + 1) * Real.log (N * (T' + 3)) *
          (Real.log (N * (T' + 3)) + Real.log (1 / δ)) := by
    intro v hv hsep
    have hv2 : 2 ≤ |v| := by
      rcases hv with h | h
      · rw [h, abs_of_nonneg (by linarith only [hT])]; exact hT
      · rw [h, abs_neg, abs_of_nonneg (by linarith only [hT])]; exact hT
    have hne0 : ∀ y : ℝ, ((y : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
      intro y h0
      have him : (((y : ℂ) + (v : ℂ) * Complex.I)).im = v := by simp
      have h1 := congrArg Complex.im h0
      rw [him] at h1
      simp at h1
      rw [h1, abs_zero] at hv2
      linarith only [hv2]
    have hrev : ∀ y : ℝ, (((y : ℂ) + (v : ℂ) * Complex.I)).re = y := fun y => by simp
    have hmemΛ : ∀ y ∈ Set.uIcc (-1/2 : ℝ) 2, DirichletCharacter.completedLFunction χ
        ((y : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
      intro y hy h0
      have hle := hsep _ h0
      have him : (((y : ℂ) + (v : ℂ) * Complex.I)).im = v := by simp
      rw [him, sub_self, abs_zero] at hle
      linarith only [hδ, hle]
    have hle_half : ∀ y ∈ Set.uIcc (-1/2 : ℝ) 2, -(1 / 2 : ℝ) ≤ y := by
      intro y hy
      have hy' := hy
      rw [Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hy'
      linarith only [hy'.1, hy']
    have hre_ge : ∀ y ∈ Set.uIcc (-1/2 : ℝ) 2, -(1 : ℝ) < (((y : ℂ) + (v : ℂ) * Complex.I)).re := by
      intro y hy
      rw [hrev y]
      linarith only [hle_half y hy, hle_half, hy]
    have hmemγ : ∀ y ∈ Set.uIcc (-1/2 : ℝ) 2, DirichletCharacter.gammaFactor χ
        ((y : ℂ) + (v : ℂ) * Complex.I) ≠ 0 :=
      fun y hy => gammaFactor_ne_zero_of_re_gt_neg_one χ (hre_ge y hy) (hne0 y)
    have hmemL : ∀ y ∈ Set.uIcc (-1/2 : ℝ) 2, DirichletCharacter.LFunction χ
        ((y : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
      intro y hy h0
      have hprod := completedL_eq_gammaFactor_mul_L χ (hne0 y) (hre_ge y hy)
      rw [h0, mul_zero] at hprod
      exact hmemΛ y hy hprod
    have hlc : ∀ y ∈ Set.uIcc (-1/2 : ℝ) 2, -(1 : ℝ) < y := fun y hy => by linarith only [hle_half y hy, hle_half, hy]
    have hpt : ∀ y ∈ Set.Icc (-1/2 : ℝ) 2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖ ≤
        ‖logDeriv (DirichletCharacter.gammaFactor χ) ((y : ℂ) + (v : ℂ) * Complex.I)‖ +
          ‖logDeriv (DirichletCharacter.LFunction χ) ((y : ℂ) + (v : ℂ) * Complex.I)‖ := by
      intro y hy
      have hyu : y ∈ Set.uIcc (-1/2 : ℝ) 2 := by
        rw [Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)]; exact hy
      exact norm_logDeriv_completedL_le χ hχ (hne0 y) (hre_ge y hyu) (hmemΛ y hyu)
    have hcontΛ : ContinuousOn (fun y : ℝ => ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) (Set.uIcc (-1/2 : ℝ) 2) :=
      ((continuousOn_logDeriv_completedL χ hχ).comp
        (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I)
        (by fun_prop) (fun y hy => hmemΛ y hy)).norm
    have hcontγ : ContinuousOn (fun y : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) (Set.uIcc (-1/2 : ℝ) 2) :=
      ((continuousOn_logDeriv_gammaFactor χ).comp
        (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I)
        (by fun_prop) (fun y hy => ⟨hre_ge y hy, hne0 y⟩)).norm
    have hcontL : ContinuousOn (fun y : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) (Set.uIcc (-1/2 : ℝ) 2) :=
      ((continuousOn_logDeriv_L χ hχ).comp
        (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I)
        (by fun_prop) (fun y hy => hmemL y hy)).norm
    have hintΛ : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) volume (-1/2) 2 :=
      hcontΛ.intervalIntegrable
    have hintγ : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) volume (-1/2) 2 :=
      hcontγ.intervalIntegrable
    have hintL : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) volume (-1/2) 2 :=
      hcontL.intervalIntegrable
    have hLb : (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) ≤
          C1 * Real.log (N * (T' + 3)) * (Real.log (N * (T' + 3)) + Real.log (1 / δ)) := by
      rcases hv with hvT | hvT
      · rw [hvT]; exact (hC1 T' hT δ hδ hδ1 hs1 hs2).1
      · rw [hvT]
        have hconv : (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
            ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I)‖)
            = ∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
              ((y : ℂ) - (T' : ℂ) * Complex.I)‖ := by
          apply intervalIntegral.integral_congr
          intro y hy
          simp only
          rw [show ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I) =
              ((y : ℂ) - (T' : ℂ) * Complex.I) by push_cast; ring]
        rw [hconv]; exact (hC1 T' hT δ hδ hδ1 hs1 hs2).2
    have hGb : (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) ≤ C2 * Real.log (N * (T' + 3)) := by
      rcases hv with hvT | hvT
      · rw [hvT]; exact (hC2 T' hT).1
      · rw [hvT]
        have hconv : (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
            ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I)‖)
            = ∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
              ((y : ℂ) - (T' : ℂ) * Complex.I)‖ := by
          apply intervalIntegral.integral_congr
          intro y hy
          simp only
          rw [show ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I) =
              ((y : ℂ) - (T' : ℂ) * Complex.I) by push_cast; ring]
        rw [hconv]; exact (hC2 T' hT).2
    have hstep1 : (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((y : ℂ) + (v : ℂ) * Complex.I)‖) ≤
        (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
            ((y : ℂ) + (v : ℂ) * Complex.I)‖) +
        (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
            ((y : ℂ) + (v : ℂ) * Complex.I)‖) := by
      calc (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
              ((y : ℂ) + (v : ℂ) * Complex.I)‖)
          ≤ ∫ y : ℝ in (-1/2)..2, (‖logDeriv (DirichletCharacter.gammaFactor χ)
                ((y : ℂ) + (v : ℂ) * Complex.I)‖ +
              ‖logDeriv (DirichletCharacter.LFunction χ) ((y : ℂ) + (v : ℂ) * Complex.I)‖) :=
            intervalIntegral.integral_mono_on (by norm_num : (-1/2:ℝ) ≤ 2) hintΛ
              (hintγ.add hintL) hpt
        _ = _ := intervalIntegral.integral_add hintγ hintL
    refine hstep1.trans ?_
    have h1 : (1 : ℝ) ≤ Real.log (N * (T' + 3)) + Real.log (1 / δ) := by linarith only [hL1, hδlog]
    have hcomb : C2 * Real.log (N * (T' + 3)) + C1 * Real.log (N * (T' + 3)) *
        (Real.log (N * (T' + 3)) + Real.log (1 / δ)) ≤
        (C1 + C2 + 1) * Real.log (N * (T' + 3)) *
          (Real.log (N * (T' + 3)) + Real.log (1 / δ)) := by
      have h2 : C2 * Real.log (N * (T' + 3)) ≤
          (C2 + 1) * Real.log (N * (T' + 3)) *
            (Real.log (N * (T' + 3)) + Real.log (1 / δ)) := by
        have h3 : C2 ≤ (C2 + 1) * (Real.log (N * (T' + 3)) + Real.log (1 / δ)) := by
          nlinarith only [h1, hC2pos, hL1, hδlog]
        calc C2 * Real.log (N * (T' + 3))
            ≤ ((C2 + 1) * (Real.log (N * (T' + 3)) + Real.log (1 / δ))) *
                Real.log (N * (T' + 3)) :=
              mul_le_mul_of_nonneg_right h3 hLpos.le
          _ = (C2 + 1) * Real.log (N * (T' + 3)) *
                (Real.log (N * (T' + 3)) + Real.log (1 / δ)) := by ring
      linarith only [h2, hC1pos, hLpos]
    linarith [hLb, hGb, hcomb]
  constructor
  · exact hbound T' (Or.inl rfl) hs1
  · have h := hbound (-T') (Or.inr rfl) (fun ρ hρ => by
      have h2 := hs2 ρ hρ
      rw [show ρ.im - (-T') = ρ.im + T' by ring]
      exact h2)
    have hconv : (∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I)‖)
        = ∫ y : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
          ((y : ℂ) - (T' : ℂ) * Complex.I)‖ := by
      apply intervalIntegral.integral_congr
      intro y hy
      simp only
      rw [show ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I) =
          ((y : ℂ) - (T' : ℂ) * Complex.I) by push_cast; ring]
    rw [hconv] at h
    exact h

lemma exists_bound_integral_logDeriv_completedL_leftEdge {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.completedLFunction χ)
          (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
        ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        C * (Real.log (N * (T + 3))) ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := leftEdge_logDeriv_bound χ hχ hχprim
  refine ⟨C1 + 61, by positivity, fun T hT => ?_⟩
  set L : ℝ := Real.log ((N : ℝ) * (T + 3)) with hLdef
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 5 := by linarith only [Real.exp_one_lt_d9]
    nlinarith only [hN1, he, hT]
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlog2T : Real.log (2 + T) ≤ L := by
    rw [hLdef]; apply Real.log_le_log (by positivity); nlinarith only [hN1, hT]
  have hlog1T : Real.log (1 + T) ≤ L := by
    rw [hLdef]; apply Real.log_le_log (by positivity); nlinarith only [hN1, hT]
  have hlogpi : Real.log Real.pi / 2 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith only [Real.pi_lt_four, h]
  set M : ℝ := Real.log Real.pi / 2 + (Real.log (2 + T) + 8) / 2 + 2 with hMdef
  have hM : M ≤ 10 * L := by
    rw [hMdef]; linarith only [hL1, hlog2T, hlogpi]
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith only [Real.pi_gt_three])
    have h2 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith only [hT])
    linarith only [h1, h2]
  set s : ℝ → ℂ := fun t => (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hsdef
  have hsre : ∀ t : ℝ, (s t).re = -1 / 2 := fun t => by simp [hsdef]
  have hne0 : ∀ t : ℝ, s t ≠ 0 := by
    intro t h
    have h0 : (s t).re = 0 := by rw [h]; simp
    rw [hsre t] at h0
    norm_num at h0
  have hre0 : ∀ t : ℝ, -(1 : ℝ) < (s t).re := by
    intro t; rw [hsre t]; norm_num
  have hnormpos : ∀ t : ℝ, 0 < ‖s t‖ := by
    intro t
    have h1 : |(s t).re| ≤ ‖s t‖ := Complex.abs_re_le_norm (s t)
    rw [hsre t] at h1
    norm_num at h1
    linarith only [h1]
  have hLne : ∀ t : ℝ, DirichletCharacter.LFunction χ (s t) ≠ 0 :=
    fun t => LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
  have hΛne : ∀ t : ℝ, DirichletCharacter.completedLFunction χ (s t) ≠ 0 := by
    intro t h
    have hγ : DirichletCharacter.gammaFactor χ (s t) ≠ 0 :=
      gammaFactor_ne_zero_of_re_gt_neg_one χ (hre0 t) (hne0 t)
    have hprod := completedL_eq_gammaFactor_mul_L χ (hne0 t) (hre0 t)
    rw [h] at hprod
    have hL0 : DirichletCharacter.LFunction χ (s t) = 0 := by
      rcases mul_eq_zero.mp hprod.symm with h1 | h1
      · exact absurd h1 hγ
      · exact h1
    exact hLne t hL0
  have hγpt : ∀ t ∈ Set.Icc (-T) T, ‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ /
      ‖s t‖ ≤ M * (3 / (1 + |t|)) := by
    intro t ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have hγ := norm_logDeriv_gammaFactor_leftEdge χ t
    have hlogmono : Real.log (2 + |t|) ≤ Real.log (2 + T) := by
      apply Real.log_le_log (by positivity); linarith only [htT]
    have hA : (Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 + 2) ≤ M := by
      rw [hMdef]; linarith only [hlogmono]
    have hinv : (‖s t‖)⁻¹ ≤ 3 / (1 + |t|) := inv_norm_half_add_I_le t
    rw [div_eq_mul_inv]
    calc ‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ * (‖s t‖)⁻¹
        ≤ (Real.log Real.pi / 2 + (Real.log (2 + |t|) + 8) / 2 + 2) * (‖s t‖)⁻¹ :=
          mul_le_mul_of_nonneg_right hγ (by positivity)
      _ ≤ M * (3 / (1 + |t|)) :=
          mul_le_mul hA hinv (by positivity) hMnn
  have hΛpt : ∀ t ∈ Set.Icc (-T) T, ‖logDeriv (DirichletCharacter.completedLFunction χ) (s t)‖ /
      ‖s t‖ ≤ M * (3 / (1 + |t|)) + ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ / ‖s t‖ := by
    intro t ht
    have hbase := norm_logDeriv_completedL_le χ hχ (hne0 t) (hre0 t) (hΛne t)
    rw [div_eq_mul_inv]
    calc ‖logDeriv (DirichletCharacter.completedLFunction χ) (s t)‖ * (‖s t‖)⁻¹
        ≤ (‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ +
            ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖) * (‖s t‖)⁻¹ :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = ‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ * (‖s t‖)⁻¹ +
            ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ * (‖s t‖)⁻¹ := by ring
      _ ≤ M * (3 / (1 + |t|)) + ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ / ‖s t‖ :=
          add_le_add_left (hγpt t ht) _
  have hcontΛ : Continuous (fun t : ℝ => ‖logDeriv (DirichletCharacter.completedLFunction χ) (s t)‖ /
      ‖s t‖) := by
    have h1 : Continuous (fun t : ℝ => logDeriv (DirichletCharacter.completedLFunction χ) (s t)) :=
      (continuousOn_logDeriv_completedL χ hχ).comp_continuous (by fun_prop) (fun t => hΛne t)
    have h2 : Continuous (fun t : ℝ => ‖s t‖) := continuous_norm.comp (by fun_prop)
    exact h1.norm.div h2 (fun t => (hnormpos t).ne')
  have hcontγ : Continuous (fun t : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ /
      ‖s t‖) := by
    have h1 : Continuous (fun t : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) (s t)) :=
      (continuousOn_logDeriv_gammaFactor χ).comp_continuous (by fun_prop)
        (fun t => ⟨hre0 t, hne0 t⟩)
    have h2 : Continuous (fun t : ℝ => ‖s t‖) := continuous_norm.comp (by fun_prop)
    exact h1.norm.div h2 (fun t => (hnormpos t).ne')
  have hcontL : Continuous (fun t : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ /
      ‖s t‖) := by
    have h1 : Continuous (fun t : ℝ => logDeriv (DirichletCharacter.LFunction χ) (s t)) :=
      (continuousOn_logDeriv_L χ hχ).comp_continuous (by fun_prop) (fun t => hLne t)
    have h2 : Continuous (fun t : ℝ => ‖s t‖) := continuous_norm.comp (by fun_prop)
    exact h1.norm.div h2 (fun t => (hnormpos t).ne')
  have hcontC : Continuous (fun t : ℝ => M * (3 / (1 + |t|))) :=
    continuous_const.mul (continuous_const.div (continuous_const.add continuous_abs)
      (fun t => by positivity))
  have hstep : (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.completedLFunction χ) (s t)‖ / ‖s t‖)
      ≤ ∫ t : ℝ in -T..T, (M * (3 / (1 + |t|)) +
        ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ / ‖s t‖) :=
    intervalIntegral.integral_mono_on (by linarith only [hT]) (hcontΛ.intervalIntegrable (-T) T)
      ((hcontC.add hcontL).intervalIntegrable (-T) T) hΛpt
  have hγint : (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ / ‖s t‖)
      ≤ M * 3 * (2 * Real.log (1 + T)) := by
    have h1 : (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.gammaFactor χ) (s t)‖ / ‖s t‖)
        ≤ ∫ t : ℝ in -T..T, M * (3 / (1 + |t|)) :=
      intervalIntegral.integral_mono_on (by linarith only [hT]) (hcontγ.intervalIntegrable (-T) T)
        (hcontC.intervalIntegrable (-T) T) hγpt
    have h2 : (∫ t : ℝ in -T..T, M * (3 / (1 + |t|))) = M * (3 * ∫ t : ℝ in -T..T, 1 / (1 + |t|)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have h3 := integral_one_div_one_add_abs_le (T := T) (by linarith only [hT])
    rw [h2] at h1
    nlinarith only [h1, h3, hM, hlog1T, hMnn, hLpos]
  have hsplit : (∫ t : ℝ in -T..T, (M * (3 / (1 + |t|)) +
        ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ / ‖s t‖)) =
      (∫ t : ℝ in -T..T, M * (3 / (1 + |t|))) +
        ∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ / ‖s t‖ :=
    intervalIntegral.integral_add (hcontC.intervalIntegrable (-T) T)
      (hcontL.intervalIntegrable (-T) T)
  have h2int : (∫ t : ℝ in -T..T, M * (3 / (1 + |t|))) ≤ M * 3 * (2 * Real.log (1 + T)) := by
    have h2 : (∫ t : ℝ in -T..T, M * (3 / (1 + |t|))) = M * (3 * ∫ t : ℝ in -T..T, 1 / (1 + |t|)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have h3 := integral_one_div_one_add_abs_le (T := T) (by linarith only [hT])
    rw [h2]
    nlinarith only [h3, hM, hMnn, hlog1T, hLpos]
  have hLint : (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.LFunction χ) (s t)‖ / ‖s t‖)
      ≤ C1 * L ^ 2 := by
    have h := hC1 T hT
    rw [hLdef]
    exact h
  refine hstep.trans ?_
  rw [hsplit]
  have hγ2 : M * 3 * (2 * Real.log (1 + T)) ≤ 60 * L ^ 2 := by
    nlinarith only [hM, hlog1T, hLpos, hMnn, hL1, hlog2T, hlogpi, hMdef]
  nlinarith [h2int, hLint, hγ2, hC1pos, hL1]

/-! ## The rectangle edge decomposition in explicit form -/

lemma rectInt_eq_edges {σ T' : ℝ} (f : ℂ → ℂ) :
    rectInt (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I)
        ((σ : ℂ) + (T' : ℂ) * Complex.I) f =
      (∫ y : ℝ in (-1/2)..σ, f ((y : ℂ) - (T' : ℂ) * Complex.I))
      - (∫ y : ℝ in (-1/2)..σ, f ((y : ℂ) + (T' : ℂ) * Complex.I))
      + Complex.I * (∫ t : ℝ in (-T')..T', f ((σ : ℂ) + Complex.I * (t : ℂ)))
      - Complex.I * (∫ t : ℝ in (-T')..T', f (((-1/2 : ℝ) : ℂ) + Complex.I * (t : ℂ))) := by
  rw [rectInt_eq_def]
  have h1 : (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I).re = -1/2 := by simp
  have h2 : (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I).im = -T' := by simp
  have h3 : (((σ : ℂ) + (T' : ℂ) * Complex.I)).re = σ := by simp
  have h4 : (((σ : ℂ) + (T' : ℂ) * Complex.I)).im = T' := by simp
  rw [h1, h2, h3, h4]
  have e1 : (∫ x : ℝ in -1/2..σ, f (↑x + ↑(-T') * Complex.I))
      = ∫ x : ℝ in -1/2..σ, f ((x : ℂ) - (T' : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    refine congrArg f ?_
    push_cast
    ring
  have e3 : (∫ y : ℝ in -T'..T', f (↑σ + ↑y * Complex.I))
      = ∫ t : ℝ in -T'..T', f ((σ : ℂ) + Complex.I * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro y _
    refine congrArg f ?_
    ring
  have e4 : (∫ y : ℝ in -T'..T', f (((-1/2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = ∫ t : ℝ in -T'..T', f (((-1/2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro y _
    refine congrArg f ?_
    ring
  rw [e1, e3, e4]
/-! ## The explicit formula for `x >= 3` -/

lemma gamma_const_bound :
    ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2 : ℂ)‖ ≤ 3 ∧
      ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (1 / 2 : ℂ) / 2 : ℂ)‖ ≤ 4 := by
  have hlogpi2 : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ ≤ 1 := by
    have hlogpi' : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (le_of_lt Real.pi_pos)]
    rw [hlogpi', norm_div, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have h1 : Real.log Real.pi ≤ 2 := by
      have h2 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
      have h3 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith only [this]
      rw [h3] at h2; linarith only [h2, h4]
    have h5 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith only [Real.pi_gt_three])
    rw [abs_of_nonneg h5]; linarith only [h1]
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith only [Real.one_half_lt_eulerMascheroniConstant]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith only [this]
  have hlog2n : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hd1 : Complex.digamma 1 = ((-Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [Complex.digamma_one]
    push_cast
    ring
  have hd2 : Complex.digamma (1 / 2 : ℂ) =
      ((-(2 * Real.log 2 + Real.eulerMascheroniConstant) : ℝ) : ℂ) := by
    rw [Complex.digamma_one_half]
    have h : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
      rw [← Complex.ofReal_log (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h]
    push_cast
    ring
  constructor
  · have h2 : ‖(((-Real.eulerMascheroniConstant : ℝ)) : ℂ) / 2‖ ≤ 1 := by
      rw [norm_div, norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hγ0]), ]
      linarith only [hγ]
    rw [hd1]
    have h3 := norm_add_le (-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)
      ((((-Real.eulerMascheroniConstant : ℝ)) : ℂ) / 2)
    linarith only [hlogpi2, h2, h3]
  · have h2 : ‖(((-(2 * Real.log 2 + Real.eulerMascheroniConstant) : ℝ)) : ℂ) / 2‖ ≤ 2 := by
      rw [norm_div, norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hγ0, hlog2n])]
      linarith only [hγ, hlog2]
    rw [hd2]
    have h3 := norm_add_le (-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)
      ((((-(2 * Real.log 2 + Real.eulerMascheroniConstant) : ℝ)) : ℂ) / 2)
    linarith only [hlogpi2, h2, h3]
/-! ## Small algebraic helpers for the final assembly -/

lemma inv_mul_I (a : ℂ) (_ha : a ≠ 0) : (a * Complex.I)⁻¹ * Complex.I = a⁻¹ := by
  rw [mul_inv, mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, mul_one]

lemma two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  have h : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  intro h0
  exact h (by linear_combination (1/2) * h0)

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero two_pi_ne_zero Complex.I_ne_zero

/-- The edge integrals of `f` over the rectangle `[-1/2, σ] × [-T', T']`. -/
lemma rectInt_eq_edges_general {σ T' : ℝ} (hσT : σ ≤ 2) (f : ℂ → ℂ) :
    rectInt (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I)
        ((σ : ℂ) + (T' : ℂ) * Complex.I) f =
      (∫ y : ℝ in (-1/2)..σ, f ((y : ℂ) - (T' : ℂ) * Complex.I))
      - (∫ y : ℝ in (-1/2)..σ, f ((y : ℂ) + (T' : ℂ) * Complex.I))
      + Complex.I * (∫ t : ℝ in (-T')..T', f ((σ : ℂ) + Complex.I * (t : ℂ)))
      - Complex.I * (∫ t : ℝ in (-T')..T', f (((-1/2 : ℝ) : ℂ) + Complex.I * (t : ℂ))) :=
  rectInt_eq_edges f


/-- Pointwise splitting of the logarithmic derivative of `Λ = γ · L` on the rectangle boundary. -/
lemma rectInt_logDeriv_L_eq_sub {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {z w : ℂ} (_hzre : z.re < w.re) (_hzim : z.im < w.im)
    (h0 : ∀ s ∈ rectBoundary z w, s ≠ 0)
    (hre : ∀ s ∈ rectBoundary z w, -(1 : ℝ) < s.re)
    (hnz : ∀ s ∈ rectBoundary z w, DirichletCharacter.completedLFunction χ s ≠ 0) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / s)) =
      rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
          ((x : ℂ) ^ s / s)) -
        rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s *
          ((x : ℂ) ^ s / s)) := by
  have hLne : ∀ s ∈ rectBoundary z w, DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s hs hL
    exact hnz s hs (by
      rw [completedL_eq_gammaFactor_mul_L χ (h0 s hs) (hre s hs), hL, mul_zero])
  have hpoint : ∀ s ∈ rectBoundary z w,
      logDeriv (DirichletCharacter.LFunction χ) s * ((x : ℂ) ^ s / s) =
        (logDeriv (DirichletCharacter.completedLFunction χ) s * ((x : ℂ) ^ s / s)) +
          (-1) * (logDeriv (DirichletCharacter.gammaFactor χ) s * ((x : ℂ) ^ s / s)) := by
    intro s hs
    rw [logDeriv_completedL_eq_add χ hχ (h0 s hs) (hre s hs) (hLne s hs)]
    ring
  have hcontΛ : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      logDeriv (DirichletCharacter.completedLFunction χ) s * ((x : ℂ) ^ s / s)) s := by
    intro s hs
    have hs0 := h0 s hs
    have hΛs := hnz s hs
    have hlog : ContinuousAt (fun z : ℂ =>
        logDeriv (DirichletCharacter.completedLFunction χ) z) s := by
      rw [show (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z) =
          fun z => deriv (DirichletCharacter.completedLFunction χ) z /
            DirichletCharacter.completedLFunction χ z from
        funext (fun z => logDeriv_apply _ _)]
      exact ((DirichletCharacter.differentiable_completedLFunction hχ).deriv.continuous.continuousAt).div
        ((DirichletCharacter.differentiable_completedLFunction hχ).continuous.continuousAt) hΛs
    exact hlog.mul (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt
      continuousAt_id hs0)
  have hcontγ : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      logDeriv (DirichletCharacter.gammaFactor χ) s * ((x : ℂ) ^ s / s)) s := by
    intro s hs
    exact (continuousAt_logDeriv_gammaFactor χ (hre s hs) (h0 s hs)).mul
      (ContinuousAt.div ((cpow_differentiable_of_pos hx) s).continuousAt continuousAt_id (h0 s hs))
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hcontΛ
  obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hcontγ
  rw [rectInt_congr_boundary' hpoint]
  rw [rectInt_add'' a1 (b1.const_mul (-1)) a2 (b2.const_mul (-1)) a3 (b3.const_mul (-1))
    a4 (b4.const_mul (-1))]
  rw [rectInt_const_mul' (-1)]
  ring

/-- The integrand `logDeriv F s * x^s / s` of the explicit formula. -/
noncomputable def explF (F : ℂ → ℂ) (x : ℝ) : ℂ → ℂ := fun s => logDeriv F s * ((x : ℂ) ^ s / s)

lemma explF_apply (F : ℂ → ℂ) (x : ℝ) (s : ℂ) :
    explF F x s = logDeriv F s * ((x : ℂ) ^ s / s) := rfl

/-- Pointwise norm bound for the horizontal integrand. -/
lemma norm_explF_le {F : ℂ → ℂ} {x σ y v : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x)
    (hyσ : y ≤ σ) (hv : 0 < |v|) :
    ‖explF F x ((y : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (x ^ σ / |v|) * ‖logDeriv F ((y : ℂ) + (v : ℂ) * Complex.I)‖ := by
  set s : ℂ := (y : ℂ) + (v : ℂ) * Complex.I with hs
  have hre : s.re = y := by rw [hs]; simp
  have him : s.im = v := by rw [hs]; simp
  have hsnorm : |v| ≤ ‖s‖ := by
    have h1 := Complex.abs_im_le_norm s
    rwa [him] at h1
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le hv hsnorm
  rw [explF_apply, norm_mul, norm_div, cpow_norm_ofReal_mul x hx0, hre]
  have hdiv : x ^ y / ‖s‖ ≤ x ^ σ / |v| :=
    div_le_div₀ (Real.rpow_nonneg hx0.le σ) (Real.rpow_le_rpow_of_exponent_le hx1 hyσ) hv hsnorm
  have hlog0 : 0 ≤ ‖logDeriv F s‖ := norm_nonneg _
  calc ‖logDeriv F s‖ * (x ^ y / ‖s‖) ≤ ‖logDeriv F s‖ * (x ^ σ / |v|) :=
        mul_le_mul_of_nonneg_left hdiv hlog0
    _ = (x ^ σ / |v|) * ‖logDeriv F s‖ := by ring

lemma norm_explF_le_upper {F : ℂ → ℂ} {x σ y T' : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x)
    (hyσ : y ≤ σ) (hT' : 0 < T') :
    ‖explF F x ((y : ℂ) + (T' : ℂ) * Complex.I)‖ ≤
      (x ^ σ / T') * ‖logDeriv F ((y : ℂ) + (T' : ℂ) * Complex.I)‖ := by
  have h := norm_explF_le (F := F) (σ := σ) (y := y) (v := T') hx0 hx1 hyσ (by rwa [abs_of_pos hT'])
  rwa [abs_of_pos hT'] at h

lemma norm_explF_le_lower {F : ℂ → ℂ} {x σ y T' : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x)
    (hyσ : y ≤ σ) (hT' : 0 < T') :
    ‖explF F x ((y : ℂ) - (T' : ℂ) * Complex.I)‖ ≤
      (x ^ σ / T') * ‖logDeriv F ((y : ℂ) - (T' : ℂ) * Complex.I)‖ := by
  have h := norm_explF_le (F := F) (σ := σ) (y := y) (v := -T') hx0 hx1 hyσ
    (by rw [abs_neg, abs_of_pos hT']; exact hT')
  rw [abs_neg, abs_of_pos hT'] at h
  have hvv : ((y : ℂ) + (((-T' : ℝ)) : ℂ) * Complex.I) = (y : ℂ) - (T' : ℂ) * Complex.I := by
    push_cast; ring
  rwa [hvv] at h

/-- `x ^ (1 + 1/log x) = e * x` for `x > 1`. -/
lemma rpow_one_add_inv_log {x : ℝ} (hx : 1 < x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0]
  have h : Real.log x * (1 / Real.log x) = 1 := by field_simp
  rw [h, mul_comm]

/-- Bound for the horizontal edge integral of `f_L` (upper height `+T'`). -/
lemma norm_horizontal_explF_le_upper {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x σ T' : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hσ : (-1 / 2 : ℝ) ≤ σ) (hσ2 : σ ≤ 2)
    (hT' : 0 < T')
    (hcont : ContinuousOn (fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) + (T' : ℂ) * Complex.I)) (Set.uIcc (-1 / 2 : ℝ) 2)) :
    ‖(∫ y in (-1 / 2)..σ, explF (DirichletCharacter.LFunction χ) x
        ((y : ℂ) + (T' : ℂ) * Complex.I))‖
      ≤ (x ^ σ / T') * ∫ y in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
          ((y : ℂ) + (T' : ℂ) * Complex.I)‖ := by
  have hIntg2 : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) + (T' : ℂ) * Complex.I)‖) volume (-1 / 2 : ℝ) 2 := hcont.norm.intervalIntegrable
  have hsub : Set.uIcc (-1 / 2 : ℝ) σ ⊆ Set.uIcc (-1 / 2 : ℝ) 2 := by
    rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc le_rfl hσ2
  have hIntg : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) + (T' : ℂ) * Complex.I)‖) volume (-1 / 2 : ℝ) σ :=
    (hcont.mono hsub).norm.intervalIntegrable
  have hmain : ‖(∫ y in (-1 / 2)..σ, explF (DirichletCharacter.LFunction χ) x
        ((y : ℂ) + (T' : ℂ) * Complex.I))‖
      ≤ ∫ y in (-1 / 2)..σ, (x ^ σ / T') * ‖logDeriv (DirichletCharacter.LFunction χ)
          ((y : ℂ) + (T' : ℂ) * Complex.I)‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hσ ?_ (hIntg.const_mul (x ^ σ / T'))
    filter_upwards with y hy
    exact norm_explF_le_upper hx0 hx1 hy.2 hT'
  rw [intervalIntegral.integral_const_mul] at hmain
  refine hmain.trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.rpow_nonneg hx0.le σ) hT'.le)
  exact intervalIntegral.integral_mono_interval (le_refl (-1 / 2 : ℝ)) hσ hσ2
    (ae_of_all _ (fun y => norm_nonneg _)) hIntg2

/-- Bound for the horizontal edge integral of `f_L` (lower height `-T'`). -/
lemma norm_horizontal_explF_le_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x σ T' : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hσ : (-1 / 2 : ℝ) ≤ σ) (hσ2 : σ ≤ 2)
    (hT' : 0 < T')
    (hcont : ContinuousOn (fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) - (T' : ℂ) * Complex.I)) (Set.uIcc (-1 / 2 : ℝ) 2)) :
    ‖(∫ y in (-1 / 2)..σ, explF (DirichletCharacter.LFunction χ) x
        ((y : ℂ) - (T' : ℂ) * Complex.I))‖
      ≤ (x ^ σ / T') * ∫ y in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
          ((y : ℂ) - (T' : ℂ) * Complex.I)‖ := by
  have hIntg2 : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) - (T' : ℂ) * Complex.I)‖) volume (-1 / 2 : ℝ) 2 := hcont.norm.intervalIntegrable
  have hsub : Set.uIcc (-1 / 2 : ℝ) σ ⊆ Set.uIcc (-1 / 2 : ℝ) 2 := by
    rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc le_rfl hσ2
  have hIntg : IntervalIntegrable (fun y : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) - (T' : ℂ) * Complex.I)‖) volume (-1 / 2 : ℝ) σ :=
    (hcont.mono hsub).norm.intervalIntegrable
  have hmain : ‖(∫ y in (-1 / 2)..σ, explF (DirichletCharacter.LFunction χ) x
        ((y : ℂ) - (T' : ℂ) * Complex.I))‖
      ≤ ∫ y in (-1 / 2)..σ, (x ^ σ / T') * ‖logDeriv (DirichletCharacter.LFunction χ)
          ((y : ℂ) - (T' : ℂ) * Complex.I)‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hσ ?_ (hIntg.const_mul (x ^ σ / T'))
    filter_upwards with y hy
    exact norm_explF_le_lower hx0 hx1 hy.2 hT'
  rw [intervalIntegral.integral_const_mul] at hmain
  refine hmain.trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.rpow_nonneg hx0.le σ) hT'.le)
  exact intervalIntegral.integral_mono_interval (le_refl (-1 / 2 : ℝ)) hσ hσ2
    (ae_of_all _ (fun y => norm_nonneg _)) hIntg2

/-- Bound for the left-edge integral of `f_L` at `Re s = -1/2`. -/
lemma norm_leftEdge_explF_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {x T' : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hT' : 0 ≤ T') :
    ‖(∫ t in (-T')..T', explF (DirichletCharacter.LFunction χ) x
        (((-1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖
      ≤ x ^ (-(1 / 2) : ℝ) * ∫ t in (-T')..T',
          ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
            ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by
  have hc := Commons.NumberTheory.DirichletCharacter.continuous_logDeriv_LFunction_of_re_eq_neg_half
    χ hχ hχprim
  have hcont : Continuous (fun t : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
        ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖) := by
    refine Continuous.div hc.norm (by fun_prop) ?_
    intro t
    refine norm_ne_zero_iff.mpr (fun h => ?_)
    have h' := congrArg Complex.re h
    simp at h'
  have hIntg : IntervalIntegrable (fun t : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
        ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖) volume (-T') T' :=
    hcont.intervalIntegrable _ _
  have hmain : ‖(∫ t in (-T')..T', explF (DirichletCharacter.LFunction χ) x
        (((-1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖
      ≤ ∫ t in (-T')..T', x ^ (-(1 / 2) : ℝ) * (‖logDeriv (DirichletCharacter.LFunction χ)
          (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
            ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith only [hT']) ?_ (hIntg.const_mul _)
    filter_upwards with t _
    have hs : (((-1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by ring
    rw [hs, explF_apply, norm_mul, norm_div, cpow_norm_ofReal_mul x hx0]
    have him : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -(1 / 2) := by
      simp
      norm_num
    rw [him]
    exact le_of_eq (by ring)
  rw [intervalIntegral.integral_const_mul] at hmain
  exact hmain

/-- The three finsum summands over the zeros of `Λ`. -/
noncomputable def zeroSummandT {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x T : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
    (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)

noncomputable def zeroSummandR {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ)
    (z w : ℂ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
    (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then (x : ℂ) ^ ρ / ρ else 0)

noncomputable def zeroSummandW {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x T T' : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
    (if T < |ρ.im| ∧ |ρ.im| ≤ T' then (x : ℂ) ^ ρ / ρ else 0)

/-- Difference of the truncated zero sums: the zeros between the two heights. -/
lemma zeroSum_diff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {x T σ T' : ℝ} {z w : ℂ}
    (hzre : z.re = (-1 / 2 : ℝ)) (hwre : w.re = σ) (hzim : z.im = (-T' : ℝ)) (hwim : w.im = T')
    (hx : 0 < x) (hTT' : T ≤ T') (hT'0 : 0 < T') (hσ1 : 1 ≤ σ)
    (hsepT : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ.im ≠ T')
    (hsepT' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ.im ≠ -T') :
    (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ) - (∑ᶠ ρ : ℂ, zeroSummandR χ x z w ρ)
      = -(∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ) := by
  classical
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U :=
    fun U z _ => hΛdiff.analyticAt z
  have hstrip : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      0 < ρ.re ∧ ρ.re < 1 := fun ρ h => zerosInStrip χ hχ hχprim ρ h
  let R : ℝ := T' + 3
  let dR : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall 0 R) u
  have hdRfin : dR.support.Finite := by
    simpa only [dR] using
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R)
  let S : Finset ℂ := hdRfin.toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ dR u ≠ 0 := fun u => hdRfin.mem_toFinset
  have hS_zero : ∀ u ∈ S, DirichletCharacter.completedLFunction χ u = 0 := by
    intro u hu
    have hnorm : ‖u‖ ≤ R := by
      by_contra hcon
      exact (hS_mem u).mp hu (by
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem)))
    exact eq_zero_of_divisor_ne_zero (hΛan _)
      (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hnorm)) ((hS_mem u).mp hu)
  have hinS : ∀ ρ : ℂ, analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 →
      ‖ρ‖ ≤ R → ρ ∈ S := by
    intro ρ hρ hnorm
    refine (hS_mem ρ).mpr ?_
    have h1 : dR ρ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℤ) := by
      dsimp only [dR]
      exact divisor_eq_analyticOrderNatAt (hΛan _)
        (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hnorm))
    rw [h1]
    exact_mod_cast hρ
  have hst : Function.support (zeroSummandT χ x T) ⊆ ↑S := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
      intro h0
      refine hρ ?_
      simp only [zeroSummandT, h0, Nat.cast_zero, zero_mul]
    have hind : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
      by_contra hcon
      refine hρ ?_
      simp only [zeroSummandT, if_neg hcon, mul_zero]
    exact hinS ρ hord (by
      have hs := hstrip ρ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      have h2 : |ρ.re| ≤ 1 := by rw [abs_of_pos hs.1]; exact le_of_lt hs.2
      have h3 : |ρ.im| ≤ T' := le_trans hind.2.2 hTT'
      dsimp only [R]; linarith only [hTT', hind, h1, h2])
  have hsr : Function.support (zeroSummandR χ x z w) ⊆ ↑S := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
      intro h0
      refine hρ ?_
      simp only [zeroSummandR, h0, Nat.cast_zero, zero_mul]
    have hind : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im := by
      by_contra hcon
      refine hρ ?_
      simp only [zeroSummandR, if_neg hcon, mul_zero]
    rw [hzre, hwre, hzim, hwim] at hind
    exact hinS ρ hord (by
      have hs := hstrip ρ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      have h2 : |ρ.re| ≤ 1 := by rw [abs_of_pos hs.1]; exact le_of_lt hs.2
      have h3 : |ρ.im| ≤ T' := by rw [abs_le]; exact ⟨by linarith only [hind.2.2.1, hind], le_of_lt hind.2.2.2⟩
      dsimp only [R]; linarith only [h1, h2, h3])
  have hsw : Function.support (zeroSummandW χ x T T') ⊆ ↑S := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
      intro h0
      refine hρ ?_
      simp only [zeroSummandW, h0, Nat.cast_zero, zero_mul]
    have hind : T < |ρ.im| ∧ |ρ.im| ≤ T' := by
      by_contra hcon
      refine hρ ?_
      simp only [zeroSummandW, if_neg hcon, mul_zero]
    exact hinS ρ hord (by
      have hs := hstrip ρ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      have h2 : |ρ.re| ≤ 1 := by rw [abs_of_pos hs.1]; exact le_of_lt hs.2
      dsimp only [R]; linarith only [hind.2, hind, hs, h1, h2])
  have hpoint : ∀ ρ ∈ S, zeroSummandT χ x T ρ - zeroSummandR χ x z w ρ
      = -(zeroSummandW χ x T T' ρ) := by
    intro ρ hρ
    have hΛ0 : DirichletCharacter.completedLFunction χ ρ = 0 := hS_zero ρ hρ
    have hs := hstrip ρ hΛ0
    have himT : ρ.im ≠ T' := hsepT ρ hΛ0
    have himT' : ρ.im ≠ -T' := hsepT' ρ hΛ0
    have habs : |ρ.im| ≠ T' := by
      intro h
      rcases (abs_eq (le_of_lt hT'0)).mp h with h1 | h1
      · exact himT h1
      · exact himT' h1
    have hft : zeroSummandT χ x T ρ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
        (if |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0) := by
      simp only [zeroSummandT]
      congr 1
      by_cases h : |ρ.im| ≤ T
      · rw [if_pos h, if_pos]
        exact ⟨hs.1, hs.2, h⟩
      · rw [if_neg h, if_neg]
        intro hcon
        exact h hcon.2.2
    have hfr : zeroSummandR χ x z w ρ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
        (if |ρ.im| < T' then (x : ℂ) ^ ρ / ρ else 0) := by
      simp only [zeroSummandR]
      rw [hzre, hwre, hzim, hwim]
      congr 1
      by_cases h : |ρ.im| < T'
      · rw [if_pos h, if_pos]
        exact ⟨by linarith only [hs.1, hs], by linarith only [hs.2, hσ1, hs], (abs_lt.mp h).1, (abs_lt.mp h).2⟩
      · rw [if_neg h, if_neg]
        intro hcon
        exact h (abs_lt.mpr hcon.2.2)
    have hfw : zeroSummandW χ x T T' ρ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
        (if T < |ρ.im| ∧ |ρ.im| ≤ T' then (x : ℂ) ^ ρ / ρ else 0) := by
      simp only [zeroSummandW]
    rw [hft, hfr, hfw]
    by_cases hcase : |ρ.im| ≤ T
    · have hlt : |ρ.im| < T' := lt_of_le_of_ne (le_trans hcase hTT') habs
      rw [if_pos hcase, if_pos hlt, if_neg (fun h => absurd h.1 (not_lt.mpr hcase))]
      ring
    · rw [not_le] at hcase
      rw [if_neg (not_le.mpr hcase)]
      by_cases hcase2 : |ρ.im| ≤ T'
      · have hlt : |ρ.im| < T' := lt_of_le_of_ne hcase2 habs
        rw [if_pos hlt, if_pos ⟨hcase, hcase2⟩]
        ring
      · rw [if_neg (not_lt.mpr (le_of_not_ge hcase2)), if_neg (fun h => hcase2 h.2)]
        ring
  have hft : (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ) =
      ∑ ρ ∈ S, zeroSummandT χ x T ρ :=
    finsum_eq_sum_of_support_subset _ hst
  have hfr : (∑ᶠ ρ : ℂ, zeroSummandR χ x z w ρ) =
      ∑ ρ ∈ S, zeroSummandR χ x z w ρ :=
    finsum_eq_sum_of_support_subset _ hsr
  have hfw : (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ) =
      ∑ ρ ∈ S, zeroSummandW χ x T T' ρ :=
    finsum_eq_sum_of_support_subset _ hsw
  rw [hft, hfr, hfw, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hpoint

/-- The residue contribution of the gamma factor at the rectangle. -/
noncomputable def gammaResidueValue {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ := by
  classical
  exact if χ.Even then (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2) - (Real.log x : ℂ)
    else (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (1 / 2 : ℂ) / 2)

lemma gammaResidueValue_even {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hE : χ.Even)
    (x : ℝ) :
    gammaResidueValue χ x =
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2) - (Real.log x : ℂ) := by
  rw [gammaResidueValue, if_pos hE]

lemma gammaResidueValue_odd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hO : χ.Odd)
    (x : ℝ) :
    gammaResidueValue χ x =
      (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (1 / 2 : ℂ) / 2) := by
  rw [gammaResidueValue, if_neg hO.not_even]

lemma norm_gammaResidueValue_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 1 ≤ x) : ‖gammaResidueValue χ x‖ ≤ 4 + Real.log x := by
  have h := gamma_const_bound
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases χ.even_or_odd with hE | hO
  · rw [gammaResidueValue_even χ hE x]
    calc ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2) - (Real.log x : ℂ)‖
        ≤ ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma 1 / 2)‖ + ‖(Real.log x : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 3 + Real.log x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
          linarith only [h.1, h]
      _ ≤ 4 + Real.log x := by linarith only []
  · rw [gammaResidueValue_odd χ hO x]
    linarith only [h.2, hlog, h]

lemma rectInt_logDeriv_gammaFactor_eq_value {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 0 < x) {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (explF (DirichletCharacter.gammaFactor χ) x) =
      2 * (Real.pi : ℂ) * Complex.I * gammaResidueValue χ x := by
  rcases χ.even_or_odd with hE | hO
  · rw [gammaResidueValue, if_pos hE]
    exact rectInt_logDeriv_gammaFactor_eq_even χ hE hx hzre hzim hz1 h0in
  · rw [gammaResidueValue, if_neg hO.not_even]
    exact rectInt_logDeriv_gammaFactor_eq_odd χ hO hx hzre hzim hz1 h0in

/-- The explicit-formula identity for the truncated Perron integral. -/
lemma perronIntegral_expansion {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {x T' : ℝ} (hx3 : 3 ≤ x) (hT'2 : 2 ≤ T')
    (hsepT : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ.im ≠ T')
    (hsepT' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ.im ≠ -T') :
    perronIntegral χ x T' =
      -(logDeriv (DirichletCharacter.completedLFunction χ) 0
          + (∑ᶠ ρ : ℂ, zeroSummandR χ x
              (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I)
              (((1 + 1 / Real.log x : ℝ) : ℂ) + (T' : ℂ) * Complex.I) ρ)
          - gammaResidueValue χ x)
        - (Complex.I / (2 * Real.pi)) *
            ((∫ y in (-1 / 2)..(1 + 1 / Real.log x), explF (DirichletCharacter.LFunction χ) x
                ((y : ℂ) - (T' : ℂ) * Complex.I))
              - (∫ y in (-1 / 2)..(1 + 1 / Real.log x), explF (DirichletCharacter.LFunction χ) x
                ((y : ℂ) + (T' : ℂ) * Complex.I)))
        - (1 / (2 * Real.pi)) *
            (∫ t in (-T')..T', explF (DirichletCharacter.LFunction χ) x
              (((-1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))) := by
  have hx0 : 0 < x := by linarith only [hx3]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith only [hx3])
  have hσ1 : 1 < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := div_pos one_pos hlogx
    linarith only [this]
  set z : ℂ := (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I) with hzdef
  set w : ℂ := (((1 + 1 / Real.log x : ℝ) : ℂ) + (T' : ℂ) * Complex.I) with hwdef
  have hzre : z.re = (-1 / 2 : ℝ) := by rw [hzdef]; simp
  have hzim : z.im = (-T' : ℝ) := by rw [hzdef]; simp
  have hwre : w.re = 1 + 1 / Real.log x := by rw [hwdef]; simp
  have hwim : w.im = T' := by rw [hwdef]; simp
  have hzre' : z.re < w.re := by rw [hzre, hwre]; linarith only [hσ1]
  have hzim' : z.im < w.im := by rw [hzim, hwim]; linarith only [hT'2]
  have h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hzre]; norm_num
    · rw [hwre]; linarith only [hσ1]
    · rw [hzim]; linarith only [hT'2]
    · rw [hwim]; linarith only [hT'2]
  have hstrip := zerosInStrip χ hχ hχprim
  have hins : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      z.re < ρ.re ∧ ρ.re < w.re := by
    intro ρ hρ
    have h := hstrip ρ hρ
    rw [hzre, hwre]
    exact ⟨by linarith only [h.1, hzre, h0in, h], by linarith only [h.2, hσ1, h]⟩
  have hnz : ∀ s ∈ rectBoundary z w, DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro s hs hzero
    have h := hstrip s hzero
    rcases hs with ⟨-, him | him⟩ | ⟨-, hre | hre⟩
    · exact hsepT' s hzero (by rw [hzim] at him; exact him)
    · exact hsepT s hzero (by rw [hwim] at him; exact him)
    · exact absurd h.1 (by rw [hzre] at hre; linarith only [hzre, h0in, h, hre])
    · exact absurd h.2 (by rw [hwre] at hre; linarith only [hσ1, h, hre])
  have hrepos : ∀ s ∈ rectBoundary z w, -(1 : ℝ) < s.re := by
    intro s hs
    have h1 : z.re ≤ s.re := by
      rcases hs with ⟨hre, -⟩ | ⟨-, hre | hre⟩
      · rw [Set.uIcc_of_le (le_of_lt hzre')] at hre; exact hre.1
      · exact le_of_eq hre.symm
      · rw [hre, hwre]; linarith only [hσ1, hzre, h0in]
    rw [hzre] at h1; linarith only [hzre, h0in, h1]
  have h0 : ∀ s ∈ rectBoundary z w, s ≠ 0 := by
    intro s hs h
    have hre0 : s.re = 0 := by rw [h]; simp
    have him0 : s.im = 0 := by rw [h]; simp
    rcases hs with ⟨-, him | him⟩ | ⟨-, hre | hre⟩
    · rw [hzim] at him; linarith only [him, him0, hT'2, hzre, h0in]
    · rw [hwim] at him; linarith only [him, him0, hT'2, hzre, h0in]
    · rw [hzre] at hre; linarith only [hre, hre0, hzre, h0in]
    · rw [hwre] at hre; linarith only [hre, hre0, hσ1, hzre, h0in]
  set AA : ℂ := logDeriv (DirichletCharacter.completedLFunction χ) 0
    + (∑ᶠ ρ : ℂ, zeroSummandR χ x z w ρ) - gammaResidueValue χ x with hAA
  set BB : ℂ := (∫ y in (-1 / 2)..(1 + 1 / Real.log x),
      explF (DirichletCharacter.LFunction χ) x ((y : ℂ) - (T' : ℂ) * Complex.I))
    - (∫ y in (-1 / 2)..(1 + 1 / Real.log x),
      explF (DirichletCharacter.LFunction χ) x ((y : ℂ) + (T' : ℂ) * Complex.I)) with hBB
  set CC : ℂ := ∫ t in (-T')..T', explF (DirichletCharacter.LFunction χ) x
      (((-1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) with hCC
  have hA := rectInt_logDeriv_completed_eq χ hχ hχprim hx0 hzre' hzim' h0in hins hnz
  have hsub := rectInt_logDeriv_L_eq_sub χ hχ hx0 hzre' hzim' h0 hrepos hnz
  have hγ := rectInt_logDeriv_gammaFactor_eq_value χ hx0 hzre' hzim'
    (by rw [hzre]; linarith only [hzre, h0in]) h0in
  have hedge := rectInt_eq_edges (σ := 1 + 1 / Real.log x) (T' := T')
    (f := explF (DirichletCharacter.LFunction χ) x)
  rw [← hzdef, ← hwdef] at hedge
  have hSR : (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
          ((x : ℂ) ^ ρ / ρ) else 0))
      = ∑ᶠ ρ : ℂ, zeroSummandR χ x z w ρ := by
    refine finsum_congr (fun ρ => ?_)
    by_cases h : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
    · simp only [zeroSummandR, if_pos h]
    · simp only [zeroSummandR, if_neg h, mul_zero]
  have hseg : vertSeg χ x (1 + 1 / Real.log x) T'
      = ∫ t in (-T')..T', explF (DirichletCharacter.LFunction χ) x
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    simp only [vertSeg, explF, mul_div_assoc]
  have hsubE : rectInt z w (explF (DirichletCharacter.LFunction χ) x)
      = rectInt z w (explF (DirichletCharacter.completedLFunction χ) x)
        - rectInt z w (explF (DirichletCharacter.gammaFactor χ) x) := hsub
  have hAE : rectInt z w (explF (DirichletCharacter.completedLFunction χ) x)
      = 2 * (Real.pi : ℂ) * Complex.I *
          (logDeriv (DirichletCharacter.completedLFunction χ) 0
            + (∑ᶠ ρ : ℂ, zeroSummandR χ x z w ρ)) := by
    rw [← hSR]
    exact hA
  have hγE : rectInt z w (explF (DirichletCharacter.gammaFactor χ) x)
      = 2 * (Real.pi : ℂ) * Complex.I * gammaResidueValue χ x := hγ
  have hcomb : BB + Complex.I * vertSeg χ x (1 + 1 / Real.log x) T' - Complex.I * CC
      = 2 * (Real.pi : ℂ) * Complex.I * AA := by
    rw [hBB, hCC, hAA, hseg, ← hedge]
    rw [hsubE, hAE, hγE]
    ring
  have hIv : Complex.I * vertSeg χ x (1 + 1 / Real.log x) T'
      = 2 * (Real.pi : ℂ) * Complex.I * AA - BB + Complex.I * CC := by
    linear_combination hcomb
  have hI2 : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have h2 : (-Complex.I) * (Complex.I * vertSeg χ x (1 + 1 / Real.log x) T')
      = vertSeg χ x (1 + 1 / Real.log x) T' := by rw [← mul_assoc, hI2, one_mul]
  have hv : vertSeg χ x (1 + 1 / Real.log x) T'
      = -Complex.I * (2 * (Real.pi : ℂ) * Complex.I * AA - BB + Complex.I * CC) := by
    have h3 := congrArg (fun u => -Complex.I * u) hIv
    rwa [h2] at h3
  rw [perronIntegral_eq_vertSeg χ hx3, hv]
  have hI3 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hkey : ∀ P Q R : ℂ, -Complex.I * (2 * (Real.pi : ℂ) * Complex.I * P - Q + Complex.I * R)
      = 2 * (Real.pi : ℂ) * P + Complex.I * Q + R := by
    intro P Q R
    linear_combination (-(2 * (Real.pi : ℂ) * P) - R) * hI3
  rw [hkey]
  rw [hAA, hBB, hCC]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := two_pi_ne_zero
  field_simp
  ring

/-- Vanishing of `L(·,χ)` propagates to the completed `L`-function. -/
lemma LVanish_eq_zero_of_completedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : s ≠ 0) (hsre : -(1 : ℝ) < s.re) :
    DirichletCharacter.LFunction χ s = 0 → DirichletCharacter.completedLFunction χ s = 0 := by
  intro h
  rw [completedL_eq_gammaFactor_mul_L χ hs hsre, h, mul_zero]

/-- The truncated explicit formula bound for `x ≥ 3`. -/
lemma explicit_formula_bound_large {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        + ∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ‖
        ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨CP, hCPpos, hCP⟩ := chebyshevPsiChi_truncatedPerron χ
  obtain ⟨cd, hcdpos, hcd⟩ := goodHeight_separated χ hχ hχprim
  obtain ⟨CW, hCWpos, hCW⟩ := zerosInWindow_weighted_bound χ hχ hχprim
  obtain ⟨Ch, hChpos, hCh⟩ := horizontalSegment_logDeriv_bound_le_one χ hχ hχprim
  obtain ⟨CL, hCLpos, hCL⟩ := leftEdge_logDeriv_bound χ hχ hχprim
  set KB : ℝ := Real.log (8 * (N : ℝ) / 3) + 2 with hKBdef
  set KC : ℝ := |Real.log cd| + 2 with hKCdef
  set K0 : ℝ := ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ with hK0def
  set Cbig : ℝ := CP + K0 + 5 + CW * 4 * (2 * KB + 2)
      + 2 * Real.exp 1 * Ch * (1 + KC) * KB ^ 2 + CL * KB ^ 2 + 1 with hCbigdef
  have hKB0 : 0 ≤ KB := by
    rw [hKBdef]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    have h1 : 0 ≤ Real.log (8 * (N : ℝ) / 3) := Real.log_nonneg (by linarith only [hN1])
    linarith only [h1]
  have hKC0 : 0 ≤ KC := by rw [hKCdef]; positivity
  have hK00 : 0 ≤ K0 := by rw [hK0def]; positivity
  have hCbigpos : 0 < Cbig := by
    rw [hCbigdef]
    have h1 : 0 ≤ CW * 4 * (2 * KB + 2) := by positivity
    have h2 : 0 ≤ 2 * Real.exp 1 * Ch * (1 + KC) * KB ^ 2 := by positivity
    have h3 : 0 ≤ CL * KB ^ 2 := by positivity
    linarith only [hCPpos, hK00, h1, h2, h3]
  refine ⟨Cbig, hCbigpos, ?_⟩
  intro x hx3 T hT2 hTx
  have hx0 : 0 < x := by linarith only [hx3]
  have hx1 : 1 ≤ x := by linarith only [hx3]
  set Φ : ℝ := x * (Real.log x) ^ 2 / T + Real.log x with hΦdef
  have hLx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith only [Real.exp_one_lt_d9, hx3]
  have hLx0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hLx1
  have hΦ1 : 1 ≤ Φ := by
    rw [hΦdef]
    have h : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
    linarith only [hLx1, h]
  have hΦpos : 0 < Φ := lt_of_lt_of_le zero_lt_one hΦ1
  have hΦLx : Real.log x ≤ Φ := by
    rw [hΦdef]
    have h : 0 ≤ x * (Real.log x) ^ 2 / T := by positivity
    linarith only [h]
  have hΦx : x * (Real.log x) ^ 2 / T ≤ Φ := by
    rw [hΦdef]
    have h : 0 ≤ Real.log x := hLx0.le
    linarith only [hLx1]
  have hσ1 : 1 ≤ 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := div_pos one_pos hLx0
    linarith only [this]
  have hσ2 : 1 + 1 / Real.log x ≤ 2 := by
    have : 1 / Real.log x ≤ 1 := by rw [div_le_one hLx0]; exact hLx1
    linarith only [this]
  have hσhalf : (-1 / 2 : ℝ) ≤ 1 + 1 / Real.log x := by linarith only [hσ1]
  have hTpos : 0 < T := by linarith only [hT2]
  obtain ⟨T', hT'T1, hT'T2, hsep1, hsep2⟩ := hcd T (by linarith only [hT2])
  have hT'0 : (0 : ℝ) < T' := by linarith only [hT2, hT'T1]
  have hT'2 : (2 : ℝ) ≤ T' := by linarith only [hT2, hT'T1]
  have hTT' : T ≤ T' := by linarith only [hT'T1]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
  set B : ℂ := (∫ y in (-1 / 2)..(1 + 1 / Real.log x), explF (DirichletCharacter.LFunction χ) x
      ((y : ℂ) - (T' : ℂ) * Complex.I)) with hBdef
  set C : ℂ := (∫ y in (-1 / 2)..(1 + 1 / Real.log x), explF (DirichletCharacter.LFunction χ) x
      ((y : ℂ) + (T' : ℂ) * Complex.I)) with hCdef
  set D : ℂ := (∫ t in (-T')..T', explF (DirichletCharacter.LFunction χ) x
      (((-1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))) with hDdef
  set LB : ℝ := Real.log ((N : ℝ) * (T' + 3)) with hLBdef
  have hLB1 : 1 ≤ LB := by
    rw [hLBdef, Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 5 := by linarith only [Real.exp_one_lt_d9]
    have : (5 : ℝ) ≤ (N : ℝ) * (T' + 3) := by nlinarith only [hN1, hT2, hT'T1]
    linarith only [he, this]
  have hLB0 : 0 < LB := lt_of_lt_of_le zero_lt_one hLB1
  set δ : ℝ := min 1 (cd / LB) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min one_pos (div_pos hcdpos hLB0)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδle : δ ≤ cd / LB := by rw [hδdef]; exact min_le_right _ _
  have hsepT : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ.im ≠ T' := by
    intro ρ hρ hc
    have h := hsep1 ρ hρ
    rw [hc, sub_self, abs_zero] at h
    exact absurd h (not_le.mpr (div_pos hcdpos hLB0))
  have hsepT' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ.im ≠ -T' := by
    intro ρ hρ hc
    have h := hsep2 ρ hρ
    rw [hc] at h
    simp only [neg_add_cancel, abs_zero] at h
    exact absurd h (not_le.mpr (div_pos hcdpos hLB0))
  have hsep_le : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - T'| :=
    fun ρ hρ => le_trans hδle (hsep1 ρ hρ)
  have hsep_le' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im + T'| :=
    fun ρ hρ => le_trans hδle (hsep2 ρ hρ)
  have hδlog : Real.log (1 / δ) ≤ KC * LB := by
    by_cases hle : cd / LB ≤ 1
    · have hδval : δ = cd / LB := by rw [hδdef]; exact min_eq_right hle
      have h1 : 1 / δ = LB / cd := by rw [hδval, one_div, inv_div]
      rw [h1, Real.log_div (ne_of_gt hLB0) (ne_of_gt hcdpos), hKCdef]
      have h2 : -Real.log cd ≤ |Real.log cd| := neg_le_abs _
      have h3 : |Real.log cd| ≤ |Real.log cd| * LB := by
        nlinarith only [abs_nonneg (Real.log cd), hLB1]
      have h4 : Real.log LB ≤ LB := by linarith only [Real.log_le_sub_one_of_pos hLB0, hLB0]
      linarith only [hLB1, h2, h3, h4]
    · have hδval : δ = 1 := by rw [hδdef]; exact min_eq_left (le_of_lt (not_le.mp hle))
      rw [hδval, one_div, inv_one, Real.log_one]
      have : 0 ≤ KC * LB := by rw [hKCdef]; nlinarith only [hLB1, abs_nonneg (Real.log cd), hKC0]
      linarith only [this]
  have hLBKB : LB ≤ KB * Real.log x := by
    have h42 : T' + 3 ≤ (8 / 3) * x := by linarith only [hx3, hTx, hT'T2]
    have hargle : (N : ℝ) * (T' + 3) ≤ (8 * (N : ℝ) / 3) * x := by
      have h := mul_le_mul_of_nonneg_left h42 (by linarith only [hN1] : (0 : ℝ) ≤ (N : ℝ))
      calc (N : ℝ) * (T' + 3) ≤ (N : ℝ) * ((8 / 3) * x) := h
        _ = (8 * (N : ℝ) / 3) * x := by ring
    have h1 : LB ≤ Real.log ((8 * (N : ℝ) / 3) * x) := by
      rw [hLBdef]
      exact Real.log_le_log (by positivity) hargle
    have h2 : Real.log ((8 * (N : ℝ) / 3) * x) =
        Real.log (8 * (N : ℝ) / 3) + Real.log x :=
      Real.log_mul (by positivity) (ne_of_gt hx0)
    rw [h2] at h1
    have h5 : 0 ≤ Real.log (8 * (N : ℝ) / 3) := Real.log_nonneg (by linarith only [hN1])
    have h4 : Real.log (8 * (N : ℝ) / 3) + Real.log x ≤
        (Real.log (8 * (N : ℝ) / 3) + 1) * Real.log x := by
      nlinarith [mul_nonneg h5 (by linarith : (0 : ℝ) ≤ Real.log x - 1)]
    have h6 : (Real.log (8 * (N : ℝ) / 3) + 1) * Real.log x ≤ KB * Real.log x := by
      apply mul_le_mul_of_nonneg_right _ hLx0.le
      rw [hKBdef]; linarith only []
    linarith only [hLx1, h1, h4]
  have hlogN : Real.log (N : ℝ) ≤ KB * Real.log x := by
    have h1 : Real.log (N : ℝ) ≤ Real.log (8 * (N : ℝ) / 3) :=
      Real.log_le_log (by linarith only [hN1]) (by linarith only [hN1])
    have h2 : Real.log (8 * (N : ℝ) / 3) ≤ KB := by rw [hKBdef]; linarith only []
    have h3 : KB ≤ KB * Real.log x := by
      have := mul_le_mul_of_nonneg_left hLx1 hKB0
      rwa [mul_one] at this
    linarith only [h1, h3]
  -- Perron error bound
  have hP1 : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - perronIntegral χ x T'‖ ≤ CP * Φ := by
    have h := hCP x hx3 T' hT'2
    have h2 : x * (Real.log x) ^ 2 / T' ≤ x * (Real.log x) ^ 2 / T :=
      div_le_div_of_nonneg_left (by positivity) hTpos hTT'
    have h3 : CP * (x * (Real.log x) ^ 2 / T' + Real.log x) ≤ CP * Φ := by
      apply mul_le_mul_of_nonneg_left _ hCPpos.le
      rw [hΦdef]
      linarith only [h2]
    exact h.trans h3
  -- integrability along the horizontal lines
  have hcontu : ContinuousOn (fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) + (T' : ℂ) * Complex.I)) (Set.uIcc (-1 / 2 : ℝ) 2) := by
    refine (continuousOn_logDeriv_L χ hχ).comp (by fun_prop) ?_
    intro y hy
    simp only [Set.mem_setOf_eq]
    intro hL0
    have hy1 : -(1 : ℝ) < y := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hy
      linarith only [hy.1, hy]
    have hs0 : ((y : ℂ) + (T' : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith only [him, hT'0, hT2, hT'T1]
    exact hsepT _ (LVanish_eq_zero_of_completedL χ hχ hs0 (by simpa using hy1) hL0) (by simp)
  have hcontl : ContinuousOn (fun y : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((y : ℂ) - (T' : ℂ) * Complex.I)) (Set.uIcc (-1 / 2 : ℝ) 2) := by
    refine (continuousOn_logDeriv_L χ hχ).comp (by fun_prop) ?_
    intro y hy
    simp only [Set.mem_setOf_eq]
    intro hL0
    have hy1 : -(1 : ℝ) < y := by
      rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hy
      linarith only [hy.1, hy]
    have hs0 : ((y : ℂ) - (T' : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith only [him, hT'0, hT2, hT'T1]
    exact hsepT' _ (LVanish_eq_zero_of_completedL χ hχ hs0 (by simpa using hy1) hL0) (by simp)
  obtain ⟨hChbU, hChbL⟩ := hCh T' hT'2 δ hδpos hδ1 hsep_le hsep_le'
  rw [← hLBdef] at hChbU hChbL
  have hChbU' := hChbU
  have hChbL' := hChbL
  have hlogδnn : (0:ℝ) ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδpos, one_mul]; exact hδ1)
  -- horizontal edge integrals
  have hB : ‖B‖ ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
    rw [hBdef]
    have h1 := norm_horizontal_explF_le_lower (χ := χ)
      (x := x) (σ := 1 + 1 / Real.log x) (T' := T') hχ hx0 hx1 hσhalf hσ2 hT'0 hcontl
    rw [rpow_one_add_inv_log (by linarith only [hx3] : 1 < x)] at h1
    have h2 : (Real.exp 1 * x / T') *
        (∫ y in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
          ((y : ℂ) - (T' : ℂ) * Complex.I)‖)
        ≤ (Real.exp 1 * x / T') * (Ch * LB * (LB + Real.log (1 / δ))) :=
      mul_le_mul_of_nonneg_left hChbL' (by positivity)
    have h3 : (Real.exp 1 * x / T') * (Ch * LB * (LB + Real.log (1 / δ)))
        = Real.exp 1 * (x / T') * Ch * (LB * (LB + Real.log (1 / δ))) := by ring
    have h4 : Real.exp 1 * (x / T') * Ch * (LB * (LB + Real.log (1 / δ)))
        ≤ Real.exp 1 * (x / T) * Ch * ((1 + KC) * LB * LB) := by
      have hL : LB * (LB + Real.log (1 / δ)) ≤ (1 + KC) * LB * LB := by
        have hh : LB + Real.log (1 / δ) ≤ (1 + KC) * LB := by
          rw [add_mul, one_mul]; linarith only [hδlog]
        have h2 := mul_le_mul_of_nonneg_left hh hLB0.le
        calc LB * (LB + Real.log (1 / δ)) ≤ LB * ((1 + KC) * LB) := h2
          _ = (1 + KC) * LB * LB := by ring
      have hQ : x / T' ≤ x / T := div_le_div_of_nonneg_left hx0.le hTpos hTT'
      have hA : Real.exp 1 * (x / T') ≤ Real.exp 1 * (x / T) :=
        mul_le_mul_of_nonneg_left hQ (Real.exp_pos 1).le
      exact mul_le_mul (mul_le_mul_of_nonneg_right hA hChpos.le) hL
        (mul_nonneg hLB0.le (add_nonneg hLB0.le hlogδnn)) (by positivity)
    have h5 : Real.exp 1 * (x / T) * Ch * ((1 + KC) * LB * LB)
        ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
      have hLsq : LB * LB ≤ KB ^ 2 * (Real.log x) ^ 2 := by
        nlinarith only [hLBKB, hLB0, hKB0, hLx0.le, hLB1]
      have h6 : Real.exp 1 * (x / T) * Ch * ((1 + KC) * LB * LB)
          = (Real.exp 1 * Ch * (1 + KC) * (x / T)) * (LB * LB) := by ring
      have h7 : Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T)
          = (Real.exp 1 * Ch * (1 + KC) * (x / T)) * (KB ^ 2 * (Real.log x) ^ 2) := by ring
      rw [h6, h7]
      exact mul_le_mul_of_nonneg_left hLsq (by positivity)
    exact h1.trans (h2.trans (h3.le.trans (h4.trans h5)))
  have hC : ‖C‖ ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
    rw [hCdef]
    have h1 := norm_horizontal_explF_le_upper (χ := χ)
      (x := x) (σ := 1 + 1 / Real.log x) (T' := T') hχ hx0 hx1 hσhalf hσ2 hT'0 hcontu
    rw [rpow_one_add_inv_log (by linarith only [hx3] : 1 < x)] at h1
    have h2 : (Real.exp 1 * x / T') *
        (∫ y in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
          ((y : ℂ) + (T' : ℂ) * Complex.I)‖)
        ≤ (Real.exp 1 * x / T') * (Ch * LB * (LB + Real.log (1 / δ))) :=
      mul_le_mul_of_nonneg_left hChbU' (by positivity)
    have h3 : (Real.exp 1 * x / T') * (Ch * LB * (LB + Real.log (1 / δ)))
        = Real.exp 1 * (x / T') * Ch * (LB * (LB + Real.log (1 / δ))) := by ring
    have h4 : Real.exp 1 * (x / T') * Ch * (LB * (LB + Real.log (1 / δ)))
        ≤ Real.exp 1 * (x / T) * Ch * ((1 + KC) * LB * LB) := by
      have hL : LB * (LB + Real.log (1 / δ)) ≤ (1 + KC) * LB * LB := by
        have hh : LB + Real.log (1 / δ) ≤ (1 + KC) * LB := by
          rw [add_mul, one_mul]; linarith only [hδlog]
        have h2 := mul_le_mul_of_nonneg_left hh hLB0.le
        calc LB * (LB + Real.log (1 / δ)) ≤ LB * ((1 + KC) * LB) := h2
          _ = (1 + KC) * LB * LB := by ring
      have hQ : x / T' ≤ x / T := div_le_div_of_nonneg_left hx0.le hTpos hTT'
      have hA : Real.exp 1 * (x / T') ≤ Real.exp 1 * (x / T) :=
        mul_le_mul_of_nonneg_left hQ (Real.exp_pos 1).le
      exact mul_le_mul (mul_le_mul_of_nonneg_right hA hChpos.le) hL
        (mul_nonneg hLB0.le (add_nonneg hLB0.le hlogδnn)) (by positivity)
    have h5 : Real.exp 1 * (x / T) * Ch * ((1 + KC) * LB * LB)
        ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
      have hLsq : LB * LB ≤ KB ^ 2 * (Real.log x) ^ 2 := by
        nlinarith only [hLBKB, hLB0, hKB0, hLx0.le, hLB1]
      have h6 : Real.exp 1 * (x / T) * Ch * ((1 + KC) * LB * LB)
          = (Real.exp 1 * Ch * (1 + KC) * (x / T)) * (LB * LB) := by ring
      have h7 : Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T)
          = (Real.exp 1 * Ch * (1 + KC) * (x / T)) * (KB ^ 2 * (Real.log x) ^ 2) := by ring
      rw [h6, h7]
      exact mul_le_mul_of_nonneg_left hLsq (by positivity)
    exact h1.trans (h2.trans (h3.le.trans (h4.trans h5)))
  -- left edge integral
  have helB : ‖D‖ ≤ CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
    rw [hDdef]
    have h1 := norm_leftEdge_explF_le (χ := χ) hχ hχprim hx0 hx1 hT'0.le
    have h2 := hCL T' hT'2
    rw [← hLBdef] at h2
    have hxhalf : x ^ (-(1 / 2) : ℝ) ≤ 1 := by
      have := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num : (-(1/2):ℝ) ≤ 0)
      simpa using this
    have h3 : x ^ (-(1 / 2) : ℝ) * (∫ t in (-T')..T', ‖logDeriv (DirichletCharacter.LFunction χ)
          (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
            ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖) ≤ 1 * (CL * LB ^ 2) := by
      refine mul_le_mul hxhalf h2 ?_ (by norm_num)
      exact intervalIntegral.integral_nonneg (by linarith only [hT2, hT'T1])
        (fun u _ => by positivity)
    have h4 : 1 * (CL * LB ^ 2) ≤ CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
      have hLsq : LB ^ 2 ≤ KB ^ 2 * (Real.log x) ^ 2 := by
        nlinarith only [hLBKB, hLB0, hKB0, hLx0.le, hLB1]
      have h5 : (Real.log x) ^ 2 ≤ x * (Real.log x) ^ 2 / T := by
        rw [le_div_iff₀ hTpos]
        nlinarith only [hLx0.le, hTx]
      have h6 : CL * LB ^ 2 ≤ CL * (KB ^ 2 * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hLsq hCLpos.le
      have h7 : CL * (KB ^ 2 * (Real.log x) ^ 2) ≤ CL * (KB ^ 2 * (x * (Real.log x) ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h5 (sq_nonneg KB)) hCLpos.le
      linarith only [h6, h7]
    exact h1.trans (h3.trans h4)
  -- windowed zero sum
  have hWb : ‖(∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)‖ ≤ CW * 4 * (2 * KB + 2) * Φ := by
    have h := hCW x (by linarith only [hx3]) T hT2 T' hTT'
    rw [← hLBdef] at h
    have h2 : T' - T + 2 ≤ 4 := by linarith only [hT'T2]
    have h3 : LB + Real.log (N : ℝ) + 2 ≤ (2 * KB + 2) * Real.log x := by
      linarith only [hLBKB, hlogN, hLx1]
    have h4 : CW * (x / T) * (T' - T + 2) * (LB + Real.log (N : ℝ) + 2)
        ≤ CW * (x / T) * 4 * ((2 * KB + 2) * Real.log x) := by
      have huv : (T' - T + 2) * (LB + Real.log (N : ℝ) + 2) ≤ 4 * ((2 * KB + 2) * Real.log x) :=
        mul_le_mul h2 h3 (by positivity) (by norm_num)
      calc CW * (x / T) * (T' - T + 2) * (LB + Real.log (N : ℝ) + 2)
          = (CW * (x / T)) * ((T' - T + 2) * (LB + Real.log (N : ℝ) + 2)) := by ring
        _ ≤ (CW * (x / T)) * (4 * ((2 * KB + 2) * Real.log x)) :=
              mul_le_mul_of_nonneg_left huv (by positivity)
        _ = CW * (x / T) * 4 * ((2 * KB + 2) * Real.log x) := by ring
    have h5 : CW * (x / T) * 4 * ((2 * KB + 2) * Real.log x)
        ≤ CW * 4 * (2 * KB + 2) * Φ := by
      have h6 : (x / T) * Real.log x ≤ x * (Real.log x) ^ 2 / T := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hTpos.le
        have hLsq : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith only [hLx1]
        exact mul_le_mul_of_nonneg_left hLsq hx0.le
      have h7 : (x / T) * Real.log x ≤ x * (Real.log x) ^ 2 / T := h6
      have h9 : (0:ℝ) ≤ 2 * KB + 2 := by linarith only [hKB0]
      have h8 : (0:ℝ) ≤ CW * 4 * (2 * KB + 2) := by positivity
      calc CW * (x / T) * 4 * ((2 * KB + 2) * Real.log x)
          = CW * 4 * (2 * KB + 2) * ((x / T) * Real.log x) := by ring
        _ ≤ CW * 4 * (2 * KB + 2) * (x * (Real.log x) ^ 2 / T) :=
              mul_le_mul_of_nonneg_left h7 h8
        _ ≤ CW * 4 * (2 * KB + 2) * Φ := by
              apply mul_le_mul_of_nonneg_left _ h8
              rw [hΦdef]; linarith only [hLx1]
    exact h.trans (h4.trans h5)
  -- final combination
  have hexp := perronIntegral_expansion χ hχ hχprim hx3 hT'2 hsepT hsepT'
  rw [← hBdef, ← hCdef, ← hDdef] at hexp
  have hdiff := zeroSum_diff (χ := χ) hχ hχprim (σ := 1 + 1 / Real.log x)
      (z := (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I))
      (w := (((1 + 1 / Real.log x : ℝ) : ℂ) + (T' : ℂ) * Complex.I))
      (by simp) (by simp) (by simp) (by simp) hx0 hTT' hT'0 hσ1 hsepT hsepT'
  have hid : perronIntegral χ x T' + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)
      = -logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x
        - (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)
        - (Complex.I / (2 * Real.pi)) * (B - C) - (1 / (2 * Real.pi)) * D := by
    rw [hexp]
    have h1 : (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)
        = (∑ᶠ ρ : ℂ, zeroSummandR χ x (((-1 / 2 : ℝ) : ℂ) - (T' : ℂ) * Complex.I)
            (((1 + 1 / Real.log x : ℝ) : ℂ) + (T' : ℂ) * Complex.I) ρ)
          + (-(∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)) := by
      rw [← hdiff]; ring
    rw [h1]; ring
  have h2pi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = (2 : ℂ) * (Real.pi : ℂ) by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [show ‖(2 : ℂ)‖ = 2 by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs]
      norm_num]
  have hnormI : ‖Complex.I / (2 * Real.pi)‖ ≤ 1 := by
    rw [norm_div, show ‖Complex.I‖ = 1 by simp, one_div, inv_le_one₀]
    · rw [h2pi]; linarith only [Real.pi_gt_three]
    · rw [h2pi]; positivity
  have hnorm1 : ‖(1 : ℂ) / (2 * Real.pi)‖ ≤ 1 := by
    rw [norm_div, norm_one, one_div, inv_le_one₀]
    · rw [h2pi]; linarith only [Real.pi_gt_three]
    · rw [h2pi]; positivity
  have hM : (0:ℝ) ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by positivity
  have hM' : (0:ℝ) ≤ CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by positivity
  have hX : ‖-(Complex.I / (2 * Real.pi)) * (B - C)‖
      ≤ 2 * (Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T)) := by
    rw [norm_mul, norm_neg]
    have h1 : ‖Complex.I / (2 * Real.pi)‖ * ‖B - C‖ ≤ 1 * (‖B‖ + ‖C‖) :=
      mul_le_mul hnormI (norm_sub_le B C) (norm_nonneg _) (by norm_num)
    have h2 : ‖B‖ + ‖C‖
        ≤ 2 * (Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T)) := by
      linarith only [hB, hC]
    linarith only [h1, h2, hB, hC]
  have hY : ‖-(1 / (2 * Real.pi)) * D‖ ≤ CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
    rw [norm_mul, norm_neg]
    have h1 : ‖(1 : ℂ) / (2 * Real.pi)‖ * ‖D‖ ≤ 1 * ‖D‖ :=
      mul_le_mul_of_nonneg_right hnorm1 (norm_nonneg D)
    linarith only [h1, helB]
  have hA : ‖-logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x
        - (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)‖
      ≤ K0 + (4 + Real.log x) + CW * 4 * (2 * KB + 2) * Φ := by
    have h1 : ‖-logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x
          - (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)‖
        ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ + ‖gammaResidueValue χ x‖
          + ‖∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ‖ := by
      have e : -logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x
          - (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)
          = (-logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x)
            + (-(∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)) := by ring
      rw [e]
      calc ‖(-logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x)
              + (-(∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ))‖
          ≤ ‖-logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x‖
              + ‖-(∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)‖ := norm_add_le _ _
        _ ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ + ‖gammaResidueValue χ x‖
              + ‖∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ‖ := by
              rw [norm_neg]
              refine add_le_add ?_ le_rfl
              have hh := norm_add_le (-(logDeriv (DirichletCharacter.completedLFunction χ) 0))
                (gammaResidueValue χ x)
              rwa [norm_neg] at hh
    have h4 : ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ = K0 := hK0def.symm
    linarith [h1, norm_gammaResidueValue_le χ hx1, h4, hWb]
  have hper : ‖perronIntegral χ x T' + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)‖
      ≤ K0 + (4 + Real.log x) + CW * 4 * (2 * KB + 2) * Φ
        + 2 * (Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T))
        + CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T) := by
    have e : -logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x
          - (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ)
          - (Complex.I / (2 * Real.pi)) * (B - C) - (1 / (2 * Real.pi)) * D
        = ((-logDeriv (DirichletCharacter.completedLFunction χ) 0 + gammaResidueValue χ x
              - (∑ᶠ ρ : ℂ, zeroSummandW χ x T T' ρ))
            + (-(Complex.I / (2 * Real.pi)) * (B - C))) + (-(1 / (2 * Real.pi)) * D) := by ring
    rw [hid, e]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ?_ hY
    exact (norm_add_le _ _).trans (add_le_add hA hX)
  have hPsi : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)
      = ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - perronIntegral χ x T')
        + (perronIntegral χ x T' + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)) := by ring
  have hmid : CP * Φ + (K0 + (4 + Real.log x) + CW * 4 * (2 * KB + 2) * Φ
        + 2 * (Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T))
        + CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T))
      ≤ Cbig * Φ := by
    rw [hCbigdef]
    have h1 : K0 ≤ K0 * Φ := le_mul_of_one_le_right hK00 hΦ1
    have h2 : 4 + Real.log x ≤ 5 * Φ := by linarith only [hΦLx, hΦ1]
    have h3 : Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T)
        ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * Φ :=
      mul_le_mul_of_nonneg_left hΦx (by positivity)
    have h5 : CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T) ≤ CL * KB ^ 2 * Φ :=
      mul_le_mul_of_nonneg_left hΦx (by positivity)
    have h3' : 2 * (Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T))
        ≤ 2 * Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * Φ := by
      have hh : (0:ℝ) ≤ Real.exp 1 * Ch * (1 + KC) * KB ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hΦx hh
      linarith only [this, h3]
    have h6 : (CP + K0 + 5 + CW * 4 * (2 * KB + 2) + 2 * Real.exp 1 * Ch * (1 + KC) * KB ^ 2
          + CL * KB ^ 2 + 1) * Φ
        = CP * Φ + K0 * Φ + 5 * Φ + CW * 4 * (2 * KB + 2) * Φ
          + 2 * Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * Φ + CL * KB ^ 2 * Φ + Φ := by ring
    rw [h6]
    linarith only [h1, h2, h3', h5, hΦpos, hΦ1, hΦLx, h3]
  rw [hPsi]
  calc ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - perronIntegral χ x T')
          + (perronIntegral χ x T' + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - perronIntegral χ x T'‖
        + ‖perronIntegral χ x T' + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)‖ := norm_add_le _ _
    _ ≤ CP * Φ + (K0 + (4 + Real.log x) + CW * 4 * (2 * KB + 2) * Φ
          + 2 * (Real.exp 1 * Ch * (1 + KC) * KB ^ 2 * (x * (Real.log x) ^ 2 / T))
          + CL * KB ^ 2 * (x * (Real.log x) ^ 2 / T)) := add_le_add hP1 hper
    _ ≤ Cbig * Φ := hmid

/-- **Truncated explicit formula for `psi(x,chi)` with zeros counted with multiplicity.**

Standard (unconditionally provable) form of the explicit formula for
`psi(x,chi) = sum_{n <= x} chi(n) Lambda(n)`: the sum over the non-trivial zeros must be
weighted by the vanishing order `analyticOrderNatAt (completedLFunction chi) rho`, because the
residue of `-(L'/L)(s) x^s/s` at a zero of order `m` is `-m x^rho/rho`.  The unweighted
(finsum over the set of zeros) version is strictly stronger and is *not* a theorem: it forces
`sum_{|Im rho| <= T} (m(rho)-1) x^{Re rho}/|rho|` to be small, i.e. it implies that all zeros of
`L(.,chi)` in the critical strip are simple, which is a famous open problem. -/
theorem chebyshevPsiChi_explicit_formula_mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (T : ℝ), 2 ≤ T → T ≤ x →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        + ∑ᶠ (ρ : ℂ), (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) *
            (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖
        ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨Cbig, hCbigpos, hCbig⟩ := explicit_formula_bound_large χ hχ hχprim
  obtain ⟨K, hKpos, hK⟩ := completedL_zeroSum_small_window_bound χ hχ hχprim
  refine ⟨max Cbig (4 * (2 + K) + 1), lt_max_of_lt_left hCbigpos, ?_⟩
  intro x hx2 T hT2 hTx
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log x := by
    have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
    linarith only [Real.log_two_gt_d9, h]
  have hFx : (1 / 4 : ℝ) ≤ x * (Real.log x) ^ 2 / T := by
    have hTpos : 0 < T := by linarith only [hT2]
    have hXT : 1 ≤ x / T := by rw [le_div_iff₀ hTpos, one_mul]; exact hTx
    have hsq : (1 / 4 : ℝ) ≤ (Real.log x) ^ 2 := by nlinarith only [hlog2]
    have h1 : x * (Real.log x) ^ 2 / T = (x / T) * (Real.log x) ^ 2 := by ring
    rw [h1]
    exact le_trans (by norm_num) (mul_le_mul hXT hsq (by norm_num) (by positivity))
  by_cases hx3 : 3 ≤ x
  · have h := hCbig x hx3 T hT2 hTx
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hx3' : x ≤ 3 := le_of_lt (not_le.mp hx3)
    have hx3lt : x < 3 := not_le.mp hx3
    have h1 : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ ≤ 2 := by
      have hfloor : ⌊x⌋₊ ≤ 2 := by
        have h : ⌊x⌋₊ < 3 := (Nat.floor_lt (show (0 : ℝ) ≤ x by linarith only [hx2])).mpr hx3lt
        omega
      have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 2 := by
        intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        exact ⟨hn.1, le_trans hn.2 hfloor⟩
      have hIcc : (∑ n ∈ Finset.Icc 1 2, (ArithmeticFunction.vonMangoldt n : ℝ)) = Real.log 2 := by
        rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from by decide]
        rw [Finset.sum_insert (by norm_num), Finset.sum_singleton,
          ArithmeticFunction.vonMangoldt_apply_one,
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      have hlog2' : Real.log 2 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith only [this]
      have hsum : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)) ≤ 2 :=
        ((Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans (le_of_eq hIcc)).trans hlog2'
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => ?_)).trans hsum)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc ‖χ ((n : ℕ) : ZMod N)‖ * ArithmeticFunction.vonMangoldt n
          ≤ 1 * ArithmeticFunction.vonMangoldt n :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _)
              ArithmeticFunction.vonMangoldt_nonneg
        _ = ArithmeticFunction.vonMangoldt n := one_mul _
    have h2 : ‖(∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)‖ ≤ K := hK x hx2 hx3' T hT2 hTx
    have h3 : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ ((n : ℕ) : ZMod N) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) + (∑ᶠ ρ : ℂ, zeroSummandT χ x T ρ)‖
        ≤ 2 + K := (norm_add_le _ _).trans (add_le_add h1 h2)
    have hΦ' : (3 / 4 : ℝ) ≤ x * (Real.log x) ^ 2 / T + Real.log x := by linarith only [hlog2, hFx]
    have hCge : 4 * (2 + K) + 1 ≤ max Cbig (4 * (2 + K) + 1) := le_max_right _ _
    have hC0 : (0:ℝ) ≤ max Cbig (4 * (2 + K) + 1) := le_trans (by positivity) hCge
    refine h3.trans ?_
    calc (2 + K) ≤ (4 * (2 + K) + 1) * (3 / 4) := by linarith only [hKpos]
      _ ≤ max Cbig (4 * (2 + K) + 1) * (x * (Real.log x) ^ 2 / T + Real.log x) :=
            mul_le_mul hCge hΦ' (by norm_num) hC0


end

end Commons.NumberTheory.DirichletCharacter
