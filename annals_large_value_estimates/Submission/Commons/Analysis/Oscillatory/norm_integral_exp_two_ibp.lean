import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Oscillatory.first_derivative_test_ibp

namespace Commons.Analysis.Oscillatory

open MeasureTheory Real Complex
open scoped Real Interval Topology

/-! ## Auxiliary calculus lemmas -/

private lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private lemma iteratedDeriv_three_eq (f : ℝ → ℝ) :
    iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_two_eq]

private lemma hasDerivAt_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x := by
  have hd : Differentiable ℝ (deriv f) := by
    have h := hf.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  exact (hd x).hasDerivAt

private lemma hasDerivAt_deriv_deriv_of_contDiff_three {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (x : ℝ) : HasDerivAt (deriv (deriv f)) (iteratedDeriv 3 f x) x := by
  have hd : Differentiable ℝ (deriv (deriv f)) := by
    have h := hf.differentiable_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_two_eq] at h
  have h1 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := (hd x).hasDerivAt
  rwa [← iteratedDeriv_three_eq] at h1

private lemma continuous_deriv_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (deriv f)) := by
  have h := hf.continuous_iteratedDeriv 2 (by norm_num)
  rwa [iteratedDeriv_two_eq] at h

private lemma continuous_deriv_deriv_of_contDiff_three {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    Continuous (deriv (deriv f)) := by
  have h := hf.continuous_iteratedDeriv 2 (by norm_num)
  rwa [iteratedDeriv_two_eq] at h

/-- The real weight `g'/Φ'² - g·Φ''/Φ'³` obtained after one integration by parts. -/
private noncomputable def twoIbpWeightR (Φ g : ℝ → ℝ) : ℝ → ℝ :=
  fun y => deriv g y / (deriv Φ y) ^ 2 - g y * deriv (deriv Φ) y / (deriv Φ y) ^ 3

/-- Its derivative. -/
private noncomputable def twoIbpWeightRDeriv (Φ g : ℝ → ℝ) : ℝ → ℝ :=
  fun y => deriv (deriv g) y / (deriv Φ y) ^ 2
    - 3 * deriv g y * deriv (deriv Φ) y / (deriv Φ y) ^ 3
    - g y * iteratedDeriv 3 Φ y / (deriv Φ y) ^ 3
    + 3 * g y * (deriv (deriv Φ) y) ^ 2 / (deriv Φ y) ^ 4

private lemma twoIbpWeightR_hasDerivAt {Φ g : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ)
    (hg : ContDiff ℝ 2 g) {x : ℝ} (hx : deriv Φ x ≠ 0) :
    HasDerivAt (twoIbpWeightR Φ g) (twoIbpWeightRDeriv Φ g x) x := by
  have hgd : HasDerivAt (deriv g) (deriv (deriv g) x) x := hasDerivAt_deriv_of_contDiff_two hg x
  have hpdd : HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x :=
    hasDerivAt_deriv_of_contDiff_two (hΦ.of_le (by norm_num)) x
  have hpddd : HasDerivAt (deriv (deriv Φ)) (iteratedDeriv 3 Φ x) x :=
    hasDerivAt_deriv_deriv_of_contDiff_three hΦ x
  have hg' : HasDerivAt g (deriv g x) x := (hg.differentiable (by norm_num) x).hasDerivAt
  have hterm1 : HasDerivAt (fun y => deriv g y / (deriv Φ y) ^ 2)
      ((deriv (deriv g) x * (deriv Φ x) ^ 2
        - deriv g x * (2 * deriv Φ x ^ (2 - 1) * deriv (deriv Φ) x)) / ((deriv Φ x) ^ 2) ^ 2) x :=
    hgd.div (hpdd.pow 2) (pow_ne_zero 2 hx)
  have hnum : HasDerivAt (fun y => g y * deriv (deriv Φ) y)
      (deriv g x * deriv (deriv Φ) x + g x * iteratedDeriv 3 Φ x) x :=
    hg'.mul hpddd
  have hterm2 : HasDerivAt (fun y => g y * deriv (deriv Φ) y / (deriv Φ y) ^ 3)
      (((deriv g x * deriv (deriv Φ) x + g x * iteratedDeriv 3 Φ x) * (deriv Φ x) ^ 3
        - (g x * deriv (deriv Φ) x) * (3 * deriv Φ x ^ (3 - 1) * deriv (deriv Φ) x))
        / ((deriv Φ x) ^ 3) ^ 2) x :=
    hnum.div (hpdd.pow 3) (pow_ne_zero 3 hx)
  have h := hterm1.sub hterm2
  have hgoal : (deriv (deriv g) x * (deriv Φ x) ^ 2
        - deriv g x * (2 * deriv Φ x ^ (2 - 1) * deriv (deriv Φ) x)) / ((deriv Φ x) ^ 2) ^ 2
      - ((deriv g x * deriv (deriv Φ) x + g x * iteratedDeriv 3 Φ x) * (deriv Φ x) ^ 3
        - (g x * deriv (deriv Φ) x) * (3 * deriv Φ x ^ (3 - 1) * deriv (deriv Φ) x))
        / ((deriv Φ x) ^ 3) ^ 2
      = twoIbpWeightRDeriv Φ g x := by
    rw [twoIbpWeightRDeriv]
    field_simp
    ring
  exact h.congr_deriv hgoal

private lemma twoIbpWeightR_cont {Φ g : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (hg : ContDiff ℝ 2 g)
    {a b : ℝ} (hpd : ∀ x ∈ Set.Icc a b, deriv Φ x ≠ 0) :
    ContinuousOn (twoIbpWeightR Φ g) (Set.Icc a b) := by
  have hpdc : Continuous (deriv Φ) := hΦ.continuous_deriv (by norm_num)
  have hpddc : Continuous (deriv (deriv Φ)) := continuous_deriv_deriv_of_contDiff_three hΦ
  have hgdc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hgc : Continuous g := hg.continuous
  unfold twoIbpWeightR
  refine ContinuousOn.sub ?_ ?_
  · exact ContinuousOn.div hgdc.continuousOn ((hpdc.continuousOn).pow 2)
      (fun x hx => pow_ne_zero 2 (hpd x hx))
  · exact ContinuousOn.div ((hgc.continuousOn).mul hpddc.continuousOn) ((hpdc.continuousOn).pow 3)
      (fun x hx => pow_ne_zero 3 (hpd x hx))

private lemma twoIbpWeightRDeriv_cont {Φ g : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (hg : ContDiff ℝ 2 g)
    {a b : ℝ} (hpd : ∀ x ∈ Set.Icc a b, deriv Φ x ≠ 0) :
    ContinuousOn (twoIbpWeightRDeriv Φ g) (Set.Icc a b) := by
  have hpdc : Continuous (deriv Φ) := hΦ.continuous_deriv (by norm_num)
  have hpddc : Continuous (deriv (deriv Φ)) := continuous_deriv_deriv_of_contDiff_three hΦ
  have hpdddc : Continuous (iteratedDeriv 3 Φ) := hΦ.continuous_iteratedDeriv 3 (by norm_num)
  have hgdc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hgddc : Continuous (deriv (deriv g)) := continuous_deriv_deriv_of_contDiff_two hg
  have hgc : Continuous g := hg.continuous
  unfold twoIbpWeightRDeriv
  refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.sub ?_ ?_) ?_) ?_
  · exact ContinuousOn.div hgddc.continuousOn ((hpdc.continuousOn).pow 2)
      (fun x hx => pow_ne_zero 2 (hpd x hx))
  · exact ContinuousOn.div ((continuousOn_const.mul hgdc.continuousOn).mul hpddc.continuousOn)
      ((hpdc.continuousOn).pow 3) (fun x hx => pow_ne_zero 3 (hpd x hx))
  · exact ContinuousOn.div (hgc.continuousOn.mul hpdddc.continuousOn) ((hpdc.continuousOn).pow 3)
      (fun x hx => pow_ne_zero 3 (hpd x hx))
  · exact ContinuousOn.div ((continuousOn_const.mul hgc.continuousOn).mul (hpddc.continuousOn.pow 2))
      ((hpdc.continuousOn).pow 4) (fun x hx => pow_ne_zero 4 (hpd x hx))


/-- Elementary arithmetic comparison for the two-fold integration-by-parts bound. -/
private lemma two_ibp_arith_bound {m M M3 A B C : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hM3 : 0 ≤ M3)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (m ^ 2)⁻¹ * A + (3 * M / m ^ 3) * B + (M3 / m ^ 3) * C + (3 * M ^ 2 / m ^ 4) * C
      ≤ 8 * (A + B * M / m + C * M3 / m + C * M ^ 2 / m ^ 2) / m ^ 2 := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hm3 : (0 : ℝ) < m ^ 3 := by positivity
  have hm4 : (0 : ℝ) < m ^ 4 := by positivity
  have h1 : (m ^ 2)⁻¹ * A ≤ 8 * A / m ^ 2 := by
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hm2)
  have h2 : (3 * M / m ^ 3) * B ≤ (8 * M / m ^ 3) * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hm3)
  have h3 : (M3 / m ^ 3) * C ≤ (8 * M3 / m ^ 3) * C := by
    apply mul_le_mul_of_nonneg_right _ hC
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hm3)
  have h4 : (3 * M ^ 2 / m ^ 4) * C ≤ (8 * M ^ 2 / m ^ 4) * C := by
    apply mul_le_mul_of_nonneg_right _ hC
    exact div_le_div_of_nonneg_right (by nlinarith) (le_of_lt hm4)
  have hEq : 8 * (A + B * M / m + C * M3 / m + C * M ^ 2 / m ^ 2) / m ^ 2
      = 8 * A / m ^ 2 + (8 * M / m ^ 3) * B + (8 * M3 / m ^ 3) * C
        + (8 * M ^ 2 / m ^ 4) * C := by
    field_simp
  rw [hEq]
  linarith

/-- The complex weight obtained after one integration by parts. -/
private noncomputable def twoIbpWeightC (Φ g : ℝ → ℝ) : ℝ → ℂ :=
  fun y => ((twoIbpWeightR Φ g y : ℝ) : ℂ)

/-- Its derivative. -/
private noncomputable def twoIbpWeightCDeriv (Φ g : ℝ → ℝ) : ℝ → ℂ :=
  fun y => ((twoIbpWeightRDeriv Φ g y : ℝ) : ℂ)

private lemma twoIbpWeightC_hasDerivAt {Φ g : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ)
    (hg : ContDiff ℝ 2 g) {x : ℝ} (hx : deriv Φ x ≠ 0) :
    HasDerivAt (twoIbpWeightC Φ g) (twoIbpWeightCDeriv Φ g x) x := by
  exact (twoIbpWeightR_hasDerivAt hΦ hg hx).ofReal_comp

private lemma twoIbpWeightC_cont {Φ g : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (hg : ContDiff ℝ 2 g)
    {a b : ℝ} (hpd : ∀ x ∈ Set.Icc a b, deriv Φ x ≠ 0) :
    ContinuousOn (twoIbpWeightC Φ g) (Set.Icc a b) :=
  Complex.continuous_ofReal.comp_continuousOn (twoIbpWeightR_cont hΦ hg hpd)

private lemma twoIbpWeightCDeriv_cont {Φ g : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (hg : ContDiff ℝ 2 g)
    {a b : ℝ} (hpd : ∀ x ∈ Set.Icc a b, deriv Φ x ≠ 0) :
    ContinuousOn (twoIbpWeightCDeriv Φ g) (Set.Icc a b) :=
  Complex.continuous_ofReal.comp_continuousOn (twoIbpWeightRDeriv_cont hΦ hg hpd)

/-- Pointwise identity: the weight times `I·Φ'` is the amplitude of the once-integrated
oscillatory integral. -/
private lemma twoIbpWeightC_mul {Φ g : ℝ → ℝ} {x : ℝ} (hx : deriv Φ x ≠ 0) :
    twoIbpWeightC Φ g x * (Complex.I * ((deriv Φ x : ℝ) : ℂ))
      = Complex.I * (((deriv g x / deriv Φ x
          - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ) := by
  have hxc : ((deriv Φ x : ℝ) : ℂ) ≠ 0 := by
    simpa using hx
  unfold twoIbpWeightC twoIbpWeightR
  push_cast
  field_simp

/-- Single integration by parts with the weight `g/Φ'`. -/
private lemma integral_ibp_exp_div_deriv {a b : ℝ} (hab : a ≤ b) {Φ g : ℝ → ℝ}
    (hΦ : ContDiff ℝ 3 Φ) (hg : ContDiff ℝ 2 g)
    (hpd : ∀ x ∈ Set.Icc a b, deriv Φ x ≠ 0) (ha : g a = 0) (hb : g b = 0) :
    ∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))
      = Complex.I * ∫ x in a..b,
          (((deriv g x / deriv Φ x - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
            * Complex.exp (Complex.I * (Φ x : ℂ)) := by
  have hpdc : Continuous (deriv Φ) := hΦ.continuous_deriv (by norm_num)
  have hpddc : Continuous (deriv (deriv Φ)) := continuous_deriv_deriv_of_contDiff_three hΦ
  have hgdc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hpd' : ∀ x ∈ Set.uIcc a b, deriv Φ x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hpd x hx
  have hu_cont : ContinuousOn (fun y : ℝ => ((g y / deriv Φ y : ℝ) : ℂ)) (Set.uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.div hgc.continuousOn hpdc.continuousOn hpd')
  have hv_cont : ContinuousOn (fun y : ℝ => Complex.exp (Complex.I * (Φ y : ℂ))) (Set.uIcc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦ.continuous.continuousOn))
  have hu_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun y : ℝ => ((g y / deriv Φ y : ℝ) : ℂ))
        (((deriv g x / deriv Φ x - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hxne : deriv Φ x ≠ 0 := hpd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have h1 : HasDerivAt g (deriv g x) x := (hg.differentiable (by norm_num) x).hasDerivAt
    have h2 : HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x :=
      hasDerivAt_deriv_of_contDiff_two (hΦ.of_le (by norm_num)) x
    have h3 := h1.div h2 hxne
    have h4 := h3.ofReal_comp
    refine h4.congr_deriv ?_
    push_cast
    field_simp
  have hv_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (Φ y : ℂ)))
        (Complex.I * ((deriv Φ x : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt Φ (deriv Φ x) x := (hΦ.differentiable (by norm_num) x).hasDerivAt
    have h4 := ((h1.ofReal_comp).const_mul Complex.I).cexp
    refine h4.congr_deriv ?_
    ring
  have hu_int : IntervalIntegrable
      (fun y : ℝ => (((deriv g y / deriv Φ y - g y * deriv (deriv Φ) y / (deriv Φ y) ^ 2 : ℝ)) : ℂ))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.sub (ContinuousOn.div hgdc.continuousOn hpdc.continuousOn ?_)
      (ContinuousOn.div (hgc.continuousOn.mul hpddc.continuousOn) ((hpdc.continuousOn).pow 2) ?_)
    · intro x hx; exact hpd x hx
    · intro x hx; exact pow_ne_zero 2 (hpd x hx)
  have hv_int : IntervalIntegrable
      (fun y : ℝ => Complex.I * ((deriv Φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ y : ℂ)))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
    · exact Complex.continuous_ofReal.comp_continuousOn hpdc.continuousOn
    · exact Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦ.continuous.continuousOn))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => ((g y / deriv Φ y : ℝ) : ℂ))
    (v := fun y : ℝ => Complex.exp (Complex.I * (Φ y : ℂ)))
    (u' := fun y : ℝ => (((deriv g y / deriv Φ y - g y * deriv (deriv Φ) y / (deriv Φ y) ^ 2 : ℝ)) : ℂ))
    (v' := fun y : ℝ => Complex.I * ((deriv Φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ y : ℂ)))
    hu_cont hv_cont hu_deriv hv_deriv hu_int hv_int
  have hL : (∫ x in a..b, ((g x / deriv Φ x : ℝ) : ℂ)
        * (Complex.I * ((deriv Φ x : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))))
      = Complex.I * ∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ)) := by
    rw [show Complex.I * ∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))
        = ∫ x in a..b, Complex.I * ((g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))) from
      (intervalIntegral.integral_const_mul Complex.I _).symm]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxne : deriv Φ x ≠ 0 := hpd x hx
    show ((g x / deriv Φ x : ℝ) : ℂ)
        * (Complex.I * ((deriv Φ x : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ)))
      = Complex.I * ((g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ)))
    have hxc : ((deriv Φ x : ℝ) : ℂ) ≠ 0 := by simpa using hxne
    push_cast
    field_simp
  have hbb : (fun y : ℝ => ((g y / deriv Φ y : ℝ) : ℂ)) b
      * (fun y : ℝ => Complex.exp (Complex.I * (Φ y : ℂ))) b = 0 := by
    show ((g b / deriv Φ b : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ b : ℂ)) = 0
    rw [hb]; simp
  have haa : (fun y : ℝ => ((g y / deriv Φ y : ℝ) : ℂ)) a
      * (fun y : ℝ => Complex.exp (Complex.I * (Φ y : ℂ))) a = 0 := by
    show ((g a / deriv Φ a : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ a : ℂ)) = 0
    rw [ha]; simp
  have key : Complex.I * ∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))
      = - ∫ x in a..b, (((deriv g x / deriv Φ x - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
          * Complex.exp (Complex.I * (Φ x : ℂ)) := by
    rw [← hL, hibp, hbb, haa]
    ring
  have h2' : Complex.I * (Complex.I * ∫ x in a..b,
        (((deriv g x / deriv Φ x - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
          * Complex.exp (Complex.I * (Φ x : ℂ)))
      = - ∫ x in a..b, (((deriv g x / deriv Φ x - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
          * Complex.exp (Complex.I * (Φ x : ℂ)) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  exact mul_left_cancel₀ Complex.I_ne_zero (by rw [key, h2'])

/-- Triangle-type bound for a four-term alternating sum. -/
private lemma abs_four_le (A B C D : ℝ) : |A - B - C + D| ≤ |A| + |B| + |C| + |D| := by
  have h1 : |A - B - C + D| ≤ |A - B - C| + |D| := abs_add_le _ _
  have h2 : |A - B - C| ≤ |A - B| + |C| := by simpa using abs_sub_le (A - B) 0 C
  have h3 : |A - B| ≤ |A| + |B| := by simpa using abs_sub_le A 0 B
  linarith

/-- Pointwise bound for the derivative of the integration-by-parts weight. -/
private lemma twoIbpWeightRDeriv_abs_le {a b m M M3 : ℝ} {Φ g : ℝ → ℝ} (hm : 0 < m)
    (hbd : ∀ x ∈ Set.Icc a b, m ≤ |deriv Φ x|)
    (h2 : ∀ x ∈ Set.Icc a b, |deriv (deriv Φ) x| ≤ M)
    (h3 : ∀ x ∈ Set.Icc a b, |iteratedDeriv 3 Φ x| ≤ M3)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |twoIbpWeightRDeriv Φ g x| ≤ (m ^ 2)⁻¹ * |deriv (deriv g) x| + (3 * M / m ^ 3) * |deriv g x|
      + (M3 / m ^ 3) * |g x| + (3 * M ^ 2 / m ^ 4) * |g x| := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (h2 x hx)
  have hM3 : 0 ≤ M3 := le_trans (abs_nonneg _) (h3 x hx)
  have hp : (0 : ℝ) < |deriv Φ x| := lt_of_lt_of_le hm (hbd x hx)
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hm3 : (0 : ℝ) < m ^ 3 := by positivity
  have hm4 : (0 : ℝ) < m ^ 4 := by positivity
  have hp2 : m ^ 2 ≤ |deriv Φ x| ^ 2 := pow_le_pow_left₀ (le_of_lt hm) (hbd x hx) 2
  have hp3 : m ^ 3 ≤ |deriv Φ x| ^ 3 := pow_le_pow_left₀ (le_of_lt hm) (hbd x hx) 3
  have hp4 : m ^ 4 ≤ |deriv Φ x| ^ 4 := pow_le_pow_left₀ (le_of_lt hm) (hbd x hx) 4
  have hb1 : |deriv (deriv g) x / (deriv Φ x) ^ 2| ≤ |deriv (deriv g) x| / m ^ 2 := by
    rw [abs_div, abs_pow]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm2 hp2
  have hb2 : |3 * deriv g x * deriv (deriv Φ) x / (deriv Φ x) ^ 3| ≤ 3 * |deriv g x| * M / m ^ 3 := by
    have hkey : |deriv (deriv Φ) x| * m ^ 3 ≤ M * |deriv Φ x| ^ 3 :=
      mul_le_mul (h2 x hx) hp3 (le_of_lt hm3) hM
    have hgd0 : 0 ≤ 3 * |deriv g x| := by positivity
    rw [abs_div, abs_pow, abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 3 from by norm_num)]
    rw [div_le_div_iff₀ (by positivity) hm3]
    have hgoal1 : 3 * |deriv g x| * (|deriv (deriv Φ) x| * m ^ 3)
        ≤ 3 * |deriv g x| * (M * |deriv Φ x| ^ 3) :=
      mul_le_mul_of_nonneg_left hkey hgd0
    nlinarith [hgoal1]
  have hb3 : |g x * iteratedDeriv 3 Φ x / (deriv Φ x) ^ 3| ≤ |g x| * M3 / m ^ 3 := by
    have hkey : |iteratedDeriv 3 Φ x| * m ^ 3 ≤ M3 * |deriv Φ x| ^ 3 :=
      mul_le_mul (h3 x hx) hp3 (le_of_lt hm3) hM3
    have hg0 : 0 ≤ |g x| := abs_nonneg _
    rw [abs_div, abs_pow, abs_mul]
    rw [div_le_div_iff₀ (by positivity) hm3]
    have hgoal1 : |g x| * (|iteratedDeriv 3 Φ x| * m ^ 3) ≤ |g x| * (M3 * |deriv Φ x| ^ 3) :=
      mul_le_mul_of_nonneg_left hkey hg0
    nlinarith [hgoal1]
  have hb4 : |3 * g x * (deriv (deriv Φ) x) ^ 2 / (deriv Φ x) ^ 4| ≤ 3 * |g x| * M ^ 2 / m ^ 4 := by
    have h3' : |deriv (deriv Φ) x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h2 x hx) 2
    have hkey : |deriv (deriv Φ) x| ^ 2 * m ^ 4 ≤ M ^ 2 * |deriv Φ x| ^ 4 :=
      mul_le_mul h3' hp4 (le_of_lt hm4) (by positivity)
    have hgd0 : 0 ≤ 3 * |g x| := by positivity
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (show (0 : ℝ) < 3 from by norm_num)]
    rw [div_le_div_iff₀ (by positivity) hm4]
    have hgoal1 : 3 * |g x| * (|deriv (deriv Φ) x| ^ 2 * m ^ 4)
        ≤ 3 * |g x| * (M ^ 2 * |deriv Φ x| ^ 4) :=
      mul_le_mul_of_nonneg_left hkey hgd0
    nlinarith [hgoal1]
  unfold twoIbpWeightRDeriv
  have htri := abs_four_le (deriv (deriv g) x / (deriv Φ x) ^ 2)
    (3 * deriv g x * deriv (deriv Φ) x / (deriv Φ x) ^ 3)
    (g x * iteratedDeriv 3 Φ x / (deriv Φ x) ^ 3)
    (3 * g x * (deriv (deriv Φ) x) ^ 2 / (deriv Φ x) ^ 4)
  rw [inv_mul_eq_div,
    show (3 * M / m ^ 3) * |deriv g x| = 3 * |deriv g x| * M / m ^ 3 from by ring,
    show (M3 / m ^ 3) * |g x| = |g x| * M3 / m ^ 3 from by ring,
    show (3 * M ^ 2 / m ^ 4) * |g x| = 3 * |g x| * M ^ 2 / m ^ 4 from by ring]
  linarith [htri, hb1, hb2, hb3, hb4]


set_option linter.unusedVariables false in
theorem norm_integral_exp_two_ibp {a b m M M3 : ℝ} (hab : a ≤ b) (hm : 0 < m)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ)
    (hmono : MonotoneOn (deriv Φ) (Set.Icc a b) ∨ AntitoneOn (deriv Φ) (Set.Icc a b))
    (hbd : ∀ x ∈ Set.Icc a b, m ≤ |deriv Φ x|)
    (h2 : ∀ x ∈ Set.Icc a b, |deriv (deriv Φ) x| ≤ M)
    (h3 : ∀ x ∈ Set.Icc a b, |iteratedDeriv 3 Φ x| ≤ M3)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgs : ∀ x, x ∉ Set.Ioo a b → g x = 0) :
    ‖∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤
      8 * ((∫ x in a..b, |deriv (deriv g) x|)
          + (∫ x in a..b, |deriv g x|) * M / m
          + (∫ x in a..b, |g x|) * M3 / m
          + (∫ x in a..b, |g x|) * M ^ 2 / m ^ 2) / m ^ 2 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (h2 a ⟨le_rfl, hab⟩)
  have hM3 : 0 ≤ M3 := le_trans (abs_nonneg _) (h3 a ⟨le_rfl, hab⟩)
  have hpd : ∀ x ∈ Set.Icc a b, deriv Φ x ≠ 0 := fun x hx =>
    abs_pos.mp (lt_of_lt_of_le hm (hbd x hx))
  have hga : g a = 0 := hgs a (by simp)
  have hgb : g b = 0 := hgs b (by simp)
  have hgdc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hgda : deriv g a = 0 := by
    have hleft : ∀ x < a, deriv g x = 0 := by
      intro x hx
      have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        exact hgs y (fun hmem => absurd hmem.1 (not_lt.mpr (le_of_lt hy)))
      rw [hev.deriv_eq]
      simp
    have hclosed : IsClosed {x : ℝ | deriv g x = 0} :=
      isClosed_eq hgdc continuous_const
    have hle : a ∈ closure (Set.Iio a) := by simp [closure_Iio]
    exact closure_minimal (fun x hx => hleft x hx) hclosed hle
  have hgdb : deriv g b = 0 := by
    have hright : ∀ x, b < x → deriv g x = 0 := by
      intro x hx
      have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact hgs y (fun hmem => absurd hmem.2 (not_lt.mpr (le_of_lt hy)))
      rw [hev.deriv_eq]
      simp
    have hclosed : IsClosed {x : ℝ | deriv g x = 0} :=
      isClosed_eq hgdc continuous_const
    have hle : b ∈ closure (Set.Ioi b) := by simp [closure_Ioi]
    exact closure_minimal (fun x hx => hright x hx) hclosed hle
  -- the first-derivative test applied to the weight `twoIbpWeightC`
  have hΨderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (twoIbpWeightC Φ g) (twoIbpWeightCDeriv Φ g x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact twoIbpWeightC_hasDerivAt hΦ hg (hpd x hx)
  have hΦderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt Φ (deriv Φ x) x := by
    intro x _
    exact ((hΦ.differentiable (by norm_num)) x).hasDerivAt
  have hΨcont : ContinuousOn (twoIbpWeightC Φ g) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact twoIbpWeightC_cont hΦ hg hpd
  have hΨ'cont : ContinuousOn (twoIbpWeightCDeriv Φ g) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact twoIbpWeightCDeriv_cont hΦ hg hpd
  have hΨ'int : IntervalIntegrable (fun x => ‖twoIbpWeightCDeriv Φ g x‖) volume a b :=
    hΨ'cont.norm.intervalIntegrable
  have hmain := first_derivative_test_ibp (a := a) (b := b) (t := 1)
    (ψ := twoIbpWeightC Φ g) (ψ' := twoIbpWeightCDeriv Φ g)
    (φ := Φ) (φ' := deriv Φ) hab (by norm_num) hΨderiv hΦderiv hΨcont hΨ'cont hΨ'int
  have hA' : (∫ x in a..b, twoIbpWeightC Φ g x * (Complex.I * ((deriv Φ x : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((1 : ℝ) * (Φ x : ℂ))))
      = ∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ)) := by
    have h1 : (∫ x in a..b, twoIbpWeightC Φ g x * (Complex.I * ((deriv Φ x : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((1 : ℝ) * (Φ x : ℂ))))
        = ∫ x in a..b, twoIbpWeightC Φ g x * (Complex.I * ((deriv Φ x : ℝ) : ℂ))
            * Complex.exp (Complex.I * (Φ x : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp
    have h2 : (∫ x in a..b, twoIbpWeightC Φ g x * (Complex.I * ((deriv Φ x : ℝ) : ℂ))
            * Complex.exp (Complex.I * (Φ x : ℂ)))
        = ∫ x in a..b, Complex.I * (((deriv g x / deriv Φ x
            - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
            * Complex.exp (Complex.I * (Φ x : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      show twoIbpWeightC Φ g x * (Complex.I * ((deriv Φ x : ℝ) : ℂ))
          * Complex.exp (Complex.I * (Φ x : ℂ))
        = Complex.I * (((deriv g x / deriv Φ x
            - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
            * Complex.exp (Complex.I * (Φ x : ℂ))
      rw [twoIbpWeightC_mul (Φ := Φ) (g := g) (x := x) (hpd x hx)]
    have h3 : (∫ x in a..b, Complex.I * (((deriv g x / deriv Φ x
            - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
            * Complex.exp (Complex.I * (Φ x : ℂ)))
        = Complex.I * ∫ x in a..b, (((deriv g x / deriv Φ x
            - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
            * Complex.exp (Complex.I * (Φ x : ℂ)) := by
      rw [show (∫ x in a..b, Complex.I * (((deriv g x / deriv Φ x
              - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
              * Complex.exp (Complex.I * (Φ x : ℂ)))
          = ∫ x in a..b, Complex.I * ((((deriv g x / deriv Φ x
              - g x * deriv (deriv Φ) x / (deriv Φ x) ^ 2 : ℝ)) : ℂ)
              * Complex.exp (Complex.I * (Φ x : ℂ))) from by
        apply intervalIntegral.integral_congr
        intro x _
        ring]
      rw [intervalIntegral.integral_const_mul]
    rw [h1, h2, h3]
    exact (integral_ibp_exp_div_deriv hab hΦ hg hpd hga hgb).symm
  have hPsiA : twoIbpWeightC Φ g a = 0 := by
    change (((twoIbpWeightR Φ g a : ℝ)) : ℂ) = 0
    simp [twoIbpWeightR, hga, hgda]
  have hPsiB : twoIbpWeightC Φ g b = 0 := by
    change (((twoIbpWeightR Φ g b : ℝ)) : ℂ) = 0
    simp [twoIbpWeightR, hgb, hgdb]
  have hbound1 : ‖∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))‖
      ≤ ∫ x in a..b, ‖twoIbpWeightCDeriv Φ g x‖ := by
    rw [← hA']
    simpa [hPsiA, hPsiB] using hmain
  -- pointwise bound on the derivative of the weight
  have hpointwise : ∀ x ∈ Set.Icc a b,
      ‖twoIbpWeightCDeriv Φ g x‖ ≤ (m ^ 2)⁻¹ * |deriv (deriv g) x| + (3 * M / m ^ 3) * |deriv g x|
        + (M3 / m ^ 3) * |g x| + (3 * M ^ 2 / m ^ 4) * |g x| := by
    intro x hx
    have h : |twoIbpWeightRDeriv Φ g x| ≤ (m ^ 2)⁻¹ * |deriv (deriv g) x|
        + (3 * M / m ^ 3) * |deriv g x| + (M3 / m ^ 3) * |g x|
        + (3 * M ^ 2 / m ^ 4) * |g x| :=
      twoIbpWeightRDeriv_abs_le hm hbd h2 h3 hx
    have hnorm : ‖twoIbpWeightCDeriv Φ g x‖ = |twoIbpWeightRDeriv Φ g x| := by
      change ‖(((twoIbpWeightRDeriv Φ g x : ℝ)) : ℂ)‖ = |twoIbpWeightRDeriv Φ g x|
      simp
    rw [hnorm]
    exact h
  have hgddc : Continuous (deriv (deriv g)) := continuous_deriv_deriv_of_contDiff_two hg
  have hgc : Continuous g := hg.continuous
  have hi_gdd : IntervalIntegrable (fun x => |deriv (deriv g) x|) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hgddc.abs.continuousOn
  have hi_gd : IntervalIntegrable (fun x => |deriv g x|) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hgdc.abs.continuousOn
  have hi_g : IntervalIntegrable (fun x => |g x|) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hgc.abs.continuousOn
  have hI1 : IntervalIntegrable (fun x => (m ^ 2)⁻¹ * |deriv (deriv g) x|) volume a b :=
    hi_gdd.const_mul _
  have hI2 : IntervalIntegrable (fun x => (3 * M / m ^ 3) * |deriv g x|) volume a b :=
    hi_gd.const_mul _
  have hI3 : IntervalIntegrable (fun x => (M3 / m ^ 3) * |g x|) volume a b :=
    hi_g.const_mul _
  have hI4 : IntervalIntegrable (fun x => (3 * M ^ 2 / m ^ 4) * |g x|) volume a b :=
    hi_g.const_mul _
  have hbnd_int : IntervalIntegrable
      (fun x => (m ^ 2)⁻¹ * |deriv (deriv g) x| + (3 * M / m ^ 3) * |deriv g x|
        + (M3 / m ^ 3) * |g x| + (3 * M ^ 2 / m ^ 4) * |g x|) volume a b :=
    ((hI1.add hI2).add hI3).add hI4
  have hle : (∫ x in a..b, ‖twoIbpWeightCDeriv Φ g x‖)
      ≤ ∫ x in a..b, ((m ^ 2)⁻¹ * |deriv (deriv g) x| + (3 * M / m ^ 3) * |deriv g x|
        + (M3 / m ^ 3) * |g x| + (3 * M ^ 2 / m ^ 4) * |g x|) :=
    intervalIntegral.integral_mono_on hab hΨ'int hbnd_int hpointwise
  have hsplit : (∫ x in a..b, ((m ^ 2)⁻¹ * |deriv (deriv g) x| + (3 * M / m ^ 3) * |deriv g x|
        + (M3 / m ^ 3) * |g x| + (3 * M ^ 2 / m ^ 4) * |g x|))
      = (m ^ 2)⁻¹ * (∫ x in a..b, |deriv (deriv g) x|)
        + (3 * M / m ^ 3) * (∫ x in a..b, |deriv g x|)
        + (M3 / m ^ 3) * (∫ x in a..b, |g x|)
        + (3 * M ^ 2 / m ^ 4) * (∫ x in a..b, |g x|) := by
    rw [intervalIntegral.integral_add ((hI1.add hI2).add hI3) hI4,
        intervalIntegral.integral_add (hI1.add hI2) hI3,
        intervalIntegral.integral_add hI1 hI2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hI2nn : 0 ≤ ∫ x in a..b, |deriv (deriv g) x| :=
    intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _)
  have hI1nn : 0 ≤ ∫ x in a..b, |deriv g x| :=
    intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _)
  have hI0nn : 0 ≤ ∫ x in a..b, |g x| :=
    intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _)
  calc ‖∫ x in a..b, (g x : ℂ) * Complex.exp (Complex.I * (Φ x : ℂ))‖
      ≤ ∫ x in a..b, ‖twoIbpWeightCDeriv Φ g x‖ := hbound1
    _ ≤ ∫ x in a..b, ((m ^ 2)⁻¹ * |deriv (deriv g) x| + (3 * M / m ^ 3) * |deriv g x|
          + (M3 / m ^ 3) * |g x| + (3 * M ^ 2 / m ^ 4) * |g x|) := hle
    _ = (m ^ 2)⁻¹ * (∫ x in a..b, |deriv (deriv g) x|)
          + (3 * M / m ^ 3) * (∫ x in a..b, |deriv g x|)
          + (M3 / m ^ 3) * (∫ x in a..b, |g x|)
          + (3 * M ^ 2 / m ^ 4) * (∫ x in a..b, |g x|) := hsplit
    _ ≤ 8 * ((∫ x in a..b, |deriv (deriv g) x|) + (∫ x in a..b, |deriv g x|) * M / m
          + (∫ x in a..b, |g x|) * M3 / m
          + (∫ x in a..b, |g x|) * M ^ 2 / m ^ 2) / m ^ 2 :=
        two_ibp_arith_bound hm hM hM3 hI2nn hI1nn hI0nn

end Commons.Analysis.Oscillatory