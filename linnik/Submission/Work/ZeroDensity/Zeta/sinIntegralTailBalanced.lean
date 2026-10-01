import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeSelf.oscillatoryIoiBound

namespace Work.ZeroDensity.Zeta

open MeasureTheory Set Filter
open scoped Topology

/-!
# Sharp oscillatory-integral tail bound for `∫_A^∞ sin(v) v^{-s-1} dv`

We prove `sinIntegralTailBalanced`:
`‖∫_{v>A} sin v · v^{-s-1}‖ ≤ 2 A^{-Re s}/(A - |Im s|) + 2 A^{-Re s - 1}` for
`Re s > 0`, `A ≥ 1`, `|Im s| < A`.  The proof splits `sin v = (e^{iv} - e^{-iv})/(2i)`
and bounds each half by a *sharp* (constant `2`) first-derivative oscillatory-integral
estimate, of the form `‖∫_{Ioi a} g ψ e^{iφ}‖ ≤ 2 g a` valid when `g ≥ 0` is
non-increasing to `0` and `φ' = ψ` on `[a,∞)`.
-/

/-- Sharp (constant `2`) first-derivative oscillatory integral bound on a finite
interval.  If `φ' = ψ` and `g ≥ 0` is non-increasing on `[a,b]`, then
`‖∫_a^b g·ψ·e^{iφ}‖ ≤ 2 g a`. -/
theorem oscSharpIoc {φ ψ g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivAt φ (ψ x) x) (hψc : ContinuousOn ψ (Set.Icc a b))
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x) (hg'c : ContinuousOn g' (Set.Icc a b))
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hg' : ∀ x ∈ Set.Icc a b, g' x ≤ 0) :
    ‖∫ x in a..b, ((g x * ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))‖ ≤ 2 * g a := by
  set E : ℝ → ℂ := fun x => Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) with hEdef
  have hφc : ContinuousOn φ (Set.Icc a b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hEderiv : ∀ x ∈ Set.Icc a b, HasDerivAt E (E x * (Complex.I * ((ψ x : ℝ) : ℂ))) x := by
    intro x hx
    have h1 : HasDerivAt (fun y => Complex.I * ((φ y : ℝ) : ℂ)) (Complex.I * ((ψ x : ℝ) : ℂ)) x :=
      HasDerivAt.const_mul Complex.I ((hφ x hx).ofReal_comp)
    exact h1.cexp
  set u : ℝ → ℂ := fun x => -Complex.I * (g x : ℂ) with hudef
  set u' : ℝ → ℂ := fun x => -Complex.I * (g' x : ℂ) with hu'def
  have huderiv : ∀ x ∈ Set.Icc a b, HasDerivAt u (u' x) x := by
    intro x hx
    have h2 : HasDerivAt (fun y => ((g y : ℝ) : ℂ)) ((g' x : ℝ) : ℂ) x := (hg x hx).ofReal_comp
    have h3 := h2.const_mul (-Complex.I)
    simpa [u, u'] using h3
  have hEint : IntervalIntegrable (fun x => E x * (Complex.I * ((ψ x : ℝ) : ℂ))) volume a b := by
    refine (show ContinuousOn (fun x => E x * (Complex.I * ((ψ x : ℝ) : ℂ))) (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]
    have hEc : ContinuousOn E (Set.Icc a b) := by
      apply Complex.continuous_exp.comp_continuousOn
      exact continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn' hφc)
    exact hEc.mul (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn' hψc))
  have hu'int : IntervalIntegrable u' volume a b := by
    refine (show ContinuousOn u' (Set.uIcc a b) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn' hg'c)
  have hEicc : ∀ x ∈ Set.uIcc a b, HasDerivAt E (E x * (Complex.I * ((ψ x : ℝ) : ℂ))) x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hEderiv x hx
  have huicc : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; exact huderiv x hx
  have hIBP : ∫ x in a..b, u x * (E x * (Complex.I * ((ψ x : ℝ) : ℂ)))
      = u b * E b - u a * E a - ∫ x in a..b, u' x * E x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul huicc hEicc hu'int hEint
  have hcongr : ∫ x in a..b, ((g x * ψ x : ℝ) : ℂ) * E x
      = ∫ x in a..b, u x * (E x * (Complex.I * ((ψ x : ℝ) : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    simp only [hudef]
    rw [Complex.ofReal_mul]
    ring_nf
    rw [Complex.I_sq]; ring
  have hnormE : ∀ x, ‖E x‖ = 1 := fun x => Complex.norm_exp_I_mul_ofReal (φ x)
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hub : ‖u b‖ = g b := by
    simp only [hudef, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (hg0 b hb)
  have hua : ‖u a‖ = g a := by
    simp only [hudef, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (hg0 a ha)
  have hbound : ‖u b * E b - u a * E a‖ ≤ g b + g a := by
    calc ‖u b * E b - u a * E a‖ ≤ ‖u b * E b‖ + ‖u a * E a‖ := norm_sub_le _ _
      _ = ‖u b‖ + ‖u a‖ := by simp only [norm_mul, hnormE, mul_one]
      _ = g b + g a := by rw [hub, hua]
  have hFTC : ∫ x in a..b, g' x = g b - g a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro x hx; rw [Set.uIcc_of_le hab] at hx; exact hg x hx
    · refine (show ContinuousOn g' (Set.uIcc a b) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab]; exact hg'c
  have hrem : ‖∫ x in a..b, u' x * E x‖ ≤ g a - g b := by
    calc ‖∫ x in a..b, u' x * E x‖
        ≤ ∫ x in a..b, ‖u' x * E x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, ‖u' x‖ := by
            apply intervalIntegral.integral_congr; intro x hx
            simp only [norm_mul, hnormE, mul_one]
      _ = ∫ x in a..b, (-(g' x)) := by
            apply intervalIntegral.integral_congr; intro x hx
            rw [Set.uIcc_of_le hab] at hx
            simp only [hu'def, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonpos (hg' x hx)]
      _ = g a - g b := by rw [intervalIntegral.integral_neg, hFTC]; ring
  rw [hcongr, hIBP]
  calc ‖u b * E b - u a * E a - ∫ x in a..b, u' x * E x‖
      ≤ ‖u b * E b - u a * E a‖ + ‖∫ x in a..b, u' x * E x‖ := norm_sub_le _ _
    _ ≤ (g b + g a) + (g a - g b) := add_le_add hbound hrem
    _ = 2 * g a := by ring

/-- Sharp (constant `2`) first-derivative oscillatory integral bound over `Ioi a`. -/
theorem oscSharpIoi {φ ψ g g' : ℝ → ℝ} {a : ℝ}
    (hφ : ∀ x ∈ Set.Ici a, HasDerivAt φ (ψ x) x) (hψc : ContinuousOn ψ (Set.Ici a))
    (hg : ∀ x ∈ Set.Ici a, HasDerivAt g (g' x) x) (hg'c : ContinuousOn g' (Set.Ici a))
    (hg0 : ∀ x ∈ Set.Ici a, 0 ≤ g x) (hg' : ∀ x ∈ Set.Ici a, g' x ≤ 0)
    (hgint : MeasureTheory.IntegrableOn
      (fun x => ((g x * ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))) (Set.Ioi a)) :
    ‖∫ x in Set.Ioi a, ((g x * ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))‖
      ≤ 2 * g a := by
  refine Work.ZeroDensity.Ingham.AfeSelf.ioiIntervalBoundAux hgint (fun B hB => ?_)
  exact oscSharpIoc hB (fun x hx => hφ x hx.1) (hψc.mono (fun x hx => hx.1))
    (fun x hx => hg x hx.1) (hg'c.mono (fun x hx => hx.1))
    (fun x hx => hg0 x hx.1) (fun x hx => hg' x hx.1)

/-! ### Complex power identity -/

/-- Split the complex power of a positive real according to real/imaginary parts. -/
lemma cpow_neg_s_sub_one (s : ℂ) {v : ℝ} (hv : 0 < v) :
    (v : ℂ) ^ (-s - 1) = ((v ^ (-s.re - 1) : ℝ) : ℂ) * Complex.exp (↑(-s.im * Real.log v) * Complex.I) := by
  have hvne : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.cpow_def_of_ne_zero hvne, ← Complex.ofReal_log hv.le]
  have hdec : (↑(Real.log v) : ℂ) * (-s - 1)
      = ↑(Real.log v * (-s.re - 1)) + ↑(-s.im * Real.log v) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hdec, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hv]

/-! ### Auxiliary functions for the two phase decompositions -/

/-- Phase of `e^{iv} v^{-s-1}`. -/
noncomputable def phi1 (s : ℂ) : ℝ → ℝ := fun x => x - s.im * Real.log x
/-- Derivative of `phi1`. -/
noncomputable def psi1 (s : ℂ) : ℝ → ℝ := fun x => 1 - s.im / x
/-- Modulus factor: `gg1 * psi1 = x^{-Re s - 1}`. -/
noncomputable def gg1 (s : ℂ) : ℝ → ℝ := fun x => x ^ (-s.re) / (x - s.im)
/-- Derivative of `gg1`. -/
noncomputable def gg1' (s : ℂ) : ℝ → ℝ :=
  fun x => ((-s.re * x ^ (-s.re - 1)) * (x - s.im) - x ^ (-s.re)) / (x - s.im) ^ 2

/-- Phase of `e^{-iv} v^{-s-1}`. -/
noncomputable def phi2 (s : ℂ) : ℝ → ℝ := fun x => -x - s.im * Real.log x
/-- Derivative of `phi2`. -/
noncomputable def psi2 (s : ℂ) : ℝ → ℝ := fun x => -1 - s.im / x
/-- Modulus factor: `gg2 * psi2 = -x^{-Re s - 1}`. -/
noncomputable def gg2 (s : ℂ) : ℝ → ℝ := fun x => x ^ (-s.re) / (x + s.im)
/-- Derivative of `gg2`. -/
noncomputable def gg2' (s : ℂ) : ℝ → ℝ :=
  fun x => ((-s.re * x ^ (-s.re - 1)) * (x + s.im) - x ^ (-s.re)) / (x + s.im) ^ 2

/-! ### Pointwise phase decompositions -/

lemma phase1Id (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : s.im < x) :
    Complex.exp (Complex.I * (x : ℂ)) * (x : ℂ) ^ (-s - 1)
      = ((x ^ (-s.re) / (x - s.im) * (1 - s.im / x) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (((x - s.im * Real.log x) : ℝ) : ℂ)) := by
  rw [cpow_neg_s_sub_one s hx]
  have hexp : Complex.exp (Complex.I * (((x - s.im * Real.log x) : ℝ) : ℂ))
      = Complex.exp (Complex.I * (x : ℂ)) * Complex.exp (↑(-s.im * Real.log x) * Complex.I) := by
    rw [show (Complex.I * (((x - s.im * Real.log x) : ℝ) : ℂ))
          = Complex.I * (x : ℂ) + ↑(-s.im * Real.log x) * Complex.I by push_cast; ring,
      Complex.exp_add]
  have hcoef : (x ^ (-s.re) / (x - s.im) * (1 - s.im / x) : ℝ) = x ^ (-s.re - 1) := by
    have hxm : x - s.im ≠ 0 := by linarith
    have h1 : (1 - s.im / x) = (x - s.im) / x := by rw [sub_div, div_self (ne_of_gt hx)]
    rw [h1, div_mul_div_comm, mul_comm (x ^ (-s.re)) (x - s.im), mul_div_mul_left _ _ hxm,
        div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hx (-s.re) (-1), sub_eq_add_neg]
  rw [hcoef, hexp]
  ring

lemma phase2Id (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : -s.im < x) :
    ((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ))
      = - (Complex.exp (-(Complex.I * (x : ℂ))) * (x : ℂ) ^ (-s - 1)) := by
  change ((x ^ (-s.re) / (x + s.im) * (-1 - s.im / x) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((-x - s.im * Real.log x) : ℝ) : ℂ))
      = - (Complex.exp (-(Complex.I * (x : ℂ))) * (x : ℂ) ^ (-s - 1))
  rw [cpow_neg_s_sub_one s hx]
  have hexp : Complex.exp (Complex.I * (((-x - s.im * Real.log x) : ℝ) : ℂ))
      = Complex.exp (-(Complex.I * (x : ℂ))) * Complex.exp (↑(-s.im * Real.log x) * Complex.I) := by
    rw [show (Complex.I * (((-x - s.im * Real.log x) : ℝ) : ℂ))
          = -(Complex.I * (x : ℂ)) + ↑(-s.im * Real.log x) * Complex.I by push_cast; ring,
      Complex.exp_add]
  have hcoef : (x ^ (-s.re) / (x + s.im) * (-1 - s.im / x) : ℝ) = - x ^ (-s.re - 1) := by
    have hxm : x + s.im ≠ 0 := by linarith
    have h1 : (-1 - s.im / x) = -((x + s.im) / x) := by
      rw [add_div, div_self (ne_of_gt hx)]; ring
    rw [h1, mul_neg, div_mul_div_comm, mul_comm (x ^ (-s.re)) (x + s.im),
        mul_div_mul_left _ _ hxm, div_eq_mul_inv, ← Real.rpow_neg_one x,
        ← Real.rpow_add hx (-s.re) (-1), sub_eq_add_neg]
  rw [hcoef, hexp]
  simp only [Complex.ofReal_neg]
  ring

/-! ### Derivatives of the auxiliary functions -/

lemma phi1_hasDerivAt (s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (phi1 s) (psi1 s x) x := by
  have h3 : HasDerivAt (fun y : ℝ => y - s.im * Real.log y) (1 - s.im * x⁻¹) x :=
    (hasDerivAt_id x).sub ((Real.hasDerivAt_log hx).const_mul s.im)
  rw [show (1 - s.im * x⁻¹ : ℝ) = psi1 s x by simp [psi1, div_eq_mul_inv]] at h3
  exact h3

lemma gg1_hasDerivAt (s : ℂ) {x : ℝ} (hx : x ≠ 0) (hxt : x - s.im ≠ 0) :
    HasDerivAt (gg1 s) (gg1' s x) x := by
  have ha : HasDerivAt (fun y : ℝ => y ^ (-s.re)) (-s.re * x ^ (-s.re - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx)
  have hb : HasDerivAt (fun y : ℝ => y - s.im) 1 x := (hasDerivAt_id x).sub_const s.im
  have hd := ha.div hb hxt
  have hval : ((-s.re * x ^ (-s.re - 1)) * (x - s.im) - x ^ (-s.re) * 1) / (x - s.im) ^ 2
      = gg1' s x := by simp [gg1', mul_one]
  rw [hval] at hd
  exact hd

lemma phi2_hasDerivAt (s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (phi2 s) (psi2 s x) x := by
  have h3 : HasDerivAt (fun y : ℝ => -y - s.im * Real.log y) (-1 - s.im * x⁻¹) x :=
    (hasDerivAt_id x).neg.sub ((Real.hasDerivAt_log hx).const_mul s.im)
  rw [show (-1 - s.im * x⁻¹ : ℝ) = psi2 s x by simp [psi2, div_eq_mul_inv]] at h3
  exact h3

lemma gg2_hasDerivAt (s : ℂ) {x : ℝ} (hx : x ≠ 0) (hxt : x + s.im ≠ 0) :
    HasDerivAt (gg2 s) (gg2' s x) x := by
  have ha : HasDerivAt (fun y : ℝ => y ^ (-s.re)) (-s.re * x ^ (-s.re - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx)
  have hb : HasDerivAt (fun y : ℝ => y + s.im) 1 x := (hasDerivAt_id x).add_const s.im
  have hd := ha.div hb hxt
  have hval : ((-s.re * x ^ (-s.re - 1)) * (x + s.im) - x ^ (-s.re) * 1) / (x + s.im) ^ 2
      = gg2' s x := by simp [gg2', mul_one]
  rw [hval] at hd
  exact hd

/-! ### Continuity of the auxiliary functions -/

lemma phi1_cont (s : ℂ) {A : ℝ} (hA : 0 < A) : ContinuousOn (phi1 s) (Set.Ici A) := by
  have hne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  change ContinuousOn (fun x : ℝ => x - s.im * Real.log x) (Set.Ici A)
  exact continuousOn_id.sub (continuousOn_const.mul (continuousOn_id.log hne))

lemma phi2_cont (s : ℂ) {A : ℝ} (hA : 0 < A) : ContinuousOn (phi2 s) (Set.Ici A) := by
  have hne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  change ContinuousOn (fun x : ℝ => -x - s.im * Real.log x) (Set.Ici A)
  exact (continuousOn_id.neg).sub (continuousOn_const.mul (continuousOn_id.log hne))

lemma psi1_cont (s : ℂ) {A : ℝ} (hA : 0 < A) : ContinuousOn (psi1 s) (Set.Ici A) := by
  have hne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  have h1 : ContinuousOn (fun x : ℝ => s.im / x) (Set.Ici A) :=
    ContinuousOn.div continuousOn_const continuousOn_id hne
  change ContinuousOn (fun x : ℝ => 1 - s.im / x) (Set.Ici A)
  exact continuousOn_const.sub h1

lemma psi2_cont (s : ℂ) {A : ℝ} (hA : 0 < A) : ContinuousOn (psi2 s) (Set.Ici A) := by
  have hne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  have h1 : ContinuousOn (fun x : ℝ => s.im / x) (Set.Ici A) :=
    ContinuousOn.div continuousOn_const continuousOn_id hne
  change ContinuousOn (fun x : ℝ => -1 - s.im / x) (Set.Ici A)
  exact continuousOn_const.sub h1

lemma gg1_cont (s : ℂ) {A : ℝ} (hA : 0 < A) (hAt : |s.im| < A) :
    ContinuousOn (gg1 s) (Set.Ici A) := by
  have hxne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  have hrpow : ContinuousOn (fun x : ℝ => x ^ (-s.re)) (Set.Ici A) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxne x hx))
  have hxmt : ∀ x ∈ Set.Ici A, x - s.im ≠ 0 := fun x hx =>
    ne_of_gt (by have := lt_of_lt_of_le hAt hx; linarith [le_abs_self s.im])
  change ContinuousOn (fun x : ℝ => x ^ (-s.re) / (x - s.im)) (Set.Ici A)
  exact hrpow.div (continuousOn_id.sub continuousOn_const) hxmt

lemma gg2_cont (s : ℂ) {A : ℝ} (hA : 0 < A) (hAt : |s.im| < A) :
    ContinuousOn (gg2 s) (Set.Ici A) := by
  have hxne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  have hrpow : ContinuousOn (fun x : ℝ => x ^ (-s.re)) (Set.Ici A) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxne x hx))
  have hxpt : ∀ x ∈ Set.Ici A, x + s.im ≠ 0 := fun x hx =>
    ne_of_gt (by have := lt_of_lt_of_le hAt hx; linarith [neg_abs_le s.im])
  change ContinuousOn (fun x : ℝ => x ^ (-s.re) / (x + s.im)) (Set.Ici A)
  exact hrpow.div (continuousOn_id.add continuousOn_const) hxpt

lemma gg1'_cont (s : ℂ) {A : ℝ} (hA : 0 < A) (hAt : |s.im| < A) :
    ContinuousOn (gg1' s) (Set.Ici A) := by
  have hxne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  have hrpow1 : ContinuousOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ici A) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxne x hx))
  have hrpow0 : ContinuousOn (fun x : ℝ => x ^ (-s.re)) (Set.Ici A) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxne x hx))
  have hxmt : ∀ x ∈ Set.Ici A, x - s.im ≠ 0 := fun x hx =>
    ne_of_gt (by have := lt_of_lt_of_le hAt hx; linarith [le_abs_self s.im])
  have hnum : ContinuousOn (fun x : ℝ => (-s.re * x ^ (-s.re - 1)) * (x - s.im) - x ^ (-s.re))
      (Set.Ici A) :=
    ((continuousOn_const.mul hrpow1).mul (continuousOn_id.sub continuousOn_const)).sub hrpow0
  have hden : ContinuousOn (fun x : ℝ => (x - s.im) ^ 2) (Set.Ici A) :=
    (continuousOn_id.sub continuousOn_const).pow 2
  change ContinuousOn
    (fun x : ℝ => ((-s.re * x ^ (-s.re - 1)) * (x - s.im) - x ^ (-s.re)) / (x - s.im) ^ 2) (Set.Ici A)
  exact hnum.div hden (fun x hx => pow_ne_zero 2 (hxmt x hx))

lemma gg2'_cont (s : ℂ) {A : ℝ} (hA : 0 < A) (hAt : |s.im| < A) :
    ContinuousOn (gg2' s) (Set.Ici A) := by
  have hxne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hA hx)
  have hrpow1 : ContinuousOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ici A) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxne x hx))
  have hrpow0 : ContinuousOn (fun x : ℝ => x ^ (-s.re)) (Set.Ici A) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxne x hx))
  have hxpt : ∀ x ∈ Set.Ici A, x + s.im ≠ 0 := fun x hx =>
    ne_of_gt (by have := lt_of_lt_of_le hAt hx; linarith [neg_abs_le s.im])
  have hnum : ContinuousOn (fun x : ℝ => (-s.re * x ^ (-s.re - 1)) * (x + s.im) - x ^ (-s.re))
      (Set.Ici A) :=
    ((continuousOn_const.mul hrpow1).mul (continuousOn_id.add continuousOn_const)).sub hrpow0
  have hden : ContinuousOn (fun x : ℝ => (x + s.im) ^ 2) (Set.Ici A) :=
    (continuousOn_id.add continuousOn_const).pow 2
  change ContinuousOn
    (fun x : ℝ => ((-s.re * x ^ (-s.re - 1)) * (x + s.im) - x ^ (-s.re)) / (x + s.im) ^ 2) (Set.Ici A)
  exact hnum.div hden (fun x hx => pow_ne_zero 2 (hxpt x hx))

/-! ### Product identities, signs and limits -/

lemma gg1_mul_psi1 (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : s.im < x) :
    gg1 s x * psi1 s x = x ^ (-s.re - 1) := by
  have hxm : x - s.im ≠ 0 := by linarith
  have h1 : (1 - s.im / x) = (x - s.im) / x := by rw [sub_div, div_self (ne_of_gt hx)]
  rw [gg1, psi1, h1, div_mul_div_comm, mul_comm (x ^ (-s.re)) (x - s.im), mul_div_mul_left _ _ hxm,
      div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hx (-s.re) (-1), sub_eq_add_neg]

lemma gg2_mul_psi2 (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : -s.im < x) :
    gg2 s x * psi2 s x = - x ^ (-s.re - 1) := by
  have hxm : x + s.im ≠ 0 := by linarith
  have h1 : (-1 - s.im / x) = -((x + s.im) / x) := by rw [add_div, div_self (ne_of_gt hx)]; ring
  rw [gg2, psi2, h1, mul_neg, div_mul_div_comm, mul_comm (x ^ (-s.re)) (x + s.im),
      mul_div_mul_left _ _ hxm, div_eq_mul_inv, ← Real.rpow_neg_one x,
      ← Real.rpow_add hx (-s.re) (-1), sub_eq_add_neg]

lemma gg1_nonneg (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : s.im < x) : 0 ≤ gg1 s x := by
  rw [gg1]; exact div_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (by linarith)

lemma gg2_nonneg (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : -s.im < x) : 0 ≤ gg2 s x := by
  rw [gg2]; exact div_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (by linarith)

lemma gg1'_nonpos (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : s.im < x) (hs0 : 0 < s.re) :
    gg1' s x ≤ 0 := by
  rw [gg1']
  apply div_nonpos_of_nonpos_of_nonneg
  · have h1 : (-s.re * x ^ (-s.re - 1)) * (x - s.im) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt hx) _)) (by linarith)
    have h2 : -(x ^ (-s.re)) ≤ 0 := neg_nonpos.mpr (Real.rpow_nonneg (le_of_lt hx) _)
    have heq : (-s.re * x ^ (-s.re - 1)) * (x - s.im) - x ^ (-s.re)
        = (-s.re * x ^ (-s.re - 1)) * (x - s.im) + -(x ^ (-s.re)) := by ring
    rw [heq]; exact add_nonpos h1 h2
  · exact sq_nonneg _

lemma gg2'_nonpos (s : ℂ) {x : ℝ} (hx : 0 < x) (hxt : -s.im < x) (hs0 : 0 < s.re) :
    gg2' s x ≤ 0 := by
  rw [gg2']
  apply div_nonpos_of_nonpos_of_nonneg
  · have h1 : (-s.re * x ^ (-s.re - 1)) * (x + s.im) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt hx) _)) (by linarith)
    have h2 : -(x ^ (-s.re)) ≤ 0 := neg_nonpos.mpr (Real.rpow_nonneg (le_of_lt hx) _)
    have heq : (-s.re * x ^ (-s.re - 1)) * (x + s.im) - x ^ (-s.re)
        = (-s.re * x ^ (-s.re - 1)) * (x + s.im) + -(x ^ (-s.re)) := by ring
    rw [heq]; exact add_nonpos h1 h2
  · exact sq_nonneg _

lemma gg1_tendsto (s : ℂ) (hs0 : 0 < s.re) : Tendsto (gg1 s) atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => x ^ (-s.re) / (x - s.im)) atTop (nhds 0)
  have hden : Tendsto (fun x : ℝ => x - s.im) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-s.im) Filter.tendsto_id
  exact (tendsto_rpow_neg_atTop hs0).div_atTop hden

lemma gg2_tendsto (s : ℂ) (hs0 : 0 < s.re) : Tendsto (gg2 s) atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => x ^ (-s.re) / (x + s.im)) atTop (nhds 0)
  have hden : Tendsto (fun x : ℝ => x + s.im) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (s.im) Filter.tendsto_id
  exact (tendsto_rpow_neg_atTop hs0).div_atTop hden

/-! ### Integrability of the two oscillatory integrands -/

lemma hint1 (s : ℂ) (hs0 : 0 < s.re) {A : ℝ} (hA : 1 ≤ A) (hAt : |s.im| < A) :
    IntegrableOn
      (fun x => ((gg1 s x * psi1 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi1 s x : ℝ) : ℂ)))
      (Set.Ioi A) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hIoi : Set.Ioi A ⊆ Set.Ici A := fun x hx => le_of_lt (Set.mem_Ioi.mp hx)
  have phc : ContinuousOn (phi1 s) (Set.Ioi A) := (phi1_cont s hApos).mono hIoi
  have psc : ContinuousOn (psi1 s) (Set.Ioi A) := (psi1_cont s hApos).mono hIoi
  have ggc : ContinuousOn (gg1 s) (Set.Ioi A) := (gg1_cont s hApos hAt).mono hIoi
  have hcont : ContinuousOn
      (fun x => ((gg1 s x * psi1 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi1 s x : ℝ) : ℂ)))
      (Set.Ioi A) :=
    (Complex.continuous_ofReal.comp_continuousOn (ggc.mul psc)).mul
      (Complex.continuous_exp.comp_continuousOn
        (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn phc)))
  refine Integrable.mono' (g := fun x : ℝ => x ^ (-s.re - 1)) ?_ ?_ ?_
  · exact integrableOn_Ioi_rpow_of_lt (show -s.re - 1 < -1 by linarith) hApos
  · exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le hApos (le_of_lt hx)
    have hxt : s.im < x := lt_of_le_of_lt (le_abs_self s.im) (lt_of_lt_of_le hAt (le_of_lt hx))
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs,
        gg1_mul_psi1 s hxpos hxt, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hxpos) _)]

lemma hint2 (s : ℂ) (hs0 : 0 < s.re) {A : ℝ} (hA : 1 ≤ A) (hAt : |s.im| < A) :
    IntegrableOn
      (fun x => ((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ)))
      (Set.Ioi A) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hIoi : Set.Ioi A ⊆ Set.Ici A := fun x hx => le_of_lt (Set.mem_Ioi.mp hx)
  have phc : ContinuousOn (phi2 s) (Set.Ioi A) := (phi2_cont s hApos).mono hIoi
  have psc : ContinuousOn (psi2 s) (Set.Ioi A) := (psi2_cont s hApos).mono hIoi
  have ggc : ContinuousOn (gg2 s) (Set.Ioi A) := (gg2_cont s hApos hAt).mono hIoi
  have hcont : ContinuousOn
      (fun x => ((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ)))
      (Set.Ioi A) :=
    (Complex.continuous_ofReal.comp_continuousOn (ggc.mul psc)).mul
      (Complex.continuous_exp.comp_continuousOn
        (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn phc)))
  refine Integrable.mono' (g := fun x : ℝ => x ^ (-s.re - 1)) ?_ ?_ ?_
  · exact integrableOn_Ioi_rpow_of_lt (show -s.re - 1 < -1 by linarith) hApos
  · exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le hApos (le_of_lt hx)
    have hxt : -s.im < x := lt_of_le_of_lt (neg_le_abs s.im) (lt_of_lt_of_le hAt (le_of_lt hx))
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs,
        gg2_mul_psi2 s hxpos hxt, abs_neg, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hxpos) _)]

/-! ### The complex exponential form of `sin` -/

lemma sin_exp_div (x : ℝ) :
    ((Real.sin x : ℝ) : ℂ)
      = (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-(Complex.I * (x : ℂ)))) / (2 * Complex.I) := by
  have h1 : Complex.exp (Complex.I * (x : ℂ)) = ↑(Real.cos x) + ↑(Real.sin x) * Complex.I := by
    rw [mul_comm, Complex.exp_ofReal_mul_I]
  have h2 : Complex.exp (-(Complex.I * (x : ℂ))) = ↑(Real.cos x) - ↑(Real.sin x) * Complex.I := by
    rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [h1, h2]
  field_simp
  ring

lemma sin_eq_exp (x : ℝ) :
    ((Real.sin x : ℝ) : ℂ)
      = (Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-(Complex.I * (x : ℂ)))) * (2 * Complex.I)⁻¹ := by
  rw [← div_eq_mul_inv]; exact sin_exp_div x

/-! ### Final arithmetic -/

lemma arith_bound (s : ℂ) {A : ℝ} (hA : 1 ≤ A) (hAt : |s.im| < A) :
    A ^ (-s.re) / (A - s.im) + A ^ (-s.re) / (A + s.im)
      ≤ 2 * A ^ (-s.re) / (A - |s.im|) + 2 * A ^ (-s.re - 1) := by
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hrp : (0 : ℝ) < A ^ (-s.re) := Real.rpow_pos_of_pos hApos _
  have hAtm : (0 : ℝ) < A - s.im := by linarith [le_abs_self s.im]
  have hAtp : (0 : ℝ) < A + s.im := by linarith [neg_abs_le s.im]
  have hAmt : (0 : ℝ) < A - |s.im| := sub_pos.mpr hAt
  have hmain : A ^ (-s.re) / (A - s.im) + A ^ (-s.re) / (A + s.im)
      ≤ 2 * A ^ (-s.re) / (A - |s.im|) := by
    rw [div_add_div _ _ (ne_of_gt hAtm) (ne_of_gt hAtp),
        div_le_div_iff₀ (by positivity) hAmt]
    have hfac : A ^ (-s.re) * (A + s.im) + (A - s.im) * A ^ (-s.re)
        = A ^ (-s.re) * (2 * A) := by ring
    rw [hfac]
    nlinarith [hrp, sq_abs s.im, abs_nonneg s.im, hAt,
      mul_le_mul_of_nonneg_left (le_of_lt hAt) (abs_nonneg s.im)]
  have hnonneg : (0 : ℝ) ≤ 2 * A ^ (-s.re - 1) := by positivity
  linarith

/-! ### The target bound -/

theorem sinIntegralTailBalanced {s : ℂ} (hs0 : 0 < s.re) {A : ℝ} (hA : 1 ≤ A) (hAt : |s.im| < A) :
    ‖∫ v in Set.Ioi A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖
      ≤ 2 * A ^ (-s.re) / (A - |s.im|) + 2 * A ^ (-s.re - 1) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  set F1 : ℝ → ℂ := fun x => Complex.exp (Complex.I * (x : ℂ)) * (x : ℂ) ^ (-s - 1) with hF1def
  set F2 : ℝ → ℂ := fun x => Complex.exp (-(Complex.I * (x : ℂ))) * (x : ℂ) ^ (-s - 1) with hF2def
  have hxpos : ∀ x ∈ Set.Ioi A, 0 < x := fun x hx => lt_of_lt_of_le hApos (le_of_lt hx)
  have hxpos' : ∀ x ∈ Set.Ici A, 0 < x := fun x hx => lt_of_lt_of_le hApos hx
  have hxt1 : ∀ x ∈ Set.Ioi A, s.im < x := fun x hx =>
    lt_of_le_of_lt (le_abs_self s.im) (lt_of_lt_of_le hAt (le_of_lt hx))
  have hxt2 : ∀ x ∈ Set.Ioi A, -s.im < x := fun x hx =>
    lt_of_le_of_lt (neg_le_abs s.im) (lt_of_lt_of_le hAt (le_of_lt hx))
  have hxt1' : ∀ x ∈ Set.Ici A, s.im < x := fun x hx =>
    lt_of_le_of_lt (le_abs_self s.im) (lt_of_lt_of_le hAt hx)
  have hxt2' : ∀ x ∈ Set.Ici A, -s.im < x := fun x hx =>
    lt_of_le_of_lt (neg_le_abs s.im) (lt_of_lt_of_le hAt hx)
  have hxne : ∀ x ∈ Set.Ici A, x ≠ 0 := fun x hx => ne_of_gt (hxpos' x hx)
  have hxtm : ∀ x ∈ Set.Ici A, x - s.im ≠ 0 := fun x hx => ne_of_gt (by linarith [hxt1' x hx])
  have hxtp : ∀ x ∈ Set.Ici A, x + s.im ≠ 0 := fun x hx => ne_of_gt (by linarith [hxt2' x hx])
  have hF1int : IntegrableOn F1 (Set.Ioi A) :=
    (hint1 s hs0 hA hAt).congr_fun (fun x hx => (phase1Id s (hxpos x hx) (hxt1 x hx)).symm)
      measurableSet_Ioi
  have hF2int : IntegrableOn F2 (Set.Ioi A) :=
    (hint2 s hs0 hA hAt).neg.congr_fun
      (fun x hx => by
        change -(((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ))) = F2 x
        rw [phase2Id s (hxpos x hx) (hxt2 x hx), neg_neg])
      measurableSet_Ioi
  have hb1 : ‖∫ x in Set.Ioi A, F1 x‖ ≤ 2 * gg1 s A := by
    rw [show ∫ x in Set.Ioi A, F1 x
        = ∫ x in Set.Ioi A,
            ((gg1 s x * psi1 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi1 s x : ℝ) : ℂ)) from
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => phase1Id s (hxpos x hx) (hxt1 x hx))]
    exact oscSharpIoi (fun x hx => phi1_hasDerivAt s (hxne x hx)) (psi1_cont s hApos)
      (fun x hx => gg1_hasDerivAt s (hxne x hx) (hxtm x hx)) (gg1'_cont s hApos hAt)
      (fun x hx => gg1_nonneg s (hxpos' x hx) (hxt1' x hx))
      (fun x hx => gg1'_nonpos s (hxpos' x hx) (hxt1' x hx) hs0)
      (hint1 s hs0 hA hAt)
  have hb2 : ‖∫ x in Set.Ioi A, F2 x‖ ≤ 2 * gg2 s A := by
    have hI2eq : ∫ x in Set.Ioi A, F2 x
        = -∫ x in Set.Ioi A,
            ((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ)) := by
      rw [show ∫ x in Set.Ioi A, F2 x
            = ∫ x in Set.Ioi A,
                -(((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ))) from
          setIntegral_congr_fun measurableSet_Ioi
            (fun x hx => by
              change F2 x = -(((gg2 s x * psi2 s x : ℝ) : ℂ) * Complex.exp (Complex.I * ((phi2 s x : ℝ) : ℂ)))
              rw [phase2Id s (hxpos x hx) (hxt2 x hx), neg_neg])]
      rw [integral_neg]
    rw [hI2eq, norm_neg]
    exact oscSharpIoi (fun x hx => phi2_hasDerivAt s (hxne x hx)) (psi2_cont s hApos)
      (fun x hx => gg2_hasDerivAt s (hxne x hx) (hxtp x hx)) (gg2'_cont s hApos hAt)
      (fun x hx => gg2_nonneg s (hxpos' x hx) (hxt2' x hx))
      (fun x hx => gg2'_nonpos s (hxpos' x hx) (hxt2' x hx) hs0)
      (hint2 s hs0 hA hAt)
  have hpoint : Set.EqOn (fun x => ((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x => (2 * Complex.I)⁻¹ * (F1 x - F2 x)) (Set.Ioi A) := by
    intro x hx
    have hsin := sin_eq_exp x
    simp only [hF1def, hF2def]
    rw [hsin]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [integral_const_mul, integral_sub hF1int hF2int]
  rw [norm_mul]
  have h2Inorm : ‖(2 * Complex.I : ℂ)⁻¹‖ = (1 : ℝ) / 2 := by
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one]
    norm_num
  rw [h2Inorm]
  calc (1 / 2) * ‖(∫ x in Set.Ioi A, F1 x) - ∫ x in Set.Ioi A, F2 x‖
      ≤ (1 / 2) * (‖∫ x in Set.Ioi A, F1 x‖ + ‖∫ x in Set.Ioi A, F2 x‖) := by
        apply mul_le_mul_of_nonneg_left (norm_sub_le _ _); norm_num
    _ ≤ (1 / 2) * (2 * gg1 s A + 2 * gg2 s A) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hb1, hb2]
    _ = gg1 s A + gg2 s A := by ring
    _ ≤ 2 * A ^ (-s.re) / (A - |s.im|) + 2 * A ^ (-s.re - 1) := by
        rw [show gg1 s A = A ^ (-s.re) / (A - s.im) from rfl,
            show gg2 s A = A ^ (-s.re) / (A + s.im) from rfl]
        exact arith_bound s hA hAt

end Work.ZeroDensity.Zeta
