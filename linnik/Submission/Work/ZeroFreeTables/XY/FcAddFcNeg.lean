import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData
import Submission.Work.ZeroFreeTables.tf72conv_eq_f
import Submission.Work.ZeroFreeTables.tf72conv_even

/-!
# `FcAddFcNeg`: the Laplace transform of `g ∗ g`

For `g = xyG = tf72g (4/3)`, the even test-function density supported in `[-3/4,3/4]`,
Heath-Brown's Lemma 7.2 identity reads, in Laplace-transform form,

`Fc z + Fc (-z) = (∫ g(x) e^{-zx} dx)²`,

where `Fc = tf72Fc (4/3)` is the Laplace transform of the one-sided test function
`f = g ∗ g` (`tf72f (4/3)`) and the right-hand side is the square of the Laplace
transform of `g`.

The proof is the classical "Laplace transform of a convolution is the product of the
Laplace transforms", spelled out in two halves:

* `AcSqEqConvIntegral`: expanding the square and applying Fubini (`integral_convolution`)
  gives `(∫ g e^{-zx})² = ∫ (g ∗ g)(x) e^{-zx} dx`, where `g ∗ g = tf72conv (4/3)` is the
  two-sided convolution;
* `ConvIntegralEqFc`: the two-sided convolution is even and supported in `[-3/2,3/2]`, and
  coincides with `f` on `[0,3/2]`; splitting the full-line integral at the origin and
  substituting `x ↦ -x` on the negative half turns it into `Fc z + Fc (-z)`.
-/

open MeasureTheory Complex
open scoped BigOperators

namespace Work.ZeroFreeTables.XY

open Work.ZeroFreeTables

noncomputable section

/-! ## Support and integrability of `g` -/

lemma xyG_support_subset : Function.support xyG ⊆ Set.Icc (-(3/4) : ℝ) (3/4) := by
  intro x hx
  have hxle : |x| ≤ 3/4 := by
    by_contra h
    exact hx (xyG_supp x (le_of_lt (lt_of_not_ge h)))
  rw [Set.mem_Icc]
  exact abs_le.mp hxle

lemma xyG_hasCompactSupport : HasCompactSupport xyG :=
  HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(3/4) : ℝ) (3/4)) isCompact_Icc xyG_support_subset

lemma xyG_c_supp (z : ℂ) {x : ℝ} (hx : (3/4 : ℝ) ≤ |x|) :
    ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) = 0 := by
  rw [xyG_supp x hx, Complex.ofReal_zero, zero_mul]

lemma xyG_c_hasCompactSupport (z : ℂ) :
    HasCompactSupport (fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) :=
  HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(3/4) : ℝ) (3/4)) isCompact_Icc (fun x hx => by
      have hxle : |x| ≤ 3/4 := by
        by_contra h
        exact hx (xyG_c_supp z (le_of_lt (lt_of_not_ge h)))
      rw [Set.mem_Icc]
      exact abs_le.mp hxle)

lemma continuous_xyG_c (z : ℂ) :
    Continuous (fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) := by
  have h1 : Continuous (fun x : ℝ => ((xyG x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp xyG_cont
  have h2 : Continuous (fun x : ℝ => Complex.exp (-(z * (x : ℂ)))) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
  exact h1.mul h2

lemma integrable_xyG_c (z : ℂ) :
    Integrable (fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) volume :=
  Continuous.integrable_of_hasCompactSupport (continuous_xyG_c z) (xyG_c_hasCompactSupport z)

/-! ## Continuity of the two-sided convolution `g ∗ g` -/

lemma continuous_tf72conv : Continuous (tf72conv (4/3)) := by
  have hcont : Continuous (MeasureTheory.convolution (fun x : ℝ => xyG x) (fun x : ℝ => xyG x)
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    HasCompactSupport.continuous_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume)
      (f := fun x : ℝ => xyG x) (g := fun x : ℝ => xyG x)
      xyG_hasCompactSupport xyG_cont.locallyIntegrable xyG_cont
  exact hcont.congr (fun x => by
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rfl)

/-! ## First half: `(∫ g e^{-zx})² = ∫ (g ∗ g) e^{-zx}` -/

lemma convolution_pointwise (z : ℂ) (x : ℝ) :
    MeasureTheory.convolution
        (fun y : ℝ => ((xyG y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ))))
        (fun y : ℝ => ((xyG y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ))))
        (ContinuousLinearMap.mul ℂ ℂ) volume x
      = ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
  rw [MeasureTheory.convolution_def]
  have hpt : ∀ t : ℝ,
      (ContinuousLinearMap.mul ℂ ℂ (((xyG t : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ)))))
        (((xyG (x - t) : ℝ) : ℂ) * Complex.exp (-(z * ((x - t : ℝ) : ℂ))))
      = ((xyG t * xyG (x - t) : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
    intro t
    rw [ContinuousLinearMap.mul_apply']
    calc (((xyG t : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ)))) *
            (((xyG (x - t) : ℝ) : ℂ) * Complex.exp (-(z * ((x - t : ℝ) : ℂ))))
        = (((xyG t : ℝ) : ℂ) * ((xyG (x - t) : ℝ) : ℂ)) *
            (Complex.exp (-(z * (t : ℂ))) * Complex.exp (-(z * ((x - t : ℝ) : ℂ)))) := by
          ring
      _ = ((xyG t * xyG (x - t) : ℝ) : ℂ) *
            (Complex.exp (-(z * (t : ℂ))) * Complex.exp (-(z * ((x - t : ℝ) : ℂ)))) := by
          rw [← Complex.ofReal_mul]
      _ = ((xyG t * xyG (x - t) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ)) + -(z * ((x - t : ℝ) : ℂ))) := by
          rw [← Complex.exp_add]
      _ = ((xyG t * xyG (x - t) : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
          rw [show -(z * (t : ℂ)) + -(z * ((x - t : ℝ) : ℂ)) = -(z * (x : ℂ)) by
            push_cast; ring]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_mul_const (r := Complex.exp (-(z * (x : ℂ))))]
  rw [integral_complex_ofReal]
  rw [show (∫ t : ℝ, xyG t * xyG (x - t)) = tf72conv (4/3) x from rfl]

theorem AcSqEqConvIntegral (z : ℂ) :
    (∫ x : ℝ, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) ^ 2
      = ∫ x : ℝ, ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
  have hφ : Integrable (fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) volume :=
    integrable_xyG_c z
  have hconv := MeasureTheory.integral_convolution (μ := volume) (ν := volume)
      (L := ContinuousLinearMap.mul ℂ ℂ)
      (f := fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      (g := fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      hφ hφ
  rw [MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => convolution_pointwise z x))] at hconv
  rw [hconv, ContinuousLinearMap.mul_apply']
  ring

/-! ## Second half: `∫ (g ∗ g) e^{-zx} = Fc z + Fc (-z)` -/

lemma tf72conv_supp_Icc {x : ℝ} (hx : (3/2 : ℝ) ≤ |x|) : tf72conv (4/3) x = 0 := by
  have hzero : (fun s : ℝ => tf72g (4/3) s * tf72g (4/3) (x - s)) = fun _ : ℝ => 0 := by
    funext s
    by_cases hs : (3/4 : ℝ) ≤ |s|
    · rw [show tf72g (4/3) s = xyG s from rfl, xyG_supp s hs, zero_mul]
    · have hs' : |s| < 3/4 := lt_of_not_ge hs
      have hxs : (3/4 : ℝ) ≤ |x - s| := by
        by_contra h
        have h' : |x - s| < 3/4 := lt_of_not_ge h
        have htri : |x| ≤ |s| + |x - s| := by
          have h := abs_add_le s (x - s)
          have hx' : s + (x - s) = x := by ring
          rwa [hx'] at h
        linarith
      rw [show tf72g (4/3) (x - s) = xyG (x - s) from rfl, xyG_supp (x - s) hxs, mul_zero]
  change (∫ s : ℝ, tf72g (4/3) s * tf72g (4/3) (x - s)) = 0
  rw [hzero, MeasureTheory.integral_zero]

lemma tf72conv_eq_xyFf {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (3/2)) :
    tf72conv (4/3) x = xyFf x := by
  have h : tf72conv (4/3) x = tf72f (4/3) x :=
    tf72conv_eq_f (4/3) (by norm_num) x (by
      refine ⟨hx.1, ?_⟩
      rw [show (2 : ℝ) / (4/3) = 3/2 by norm_num]
      exact hx.2)
  rw [h]
  rfl

lemma continuous_convInt (z : ℂ) :
    Continuous (fun x : ℝ => ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) :=
  (Complex.continuous_ofReal.comp continuous_tf72conv).mul
    (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg))

lemma integral_convInt_eq (z : ℂ) :
    (∫ x : ℝ, ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = ∫ x in (-(3/2))..(3/2),
          ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc (-(3/2)) (3/2) →
      ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) = 0 := by
    intro x hx
    have hxabs : (3/2 : ℝ) ≤ |x| := by
      by_contra h
      exact hx (abs_le.mp (le_of_lt (lt_of_not_ge h)))
    rw [tf72conv_supp_Icc hxabs, Complex.ofReal_zero, zero_mul]
  rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (-(3/2) : ℝ) ≤ 3/2 by norm_num)]

lemma integral_convInt_pos (z : ℂ) :
    (∫ x in (0 : ℝ)..(3/2),
        ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = tf72Fc (4/3) z := by
  unfold tf72Fc
  rw [show (2 : ℝ) / (4/3) = 3/2 by norm_num]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 3/2 by norm_num)] at hx
  change ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))
      = Complex.exp (-(z * (x : ℂ))) * ((tf72f (4/3) x : ℝ) : ℂ)
  rw [tf72conv_eq_xyFf hx, show xyFf x = tf72f (4/3) x from rfl]
  ring

lemma integral_convInt_neg (z : ℂ) :
    (∫ x in (-(3/2))..(0 : ℝ),
        ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = tf72Fc (4/3) (-z) := by
  have hcomp : (∫ x in (-(3/2))..(0 : ℝ),
        ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = ∫ x in (0 : ℝ)..(3/2),
          ((tf72conv (4/3) (-x) : ℝ) : ℂ) * Complex.exp (-(z * ((-x : ℝ) : ℂ))) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := (3/2 : ℝ))
      (f := fun x : ℝ => ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
    rw [neg_zero] at h
    exact h.symm
  rw [hcomp]
  unfold tf72Fc
  rw [show (2 : ℝ) / (4/3) = 3/2 by norm_num]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 3/2 by norm_num)] at hu
  change ((tf72conv (4/3) (-u) : ℝ) : ℂ) * Complex.exp (-(z * ((-u : ℝ) : ℂ)))
      = Complex.exp (-((-z) * (u : ℂ))) * ((tf72f (4/3) u : ℝ) : ℂ)
  rw [tf72conv_even (4/3) (by norm_num) u, tf72conv_eq_xyFf hu,
      show xyFf u = tf72f (4/3) u from rfl]
  rw [show -(z * ((-u : ℝ) : ℂ)) = -((-z) * (u : ℂ)) by push_cast; ring]
  ring

theorem ConvIntegralEqFc (z : ℂ) :
    (∫ x : ℝ, ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = Work.ZeroFreeTables.xyT.Fc z + Work.ZeroFreeTables.xyT.Fc (-z) := by
  rw [show Work.ZeroFreeTables.xyT.Fc = tf72Fc (4/3) from rfl]
  rw [integral_convInt_eq z]
  rw [show (∫ x in (-(3/2))..(3/2),
              ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
        = (∫ x in (-(3/2))..(0 : ℝ),
              ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
          + (∫ x in (0 : ℝ)..(3/2),
              ((tf72conv (4/3) x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      from (intervalIntegral.integral_add_adjacent_intervals
            ((continuous_convInt z).intervalIntegrable (-(3/2)) 0)
            ((continuous_convInt z).intervalIntegrable 0 (3/2))).symm]
  rw [integral_convInt_neg z, integral_convInt_pos z]
  exact add_comm _ _

/-! ## The target identity -/

theorem FcAddFcNeg (z : ℂ) :
    Work.ZeroFreeTables.xyT.Fc z + Work.ZeroFreeTables.xyT.Fc (-z)
      = (∫ x : ℝ, ((Work.ZeroFreeTables.XY.xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))^2 := by
  rw [AcSqEqConvIntegral z, ConvIntegralEqFc z]

end

end Work.ZeroFreeTables.XY
