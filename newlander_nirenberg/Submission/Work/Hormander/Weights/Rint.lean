/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The weighted integral `rint` and the real pairing `rpair0`

`rint φ U = ∫ U e^{-φ}` is the basic real functional; `normSq0 φ u = rint φ (‖u‖²)` and
`pairing0 φ u v = ∫ u conj v e^{-φ}` are the two ways of pairing functions.  For the
Kohn–Morrey identity it is convenient to use the *real* pairing
`rpair0 φ u v = rint φ (Re (u conj v))`, which is symmetric and `ℝ`-bilinear; every quantity
in the identity is real once one takes real parts, and the antisymmetrisation of
`(0,2)`-forms then involves no conjugation.
-/
import Submission.Work.Hormander.Weights.Defs

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-! ### The integrand `U * e^{-φ}` -/

lemma continuous_wn {φ : Cn n → ℝ} (hφ : Continuous φ) : Continuous (wn n φ) :=
  Real.continuous_exp.comp (continuous_neg.comp hφ)

lemma integrable_wn_mul {φ : Cn n → ℝ} {U : Cn n → ℝ} (hφ : Continuous φ)
    (hU : Continuous U) (hsU : HasCompactSupport U) :
    Integrable (fun z => U z * wn n φ z) :=
  (hU.mul (continuous_wn hφ)).integrable_of_hasCompactSupport (hsU.mul_right)

/-! ### Algebra of `rint` -/

lemma rint_congr {φ : Cn n → ℝ} {U V : Cn n → ℝ} (h : ∀ z, U z = V z) :
    rint φ U = rint φ V := by
  unfold rint
  congr 1
  exact funext fun z => by rw [h z]

lemma rint_add {φ : Cn n → ℝ} {U V : Cn n → ℝ}
    (hU : Integrable (fun z => U z * wn n φ z)) (hV : Integrable (fun z => V z * wn n φ z)) :
    rint φ (fun z => U z + V z) = rint φ U + rint φ V := by
  unfold rint
  rw [← integral_add hU hV]
  congr 1
  exact funext fun z => by ring

lemma rint_sub {φ : Cn n → ℝ} {U V : Cn n → ℝ}
    (hU : Integrable (fun z => U z * wn n φ z)) (hV : Integrable (fun z => V z * wn n φ z)) :
    rint φ (fun z => U z - V z) = rint φ U - rint φ V := by
  unfold rint
  rw [← integral_sub hU hV]
  congr 1
  exact funext fun z => by ring

lemma rint_neg {φ : Cn n → ℝ} {U : Cn n → ℝ} :
    rint φ (fun z => -U z) = -rint φ U := by
  unfold rint
  rw [← integral_neg]
  congr 1
  exact funext fun z => by ring

lemma rint_const_mul {φ : Cn n → ℝ} (c : ℝ) (U : Cn n → ℝ) :
    rint φ (fun z => c * U z) = c * rint φ U := by
  unfold rint
  rw [← integral_const_mul]
  congr 1
  exact funext fun z => by ring

lemma rint_sum {φ : Cn n → ℝ} {ι : Type*} (s : Finset ι) {U : ι → Cn n → ℝ}
    (hU : ∀ i ∈ s, Integrable (fun z => U i z * wn n φ z)) :
    rint φ (fun z => ∑ i ∈ s, U i z) = ∑ i ∈ s, rint φ (U i) := by
  unfold rint
  rw [← integral_finset_sum s hU]
  congr 1
  exact funext fun z => by rw [Finset.sum_mul]

lemma integrable_rint_const_mul {φ : Cn n → ℝ} (c : ℝ) {U : Cn n → ℝ}
    (h : Integrable (fun z => U z * wn n φ z)) :
    Integrable (fun z => (c * U z) * wn n φ z) := by
  refine (h.const_mul c).congr ?_
  filter_upwards with z
  ring

lemma integrable_rint_sum {φ : Cn n → ℝ} {ι : Type*} (s : Finset ι) {U : ι → Cn n → ℝ}
    (h : ∀ i ∈ s, Integrable (fun z => U i z * wn n φ z)) :
    Integrable (fun z => (∑ i ∈ s, U i z) * wn n φ z) := by
  refine (integrable_finset_sum s h).congr ?_
  filter_upwards with z
  rw [Finset.sum_mul]

lemma rint_nonneg {φ : Cn n → ℝ} {U : Cn n → ℝ} (hU : ∀ z, 0 ≤ U z) : 0 ≤ rint φ U := by
  unfold rint
  exact integral_nonneg fun z => mul_nonneg (hU z) (le_of_lt (wn_pos φ z))

lemma rint_mono {φ : Cn n → ℝ} {U V : Cn n → ℝ} (h : ∀ z, U z ≤ V z)
    (hU : Integrable (fun z => U z * wn n φ z)) (hV : Integrable (fun z => V z * wn n φ z)) :
    rint φ U ≤ rint φ V := by
  have h0 : rint φ (fun z => V z - U z) = rint φ V - rint φ U := rint_sub hV hU
  have h1 : 0 ≤ rint φ (fun z => V z - U z) := rint_nonneg fun z => sub_nonneg.mpr (h z)
  linarith [h0 ▸ h1]

/-! ### Pointwise real parts of products of conjugates -/

private lemma star_eq_starRingEnd (a : ℂ) : star a = (starRingEnd ℂ) a := rfl

lemma re_mul_star (a b : ℂ) : (a * star b).re = a.re * b.re + a.im * b.im := by
  rw [star_eq_starRingEnd, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma re_mul_star_self (a : ℂ) : (a * star a).re = ‖a‖ ^ 2 := by
  rw [re_mul_star, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

lemma re_mul_ofReal (a : ℂ) (r : ℝ) : (a * (r : ℂ)).re = a.re * r := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

lemma re_mul_star_comm (a b : ℂ) : (a * star b).re = (b * star a).re := by
  rw [re_mul_star, re_mul_star]
  ring

private lemma re_mul_star_add_left (a b c : ℂ) :
    ((a + b) * star c).re = (a * star c).re + (b * star c).re := by
  rw [add_mul, Complex.add_re]

private lemma re_mul_star_sub_left (a b c : ℂ) :
    ((a - b) * star c).re = (a * star c).re - (b * star c).re := by
  rw [sub_mul, Complex.sub_re]

private lemma re_mul_star_add_right (a b c : ℂ) :
    (a * star (b + c)).re = (a * star b).re + (a * star c).re := by
  rw [star_add, mul_add, Complex.add_re]

private lemma re_mul_star_sub_right (a b c : ℂ) :
    (a * star (b - c)).re = (a * star b).re - (a * star c).re := by
  rw [star_sub, mul_sub, Complex.sub_re]

/-! ### The real pairing `rpair0` -/

lemma rpair0_congr_left {φ : Cn n → ℝ} {u u' v : Form0 n} (h : ∀ z, u z = u' z) :
    rpair0 φ u v = rpair0 φ u' v :=
  rint_congr fun z => by rw [h z]

lemma rpair0_congr_right {φ : Cn n → ℝ} {u v v' : Form0 n} (h : ∀ z, v z = v' z) :
    rpair0 φ u v = rpair0 φ u v' :=
  rint_congr fun z => by rw [h z]

lemma rpair0_add_left {φ : Cn n → ℝ} {u w v : Form0 n}
    (hu : Integrable (fun z => (u z * star (v z)).re * wn n φ z))
    (hw : Integrable (fun z => (w z * star (v z)).re * wn n φ z)) :
    rpair0 φ (u + w) v = rpair0 φ u v + rpair0 φ w v := by
  have h : (fun z => ((u + w) z * star (v z)).re)
      = fun z => (u z * star (v z)).re + (w z * star (v z)).re :=
    funext fun z => re_mul_star_add_left (u z) (w z) (v z)
  unfold rpair0
  rw [h, rint_add hu hw]

lemma rpair0_sub_left {φ : Cn n → ℝ} {u w v : Form0 n}
    (hu : Integrable (fun z => (u z * star (v z)).re * wn n φ z))
    (hw : Integrable (fun z => (w z * star (v z)).re * wn n φ z)) :
    rpair0 φ (u - w) v = rpair0 φ u v - rpair0 φ w v := by
  have h : (fun z => ((u - w) z * star (v z)).re)
      = fun z => (u z * star (v z)).re - (w z * star (v z)).re :=
    funext fun z => re_mul_star_sub_left (u z) (w z) (v z)
  unfold rpair0
  rw [h, rint_sub hu hw]

lemma rpair0_add_right {φ : Cn n → ℝ} {u v w : Form0 n}
    (hv : Integrable (fun z => (u z * star (v z)).re * wn n φ z))
    (hw : Integrable (fun z => (u z * star (w z)).re * wn n φ z)) :
    rpair0 φ u (v + w) = rpair0 φ u v + rpair0 φ u w := by
  have h : (fun z => (u z * star ((v + w) z)).re)
      = fun z => (u z * star (v z)).re + (u z * star (w z)).re :=
    funext fun z => re_mul_star_add_right (u z) (v z) (w z)
  unfold rpair0
  rw [h, rint_add hv hw]

lemma rpair0_sub_right {φ : Cn n → ℝ} {u v w : Form0 n}
    (hv : Integrable (fun z => (u z * star (v z)).re * wn n φ z))
    (hw : Integrable (fun z => (u z * star (w z)).re * wn n φ z)) :
    rpair0 φ u (v - w) = rpair0 φ u v - rpair0 φ u w := by
  have h : (fun z => (u z * star ((v - w) z)).re)
      = fun z => (u z * star (v z)).re - (u z * star (w z)).re :=
    funext fun z => re_mul_star_sub_right (u z) (v z) (w z)
  unfold rpair0
  rw [h, rint_sub hv hw]

lemma rpair0_sum_left {φ : Cn n → ℝ} {ι : Type*} (s : Finset ι) {u : ι → Form0 n}
    {v : Form0 n} (h : ∀ i ∈ s, Integrable (fun z => (u i z * star (v z)).re * wn n φ z)) :
    rpair0 φ (∑ i ∈ s, u i) v = ∑ i ∈ s, rpair0 φ (u i) v := by
  have hcongr : (fun z => ((∑ i ∈ s, u i) z * star (v z)).re)
      = fun z => ∑ i ∈ s, (u i z * star (v z)).re := by
    funext z
    rw [Finset.sum_apply, Finset.sum_mul, Complex.re_sum]
  unfold rpair0
  rw [hcongr, rint_sum s h]

lemma rpair0_smul_left {φ : Cn n → ℝ} (c : ℝ) (u v : Form0 n) :
    rpair0 φ (c • u) v = c * rpair0 φ u v := by
  have h : (fun z => ((c • u) z * star (v z)).re)
      = fun z => c * (u z * star (v z)).re := by
    funext z
    show (c * u z * star (v z)).re = c * (u z * star (v z)).re
    rw [mul_assoc, Complex.re_ofReal_mul]
  unfold rpair0
  rw [h, rint_const_mul]

/-- `rpair0 φ u u` is the (real) square norm of `u`. -/
lemma rpair0_self {φ : Cn n → ℝ} (u : Form0 n) : rpair0 φ u u = normSq0 φ u := by
  unfold rpair0 rint normSq0
  congr 1
  funext z
  show (u z * star (u z)).re * wn n φ z = ‖u z‖ ^ 2 * wn n φ z
  rw [re_mul_star_self]

/-- `rpair0 φ` is symmetric. -/
lemma rpair0_comm {φ : Cn n → ℝ} (u v : Form0 n) : rpair0 φ u v = rpair0 φ v u := by
  unfold rpair0
  congr 1
  exact funext fun z => re_mul_star_comm (u z) (v z)

/-- `rpair0` is the real part of the Hermitian pairing `pairing0`. -/
lemma rpair0_eq_re_pairing {φ : Cn n → ℝ} {u v : Form0 n}
    (h : Integrable (fun z => u z * star (v z) * wn n φ z)) :
    (pairing0 φ u v).re = rpair0 φ u v := by
  have hre : (pairing0 φ u v).re = ∫ z, (u z * star (v z) * wn n φ z).re := by
    unfold pairing0
    simpa using (integral_re (𝕜 := ℂ) h).symm
  rw [hre]
  unfold rpair0 rint
  congr 1
  funext z
  exact re_mul_ofReal (u z * star (v z)) (wn n φ z)

end Work.Hormander.Weights
