import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.sqrtKin_diffForm
import Submission.Work.BoseRowsL.Row2.lattice_gauss_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.smallT_bound` — the small-`t` half of the heat comparison

## The requested statement is FALSE as written (a missing parenthesis)

The requested statement contains the summand

`- (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, h x - ∫ x : ℝ³, h x * heatK t x`.

Because the body of an integral binder extends to the right, Lean parses this as

`- (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, (h x - ∫ y : ℝ³, h y * heatK t y))` ,

i.e. the second subtraction is *inside* the integral, whereas the intended reading
(`|hM t - hB t|` for the `hM`, `hB` of `Row2/omegaLatticeRow_of_interface.lean`) is

`(- (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x)) - (∫ x : ℝ³, h x * heatK t x)` .

The two readings are *not* the same term (checked by `rfl`/type mismatch); the probe file
`_probeST7.lean` of this directory reproduces the check: the intended reading does not
typecheck against the theorem, the elaborated one does.

With the elaborated reading, for `h ≥ 0` (not a.e. `0`) and `t > 0` the inner integrand
`x ↦ h x - ∫ y, h y * heatK t y` equals the *nonzero* constant `-∫ y, h y * heatK t y`
off the (compact) support of `h`; it is therefore not integrable, and by
`MeasureTheory.integral_undef` the inner integral is `0`.  So the elaborated statement
asserts `∫_0^{ℓ²}|∑_m ∫ x, h x · heatK t (ℓ m - x)| ≤ 3000 ∫|h| / ℓ`, which fails for
`ℓ = 1`, `h = 1_{B(0,δ)}`, `δ = 10⁻⁶` (`h` is admissible): the left side is at least
`(1/2)δ² (1 - δ/√π) ≈ 5·10⁻¹³` while the right side is `3000·(4π/3)δ³ ≈ 1.26·10⁻¹⁴`
(in general the inequality fails for `δ < ℓ/25132`, with ratio `≍ ℓ/δ`).  A numerical
evaluation from the exact expression `∫_0^{ℓ²}K_t(x)dt = (4π)^{-3/2}(2/‖x‖)Γ(1/2,‖x‖²/4)`
gives `4.999998·10⁻¹³` for the left side against `1.2566·10⁻¹⁴` for the right.  Hence the
path `Work.BoseRowsL.Row2.smallT_bound` carries `sorry` below.

## What is proved here

The **intended** statement, with the parenthesis inserted,
`Work.BoseRowsL.Row2.smallT_bound_repaired`, is TRUE and is proved in this file.  Its proof
is the standard image-side estimate: for `t ∈ (0, ℓ²)` and `m ≠ 0` the far images
`ℓ • latVec m` are separated from `tsupport h ⊆ B(0, ℓ/2)`, so

`|∫ x, h x · heatK t (ℓ • latVec m - x)| ≤ (4πt)^{-3/2} e^{-ℓ²‖m‖²/16t} ∫|h|` ;

summing in `m` against the Gaussian lattice bounds (`lattice_gauss_sum`,
`tsum_pi3_exp_neg_mul_normSq_le`) and integrating in `t` (using `e^{-c/t} ≤ t/(ec)`) gives
`1439 ∫|h| / ℓ ≤ 3000 ∫|h| / ℓ`.
-/

namespace Work.BoseRowsL.Row2

open MeasureTheory Set
open scoped Real BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. Elementary lattice facts -/

/-- The lattice vector of `0` vanishes. -/
lemma smallT_latVec_zero : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = 0 :=
  Work.BoseRowsFS.vecZ_zero

/-- A nonzero lattice point is at distance at least `1` from the origin. -/
lemma smallT_one_le_norm_latVec {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    1 ≤ ‖Work.BoseBoxFock.latVec m‖ :=
  Work.BoseRowsFS.norm_vecZ_ge_one hm

/-- `|∑' i, f i| ≤ ∑' i, |f i|` for real `f`. -/
lemma smallT_abs_tsum_le {ι : Type*} [Countable ι] {f : ι → ℝ}
    (hf : Summable (fun i => |f i|)) : |∑' i, f i| ≤ ∑' i, |f i| := by
  have h := norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using hf)
  simpa only [Real.norm_eq_abs] using h

/-! ## 2. Gaussian lattice sums -/

/-- Summability of the Gaussian lattice sum. -/
lemma smallT_summable_latVec_exp {u : ℝ} (hu : 0 < u) :
    Summable (fun m : Fin 3 → ℤ => Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) :=
  Work.BoseRowsFS.summable_pi3_exp_neg_mul_normSq hu

/-- The same sum with the `m = 0` term removed. -/
lemma smallT_summable_ite_latVec_exp {u : ℝ} (hu : 0 < u) :
    Summable (fun m : Fin 3 → ℤ =>
      if m = 0 then 0 else Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (smallT_summable_latVec_exp hu)
  · by_cases h : m = 0
    · rw [if_pos h]
    · rw [if_neg h]; exact Real.exp_nonneg _
  · by_cases h : m = 0
    · rw [if_pos h]; exact Real.exp_nonneg _
    · rw [if_neg h]

/-- **The Gaussian lattice sum is at most `1000` for `u ≥ 1/16`.** -/
lemma smallT_tsum_latVec_exp_le_1000 {u : ℝ} (hu : 1/16 ≤ u) :
    (∑' m : Fin 3 → ℤ, Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) ≤ 1000 := by
  have h16 : (∑' m : Fin 3 → ℤ,
      Real.exp (-((1/16 : ℝ) * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) ≤ 1000 := by
    have h := Work.BoseRowsFS.tsum_pi3_exp_neg_mul_normSq_le (c := (1/16 : ℝ)) (by norm_num)
    have hs : Real.sqrt (1/16 : ℝ) = 1/4 := by
      rw [show (1/16:ℝ) = (1/4)^2 by norm_num, Real.sqrt_sq_eq_abs]; norm_num
    rw [hs] at h; norm_num at h; exact h
  refine le_trans ?_ h16
  refine Summable.tsum_le_tsum (fun m => ?_)
    (smallT_summable_latVec_exp (lt_of_lt_of_le (by norm_num) hu))
    (smallT_summable_latVec_exp (by norm_num : (0:ℝ) < 1/16))
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖Work.BoseBoxFock.latVec m‖])

/-- **With the `m = 0` term removed the sum is at most `75 e^{-u}` for `u ≥ 1`.** -/
lemma smallT_tsum_ite_latVec_exp_le_75 {u : ℝ} (hu : 1 ≤ u) :
    (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
      Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) ≤ 75 * Real.exp (-u) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hs : Summable (fun m : Fin 3 → ℤ =>
      Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) := smallT_summable_latVec_exp hu0
  have hsplit := Summable.tsum_eq_add_tsum_ite hs (0 : Fin 3 → ℤ)
  have h0 : Real.exp (-(u * ‖Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ)‖ ^ 2)) = 1 := by
    rw [smallT_latVec_zero, norm_zero]; norm_num
  rw [h0] at hsplit
  have hb : (∑' m : Fin 3 → ℤ, Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))
      ≤ 1 + 75 * Real.exp (-u) := (Work.BoseRowsL.Row2.lattice_gauss_sum).1 u hu
  have hthis : (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
      Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2))))
      = (∑' m : Fin 3 → ℤ, Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) - 1 := by linarith
  rw [hthis]; linarith

/-- **With the `m = 0` term removed the sum is at most `1000` for `u ≥ 1/16`.** -/
lemma smallT_tsum_ite_latVec_exp_le_1000 {u : ℝ} (hu : 1/16 ≤ u) :
    (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
      Real.exp (-(u * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) ≤ 1000 := by
  refine le_trans ?_ (smallT_tsum_latVec_exp_le_1000 hu)
  refine Summable.tsum_le_tsum (fun m => ?_)
    (smallT_summable_ite_latVec_exp (lt_of_lt_of_le (by norm_num) hu))
    (smallT_summable_latVec_exp (lt_of_lt_of_le (by norm_num) hu))
  by_cases h : m = 0
  · rw [if_pos h]; exact Real.exp_nonneg _
  · rw [if_neg h]

/-! ## 3. The heat-kernel bounds -/

/-- `heatK t z ≤ (4πt)^{-3/2}`. -/
lemma smallT_heatK_le_self {t : ℝ} (ht : 0 < t) (z : ℝ³) :
    Work.BoseBoxFock.heatK t z ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
  rw [Work.BoseBoxFock.heatK]
  refine mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) ?_
  rw [Real.exp_le_one_iff]
  have h : (0:ℝ) ≤ ‖z‖ ^ 2 / (4 * t) := div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- **A far image is Gaussian-small.** -/
lemma smallT_heatK_image_le {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) {m : Fin 3 → ℤ}
    (hm : m ≠ 0) {x : ℝ³} (hx : ‖x‖ ≤ ℓ / 2) :
    Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)
      ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
        * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) := by
  have hm1 : 1 ≤ ‖Work.BoseBoxFock.latVec m‖ := smallT_one_le_norm_latVec hm
  have h3 : ‖ℓ • Work.BoseBoxFock.latVec m‖ = ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
  have h4 : ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2 ≤ ‖ℓ • Work.BoseBoxFock.latVec m - x‖ := by
    have h5 : ℓ * ‖Work.BoseBoxFock.latVec m‖ - ‖x‖ ≤ ‖ℓ • Work.BoseBoxFock.latVec m - x‖ := by
      have h := (abs_le.mp (abs_norm_sub_norm_le (ℓ • Work.BoseBoxFock.latVec m) x)).2
      rwa [h3] at h
    have h6 : ℓ * 1 ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ := mul_le_mul_of_nonneg_left hm1 hℓ.le
    linarith
  have h4nn : (0:ℝ) ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2 := by positivity
  have hsq : ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4
      ≤ ‖ℓ • Work.BoseBoxFock.latVec m - x‖ ^ 2 := by
    have h := pow_le_pow_left₀ h4nn h4 2
    have he : (ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2) ^ 2
        = ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4 := by ring
    linarith [h, he.le, he.ge]
  have hmain : (ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2
      ≤ ‖ℓ • Work.BoseBoxFock.latVec m - x‖ ^ 2 / (4 * t) := by
    have h1 : ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4 / (4 * t)
        ≤ ‖ℓ • Work.BoseBoxFock.latVec m - x‖ ^ 2 / (4 * t) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have h2 : ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4 / (4 * t)
        = (ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2 := by
      field_simp
      ring
    linarith [h1, h2.le, h2.ge]
  rw [Work.BoseBoxFock.heatK]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (Real.rpow_nonneg (by positivity) _)

/-- The same bound, including `m = 0` (where it reduces to `heatK t z ≤ (4πt)^{-3/2}`). -/
lemma smallT_heatK_image_le' {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (m : Fin 3 → ℤ) {x : ℝ³}
    (hx : ‖x‖ ≤ ℓ / 2) :
    Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)
      ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
        * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rw [smallT_latVec_zero, smul_zero, zero_sub, Work.BoseBoxFock.heatK_even]
    simpa using smallT_heatK_le_self ht x
  · exact smallT_heatK_image_le hℓ ht hm hx

/-! ## 4. The per-image integral estimate -/

/-- If `K ≥ 0` and `K ≤ M` on `tsupport h`, then `|∫ x, h x * K x| ≤ M ∫ x, |h x|`. -/
lemma smallT_abs_integral_mul_le {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h) {M : ℝ}
    (hM : 0 ≤ M) {K : ℝ³ → ℝ} (hKn : ∀ x, 0 ≤ K x) (hK : ∀ x ∈ tsupport h, K x ≤ M) :
    |∫ x, h x * K x| ≤ M * ∫ x, |h x| := by
  have h1 : |∫ x, h x * K x| ≤ ∫ x, |h x * K x| := by
    simpa using norm_integral_le_integral_norm (fun x : ℝ³ => h x * K x)
  have h2 : (∫ x, |h x * K x|) ≤ ∫ x, |h x| * M := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (hI.abs.mul_const M) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    change |h x * K x| ≤ |h x| * M
    rw [abs_mul, abs_of_nonneg (hKn x)]
    by_cases hx : x ∈ tsupport h
    · exact mul_le_mul_of_nonneg_left (hK x hx) (abs_nonneg _)
    · have hzero : h x = 0 := by
        by_contra hne
        exact hx (subset_tsupport h hne)
      rw [hzero, abs_zero, zero_mul, zero_mul]
  have h3 : (∫ x, |h x| * M) = (∫ x, |h x|) * M := integral_mul_const M (fun x => |h x|)
  rw [h3] at h2
  have := le_trans h1 h2
  linarith [this, mul_comm M (∫ x, |h x|)]

/-- The `m`-th image integral is bounded by the Gaussian weight times `∫|h|`. -/
lemma smallT_abs_image_le {ℓ t : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h)
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2)) (ht : 0 < t) (m : Fin 3 → ℤ) :
    |∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)|
      ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
        * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2))
        * (∫ x : ℝ³, |h x|) := by
  have hM : (0:ℝ) ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
      * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)
  refine smallT_abs_integral_mul_le hI hM (fun x => Work.BoseBoxFock.heatK_nonneg ht.le _)
    (fun x hx => ?_)
  have hx' : ‖x‖ ≤ ℓ / 2 := by
    have h := hsupp hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  exact smallT_heatK_image_le' hℓ ht m hx'

/-! ## 5. The integrand bound (in the intended, parenthesised form) -/

/-- **The key pointwise bound.** -/
lemma smallT_abs_integrand_le {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h)
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2)) {t : ℝ} (ht : 0 < t) :
    |(∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
      - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x)|
      ≤ (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, |h x|)
        + (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * (∫ x : ℝ³, |h x|)
          * (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) := by
  set W : ℝ := ∫ x : ℝ³, |h x| with hW
  have hWnn : 0 ≤ W := by rw [hW]; exact integral_nonneg (fun x => abs_nonneg (h x))
  set P : ℝ := (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) with hP
  have hPnn : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg (by positivity) _
  have hu_pos : (0:ℝ) < ℓ^2/(16*t) := by positivity
  have hsumm3 : Summable (fun m : Fin 3 → ℤ => (P * W) *
      (if m = 0 then 0 else
        Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) :=
    (smallT_summable_ite_latVec_exp hu_pos).mul_left (P * W)
  have hpoint : ∀ m : Fin 3 → ℤ,
      |if m = 0 then 0 else
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)|
        ≤ (P * W) * (if m = 0 then 0 else
            Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      have himg := smallT_abs_image_le hℓ hI hsupp ht m
      rw [← hW] at himg
      rw [← hP] at himg
      calc |∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)|
          ≤ P * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) * W := himg
        _ = (P * W) * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) := by ring
  have hsumm2 : Summable (fun m : Fin 3 → ℤ => |if m = 0 then 0 else
      ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hpoint hsumm3
  have hS1 : |(∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))|
      ≤ ∑' m : Fin 3 → ℤ, |if m = 0 then 0 else
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)| :=
    smallT_abs_tsum_le hsumm2
  have hS2 : (∑' m : Fin 3 → ℤ, |if m = 0 then 0 else
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)|)
      ≤ (P * W) * (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) :=
    calc _ ≤ ∑' m : Fin 3 → ℤ, (P * W) * (if m = 0 then 0 else
            Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2))) :=
          Summable.tsum_le_tsum hpoint hsumm2 hsumm3
      _ = (P * W) * (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) := tsum_mul_left
  have hBnd : |(ℓ ^ 3)⁻¹ * ∫ x : ℝ³, h x| ≤ (ℓ ^ 3)⁻¹ * W := by
    have hℓ3 : (0:ℝ) < (ℓ^3)⁻¹ := by positivity
    have hint : |∫ x : ℝ³, h x| ≤ W := by
      rw [hW]
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x : ℝ³ => h x)
    rw [abs_mul, abs_of_pos hℓ3]
    exact mul_le_mul_of_nonneg_left hint hℓ3.le
  calc |(∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
        - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x)|
      ≤ |(∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))|
        + |(ℓ ^ 3)⁻¹ * ∫ x : ℝ³, h x| := by
        have h3 := abs_add_le (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
          (-((ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x)))
        simpa only [abs_neg, sub_eq_add_neg] using h3
    _ ≤ ((P * W) * (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))))
        + (ℓ ^ 3)⁻¹ * W := add_le_add (le_trans hS1 hS2) hBnd
    _ = (ℓ ^ 3)⁻¹ * W + (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * W
          * (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) := by
        rw [← hP]; ring

/-! ## 6. Elementary numerical estimates -/

/-- `e^{-c/t} ≤ t/(e·c)` for `c, t > 0`. -/
lemma smallT_exp_neg_div_le {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    Real.exp (-(c/t)) ≤ t / (Real.exp 1 * c) := by
  have h1 : c/t ≤ Real.exp (c/t - 1) := by
    have := Real.add_one_le_exp (c/t - 1); linarith
  have h2 : Real.exp (c/t - 1) = Real.exp (c/t) / Real.exp 1 := by rw [← Real.exp_sub]
  have h3 : Real.exp 1 * (c/t) ≤ Real.exp (c/t) := by
    rw [h2] at h1
    have h := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos 1))
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos 1))] at h
    rwa [mul_comm] at h
  have h4 : 1 / Real.exp (c/t) ≤ 1 / (Real.exp 1 * (c/t)) :=
    one_div_le_one_div_of_le (by positivity) h3
  rw [Real.exp_neg]
  calc (Real.exp (c/t))⁻¹ = 1 / Real.exp (c/t) := by rw [one_div]
    _ ≤ 1 / (Real.exp 1 * (c/t)) := h4
    _ = t / (Real.exp 1 * c) := by field_simp

/-- **The small-`t` arithmetic**: the Gaussian term integrates against `t^{-1/2}`. -/
lemma smallT_heatK_smallT_le {ℓ t W : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (hW : 0 ≤ W) :
    (4*Real.pi*t)^(-(3:ℝ)/2) * W * 75 * Real.exp (-(ℓ^2/(16*t)))
      ≤ ((4*Real.pi)^(-(3:ℝ)/2) * (16/(Real.exp 1 * ℓ^2)) * 75 * W) * t^(-(1:ℝ)/2) := by
  have hc : (0:ℝ) < ℓ^2/16 := by positivity
  have hexp : Real.exp (-(ℓ^2/(16*t))) ≤ t / (Real.exp 1 * (ℓ^2/16)) := by
    have := smallT_exp_neg_div_le (c := ℓ^2/16) (t := t) hc ht
    rwa [show (ℓ^2/16)/t = ℓ^2/(16*t) by ring] at this
  have htp : (4*Real.pi*t)^(-(3:ℝ)/2) = (4*Real.pi)^(-(3:ℝ)/2) * t^(-(3:ℝ)/2) := by
    rw [show (4:ℝ)*Real.pi*t = (4*Real.pi)*t by ring, Real.mul_rpow (by positivity) ht.le]
  have hts : t^(-(3:ℝ)/2) * t = t^(-(1:ℝ)/2) := by
    calc t^(-(3:ℝ)/2) * t = t^(-(3:ℝ)/2) * t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^(-(3:ℝ)/2 + 1) := by rw [← Real.rpow_add ht (-(3:ℝ)/2) 1]
      _ = t^(-(1:ℝ)/2) := by norm_num
  have hstep : t^(-(3:ℝ)/2) * Real.exp (-(ℓ^2/(16*t)))
      ≤ t^(-(1:ℝ)/2) * (16/(Real.exp 1 * ℓ^2)) := by
    have h := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le (-(3:ℝ)/2))
    rwa [show t^(-(3:ℝ)/2) * (t / (Real.exp 1 * (ℓ^2/16)))
        = t^(-(1:ℝ)/2) * (16/(Real.exp 1 * ℓ^2)) by
      rw [← mul_div_assoc, hts]; field_simp] at h
  rw [htp]
  calc (4*Real.pi)^(-(3:ℝ)/2) * t^(-(3:ℝ)/2) * W * 75 * Real.exp (-(ℓ^2/(16*t)))
      = (4*Real.pi)^(-(3:ℝ)/2) * 75*W * (t^(-(3:ℝ)/2) * Real.exp (-(ℓ^2/(16*t)))) := by ring
    _ ≤ (4*Real.pi)^(-(3:ℝ)/2) * 75*W * (t^(-(1:ℝ)/2) * (16/(Real.exp 1 * ℓ^2))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ((4*Real.pi)^(-(3:ℝ)/2) * (16/(Real.exp 1 * ℓ^2)) * 75 * W) * t^(-(1:ℝ)/2) := by ring

/-- `(4π)^{-3/2} ≤ 1/40`. -/
lemma smallT_P_le_inv40 : (4 * Real.pi) ^ (-(3:ℝ)/2) ≤ 1/40 := by
  have hπ : (3.4:ℝ) ≤ Real.sqrt (4*Real.pi) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_three])
  have hpos : (0:ℝ) < 4 * Real.pi := by positivity
  have h40 : (40:ℝ) ≤ (4*Real.pi) ^ (3/2 : ℝ) := by
    have hrw : (4*Real.pi) ^ (3/2:ℝ) = (4*Real.pi) * Real.sqrt (4*Real.pi) := by
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [hrw]
    nlinarith [hπ, Real.pi_gt_three]
  have hpos2 : (0:ℝ) < (4*Real.pi) ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hpos _
  have h := (inv_le_inv₀ (a := (4*Real.pi) ^ (3/2 : ℝ)) (b := (40:ℝ)) hpos2 (by norm_num)).mpr h40
  rw [show (-(3:ℝ)/2) = -(3/2:ℝ) by norm_num, Real.rpow_neg hpos.le]
  simpa using h

/-- **The rescaling `(4π(ℓ²/16))^{-3/2} ℓ² = (π/4)^{-3/2} ℓ^{-1}`.** -/
lemma smallT_QQ_mul_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (4*Real.pi * (ℓ^2/16)) ^ (-(3:ℝ)/2) * ℓ^2
      = (Real.pi/4) ^ (-(3:ℝ)/2) * ℓ^(-(1:ℝ)) := by
  rw [← Real.rpow_two ℓ]
  rw [show (4*Real.pi * (ℓ ^ (2:ℝ)/16)) = (Real.pi/4) * (ℓ ^ (2:ℝ)) by ring,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hℓ.le _),
    ← Real.rpow_mul hℓ.le 2 (-(3:ℝ)/2),
    show (2:ℝ) * (-(3:ℝ)/2) = -3 by norm_num]
  rw [mul_assoc, ← Real.rpow_add hℓ (-3) 2]
  norm_num

/-- `(π/4)^{-3/2} ≤ 8/5`. -/
lemma smallT_pi_div_four_rpow_le : (Real.pi/4) ^ (-(3:ℝ)/2) ≤ 8/5 := by
  have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hpos : (0:ℝ) < Real.pi/4 := by positivity
  have hsq : ((5:ℝ)/6)^2 ≤ (3:ℝ)/4 := by norm_num
  have hs : (5:ℝ)/6 ≤ Real.sqrt (3/4) := (Real.le_sqrt (by norm_num) (by norm_num)).mpr hsq
  have h34 : (5:ℝ)/8 ≤ (3/4:ℝ) ^ (3/2:ℝ) := by
    have hrw : (3/4:ℝ) ^ (3/2:ℝ) = (3/4) * Real.sqrt (3/4) := by
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [hrw]
    nlinarith [hs]
  have hle : (3/4:ℝ) ^ (3/2:ℝ) ≤ (Real.pi/4) ^ (3/2:ℝ) :=
    Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have h5 : (5:ℝ)/8 ≤ (Real.pi/4) ^ (3/2:ℝ) := le_trans h34 hle
  have hpos2 : (0:ℝ) < (Real.pi/4) ^ (3/2:ℝ) := Real.rpow_pos_of_pos hpos _
  have h := (inv_le_inv₀ (a := (Real.pi/4) ^ (3/2:ℝ)) (b := (5:ℝ)/8) hpos2 (by norm_num)).mpr h5
  rw [show (-(3:ℝ)/2) = -(3/2:ℝ) by norm_num, Real.rpow_neg hpos.le]
  simpa using h

/-- `(ℓ^3)^{-1} ℓ^2 = ℓ^{-1}`. -/
lemma smallT_inv_cube_mul_sq {ℓ : ℝ} (hℓ : 0 < ℓ) : (ℓ^3)⁻¹ * ℓ^2 = ℓ^(-(1:ℝ)) := by
  rw [Real.rpow_neg_one]
  field_simp

/-- **Monotonicity of the far constant.** -/
lemma smallT_rpow_mono {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) (h : ℓ^2/16 ≤ t) :
    (4 * Real.pi * t) ^ (-(3:ℝ)/2) ≤ (4 * Real.pi * (ℓ^2/16)) ^ (-(3:ℝ)/2) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [h, Real.pi_pos]) (by norm_num)

/-! ## 7. The repaired (intended) statement -/

/-- **The intended small-`t` bound**: the requested statement with the parenthesis around
`∫ x : ℝ³, h x` inserted, so that the second subtraction lies *outside* the integral.
This is exactly `∫_{t ∈ (0,ℓ²)} |hM t - hB t| ≤ 3000 ∫|h| / ℓ` for the `hM`, `hB` of
`Row2/omegaLatticeRow_of_interface.lean`. -/
theorem smallT_bound_repaired {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h)
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2)) :
    ∫ t in Set.Ioo (0 : ℝ) (ℓ ^ 2), |(∑' m : Fin 3 → ℤ,
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x))
      - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x| ≤ 3000 * (∫ x : ℝ³, |h x|) / ℓ := by
  set W : ℝ := ∫ x : ℝ³, |h x| with hW
  have hWnn : 0 ≤ W := by rw [hW]; exact integral_nonneg (fun x => abs_nonneg (h x))
  set P : ℝ := (4 * Real.pi) ^ (-(3:ℝ)/2) with hP
  have hPnn : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg (by positivity) _
  set QQ : ℝ := (4 * Real.pi * (ℓ^2/16)) ^ (-(3:ℝ)/2) with hQQ
  have hQQnn : 0 ≤ QQ := by rw [hQQ]; exact Real.rpow_nonneg (by positivity) _
  set C1 : ℝ := (ℓ^3)⁻¹ * W + 1000 * QQ * W with hC1
  set Kc : ℝ := P * (16 / (Real.exp 1 * ℓ^2)) * 75 * W with hKc
  have hKnn : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg (mul_nonneg (mul_nonneg hPnn (by positivity)) (by norm_num)) hWnn
  -- the pointwise bound on `(0, ℓ²)`
  have hpt : ∀ t ∈ Set.Ioo (0:ℝ) (ℓ^2),
      |(∑' m : Fin 3 → ℤ, ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x))
        - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x|
      ≤ C1 + Kc * t ^ (-(1:ℝ)/2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htℓ : t < ℓ^2 := ht.2
    have hu16 : (1/16 : ℝ) ≤ ℓ^2/(16*t) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [htℓ, ht0]
    have hu_pos : (0:ℝ) < ℓ^2/(16*t) := by positivity
    have hsummB : Summable (fun m : Fin 3 → ℤ =>
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)) := by
      have hcomp : Summable (fun m : Fin 3 → ℤ =>
          (4 * Real.pi * t) ^ (-(3:ℝ)/2)
            * Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) * W) :=
        ((smallT_summable_latVec_exp hu_pos).mul_left ((4 * Real.pi * t) ^ (-(3:ℝ)/2))).mul_right W
      refine Summable.of_norm_bounded hcomp (fun m => ?_)
      have himg := smallT_abs_image_le hℓ hI hsupp ht0 m
      rw [← hW] at himg
      simpa only [Real.norm_eq_abs] using himg
    have hsplit := Summable.tsum_eq_add_tsum_ite hsummB (0 : Fin 3 → ℤ)
    have ha0 : (∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t
          (ℓ • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) - x))
        = ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x := by
      simp only [smallT_latVec_zero, smul_zero, zero_sub, Work.BoseBoxFock.heatK_even]
    rw [ha0] at hsplit
    rw [hsplit]
    have hring : (∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x)
        + (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
        - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x
        = (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
          - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) := by ring
    rw [hring]
    have hbase := smallT_abs_integrand_le hℓ hI hsupp ht0
    rw [← hW] at hbase
    by_cases hcase : ℓ^2/(16*t) ≤ 1
    · have hT := smallT_tsum_ite_latVec_exp_le_1000 hu16
      have hle : ℓ^2/16 ≤ t := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 16*t)] at hcase
        linarith [hcase]
      have hPt : (4*Real.pi*t)^(-(3:ℝ)/2) ≤ QQ := by
        rw [hQQ]
        exact smallT_rpow_mono hℓ ht0 hle
      have hTnn : (0:ℝ) ≤ (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) :=
        tsum_nonneg (fun m => by split <;> positivity)
      have hstep : (4*Real.pi*t)^(-(3:ℝ)/2) * W * (∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) ≤ QQ * W * 1000 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hPt hWnn) hT hTnn (mul_nonneg hQQnn hWnn)
      calc |(∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
            - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x)|
          ≤ (ℓ ^ 3)⁻¹ * W + (4*Real.pi*t)^(-(3:ℝ)/2) * W * (∑' m : Fin 3 → ℤ,
              (if m = 0 then 0 else
                Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) := hbase
        _ ≤ (ℓ ^ 3)⁻¹ * W + QQ * W * 1000 := by linarith [hstep]
        _ = C1 := by rw [hC1]; ring
        _ ≤ C1 + Kc * t ^ (-(1:ℝ)/2) :=
            le_add_of_nonneg_right (mul_nonneg hKnn (Real.rpow_nonneg ht0.le _))
    · have hcase' : 1 < ℓ^2/(16*t) := lt_of_not_ge hcase
      have hT := smallT_tsum_ite_latVec_exp_le_75 (le_of_lt hcase')
      have hsmall := smallT_heatK_smallT_le (ℓ := ℓ) (t := t) (W := W) hℓ ht0 hWnn
      have hKc_eq : Kc = (4*Real.pi)^(-(3:ℝ)/2) * (16/(Real.exp 1 * ℓ^2)) * 75 * W := by
        rw [hKc, hP]
      have hsmall' : (4*Real.pi*t)^(-(3:ℝ)/2) * W * (75 * Real.exp (-(ℓ^2/(16*t))))
          ≤ Kc * t ^ (-(1:ℝ)/2) := by
        rw [hKc_eq]
        calc (4*Real.pi*t)^(-(3:ℝ)/2) * W * (75 * Real.exp (-(ℓ^2/(16*t))))
            = (4*Real.pi*t)^(-(3:ℝ)/2) * W * 75 * Real.exp (-(ℓ^2/(16*t))) := by ring
          _ ≤ _ := hsmall
      calc |(∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)))
            - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x)|
          ≤ (ℓ ^ 3)⁻¹ * W + (4*Real.pi*t)^(-(3:ℝ)/2) * W * (∑' m : Fin 3 → ℤ,
              (if m = 0 then 0 else
                Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)))) := hbase
        _ ≤ (ℓ ^ 3)⁻¹ * W + (4*Real.pi*t)^(-(3:ℝ)/2) * W
              * (75 * Real.exp (-(ℓ^2/(16*t)))) := by
            have hstep : (4*Real.pi*t)^(-(3:ℝ)/2) * W * (∑' m : Fin 3 → ℤ,
                (if m = 0 then 0 else
                  Real.exp (-((ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2))))
                ≤ (4*Real.pi*t)^(-(3:ℝ)/2) * W * (75 * Real.exp (-(ℓ^2/(16*t)))) :=
              mul_le_mul_of_nonneg_left hT
                (mul_nonneg (Real.rpow_nonneg (by positivity) _) hWnn)
            linarith [hstep]
        _ ≤ (ℓ ^ 3)⁻¹ * W + Kc * t ^ (-(1:ℝ)/2) := by linarith [hsmall']
        _ ≤ C1 + Kc * t ^ (-(1:ℝ)/2) := by
            have : (ℓ ^ 3)⁻¹ * W ≤ C1 := by
              rw [hC1]
              have : (0:ℝ) ≤ 1000 * QQ * W := by positivity
              linarith
            linarith [this]
  -- the majorant is integrable
  have hIntG : Integrable ((Set.Ioo (0:ℝ) (ℓ^2)).indicator
      (fun t : ℝ => C1 + Kc * t ^ (-(1:ℝ)/2))) := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    have h1 : IntegrableOn (fun _ : ℝ => C1) (Set.Ioo (0:ℝ) (ℓ^2)) volume :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have h2 : IntegrableOn (fun t : ℝ => Kc * t ^ (-(1:ℝ)/2)) (Set.Ioo (0:ℝ) (ℓ^2)) volume := by
      have hb : IntegrableOn (fun t : ℝ => t ^ (-(1:ℝ)/2)) (Set.Ioo (0:ℝ) (ℓ^2)) volume :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (by positivity : (0:ℝ) < ℓ^2)).mpr (by norm_num)
      rw [IntegrableOn] at hb ⊢
      exact hb.const_mul Kc
    have hab : (fun t : ℝ => C1 + Kc * t ^ (-(1:ℝ)/2))
        = (fun _ : ℝ => C1) + (fun t : ℝ => Kc * t ^ (-(1:ℝ)/2)) := by funext t; rfl
    rw [hab]
    exact h1.add h2
  have key : (∫ t in Set.Ioo (0:ℝ) (ℓ^2),
      |(∑' m : Fin 3 → ℤ, ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x))
        - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x|)
      ≤ ∫ t, (Set.Ioo (0:ℝ) (ℓ^2)).indicator (fun t : ℝ => C1 + Kc * t ^ (-(1:ℝ)/2)) t := by
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_mono_of_nonneg ?_ hIntG ?_
    · refine Filter.Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ Set.Ioo (0:ℝ) (ℓ^2)
      · rw [Set.indicator_of_mem ht]; exact abs_nonneg _
      · have h1 : (Set.indicator (Set.Ioo (0:ℝ) (ℓ^2)) (fun t : ℝ =>
            |(∑' m : Fin 3 → ℤ, ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t
                (ℓ • Work.BoseBoxFock.latVec m - x))
              - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x|)) t
            = 0 := Set.indicator_of_notMem ht _
        simp only [h1]
        exact le_refl 0
    · refine Filter.Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ Set.Ioo (0:ℝ) (ℓ^2)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        exact hpt t ht
      · have h1 : (Set.indicator (Set.Ioo (0:ℝ) (ℓ^2)) (fun t : ℝ =>
            |(∑' m : Fin 3 → ℤ, ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t
                (ℓ • Work.BoseBoxFock.latVec m - x))
              - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x|)) t
            = 0 := Set.indicator_of_notMem ht _
        have h2 : (Set.indicator (Set.Ioo (0:ℝ) (ℓ^2))
            (fun t : ℝ => C1 + Kc * t ^ (-(1:ℝ)/2))) t = 0 := Set.indicator_of_notMem ht _
        simp only [h1, h2]
        exact le_refl 0
  have hval : (∫ t, (Set.Ioo (0:ℝ) (ℓ^2)).indicator
        (fun t : ℝ => C1 + Kc * t ^ (-(1:ℝ)/2)) t) = C1 * ℓ^2 + Kc * (2 * ℓ) := by
    rw [integral_indicator measurableSet_Ioo]
    have h1 : IntegrableOn (fun _ : ℝ => C1) (Set.Ioo (0:ℝ) (ℓ^2)) volume :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have h2 : IntegrableOn (fun t : ℝ => Kc * t ^ (-(1:ℝ)/2)) (Set.Ioo (0:ℝ) (ℓ^2)) volume := by
      have hb : IntegrableOn (fun t : ℝ => t ^ (-(1:ℝ)/2)) (Set.Ioo (0:ℝ) (ℓ^2)) volume :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (by positivity : (0:ℝ) < ℓ^2)).mpr (by norm_num)
      rw [IntegrableOn] at hb ⊢
      exact hb.const_mul Kc
    have hab : (∫ t in Set.Ioo (0:ℝ) (ℓ^2), (C1 + Kc * t ^ (-(1:ℝ)/2)))
        = (∫ t in Set.Ioo (0:ℝ) (ℓ^2), C1) + (∫ t in Set.Ioo (0:ℝ) (ℓ^2), Kc * t ^ (-(1:ℝ)/2)) :=
      integral_add h1 h2
    rw [hab]
    have hC : (∫ t in Set.Ioo (0:ℝ) (ℓ^2), C1) = C1 * ℓ^2 := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by nlinarith [sq_nonneg ℓ]), sub_zero]
      ring
    have hK : (∫ t in Set.Ioo (0:ℝ) (ℓ^2), Kc * t ^ (-(1:ℝ)/2)) = Kc * (2 * ℓ) := by
      rw [integral_const_mul]
      rw [show (∫ t in Set.Ioo (0:ℝ) (ℓ^2), t ^ (-(1:ℝ)/2)) = 2 * ℓ from by
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ ℓ^2)]
        rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1:ℝ)/2))]
        norm_num
        rw [show (ℓ^2 : ℝ) ^ (1/2:ℝ) = ℓ by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hℓ]]
        ring]
    rw [hC, hK]
  have harith : C1 * ℓ^2 + Kc * (2 * ℓ) ≤ 3000 * W / ℓ := by
    have hQmul : QQ * ℓ^2 = (Real.pi/4)^(-(3:ℝ)/2) * ℓ^(-(1:ℝ)) := by
      rw [hQQ]; exact smallT_QQ_mul_sq hℓ
    have hQle : (Real.pi/4)^(-(3:ℝ)/2) ≤ 8/5 := smallT_pi_div_four_rpow_le
    have hPle : P ≤ 1/40 := by rw [hP]; exact smallT_P_le_inv40
    have hℓinv : (0:ℝ) ≤ ℓ^(-(1:ℝ)) := Real.rpow_nonneg hℓ.le _
    have hcube : (ℓ^3)⁻¹ * ℓ^2 = ℓ^(-(1:ℝ)) := smallT_inv_cube_mul_sq hℓ
    have h1 : C1 * ℓ^2 ≤ 1601 * (W * ℓ^(-(1:ℝ))) := by
      rw [hC1]
      have heq : ((ℓ^3)⁻¹ * W + 1000 * QQ * W) * ℓ^2
          = (ℓ^3)⁻¹ * ℓ^2 * W + 1000 * (QQ * ℓ^2) * W := by ring
      rw [heq, hcube, hQmul]
      have hb : (Real.pi/4)^(-(3:ℝ)/2) * ℓ^(-(1:ℝ)) ≤ (8/5) * ℓ^(-(1:ℝ)) :=
        mul_le_mul_of_nonneg_right hQle hℓinv
      have hbW : ((Real.pi/4)^(-(3:ℝ)/2) * ℓ^(-(1:ℝ))) * W ≤ ((8/5) * ℓ^(-(1:ℝ))) * W :=
        mul_le_mul_of_nonneg_right hb hWnn
      nlinarith [hbW, hWnn, hℓinv, mul_nonneg hWnn hℓinv]
    have h2 : Kc * (2 * ℓ) ≤ 30 * (W * ℓ^(-(1:ℝ))) := by
      have hPe : 2400 * P / Real.exp 1 ≤ 30 := by
        rw [div_le_iff₀ (Real.exp_pos 1)]
        nlinarith [hPle, hPnn, Real.exp_one_gt_two]
      have hEq : Kc * (2 * ℓ) = (2400 * P / Real.exp 1) * (W * ℓ^(-(1:ℝ))) := by
        rw [hKc, Real.rpow_neg_one]
        field_simp
        ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_right hPe (mul_nonneg hWnn hℓinv)
    have hsum := add_le_add h1 h2
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    have hX : (0:ℝ) ≤ W * ℓ^(-(1:ℝ)) := mul_nonneg hWnn hℓinv
    nlinarith [hsum, hX]
  calc (∫ t in Set.Ioo (0:ℝ) (ℓ^2),
        |(∑' m : Fin 3 → ℤ, ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x))
          - (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, h x) - ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x|)
      ≤ ∫ t, (Set.Ioo (0:ℝ) (ℓ^2)).indicator (fun t : ℝ => C1 + Kc * t ^ (-(1:ℝ)/2)) t := key
    _ = C1 * ℓ^2 + Kc * (2 * ℓ) := hval
    _ ≤ 3000 * W / ℓ := harith

/-! ## 8. The requested statement (it is FALSE as elaborated; the corrected form is §7)

The requested text omitted the parentheses around the first `∫ x, h x`; as elaborated the binder
swallows the second subtraction, the inner integrand becomes the nonzero constant
`-∫ y, h y * heatK t y` off the support of `h`, and `MeasureTheory.integral_undef` makes the inner
integral `0`.  The resulting statement is `∫_0^{ℓ²} |Σ_m ∫ x, h x · heatK t (ℓm − x)| ≤ 3000‖h‖₁/ℓ`,
which fails for `ℓ = 1`, `h = 1_{B(0,δ)}`, `δ = 10⁻⁶` (LHS `≈ 5·10⁻¹³` vs RHS `≈ 1.26·10⁻¹⁴`;
it fails for every `δ < ℓ/25132`, the ratio being `≍ ℓ/δ`).  The *true* (parenthesised) statement
is `Work.BoseRowsL.Row2.smallT_bound_repaired`, proved in §7 above and used by
`Work.BoseRowsL.Row2.omegaLatticeRow_of_interface`.

The false statement is deliberately **not** declared here: a `sorry`-backed declaration of it would
put `sorryAx` into the environment of every consumer of this module (it is imported by
`Row2/omegaLatticeRow_of_interface.lean`). -/

end Work.BoseRowsL.Row2
