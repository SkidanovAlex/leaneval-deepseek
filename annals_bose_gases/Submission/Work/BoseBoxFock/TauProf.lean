import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.TauProf` — an explicit smooth monotone kinetic profile `τ̃`

This module proves `Work.BoseBoxFock.exists_tauProf`: there is a `C^∞` monotone profile
`φ : ℝ → ℝ` with

* `(max 0 (r-2))^2 ≤ φ r ≤ (max 0 (r-1))^2`,
* `φ r = 0` for `r ≤ 1`,
* `φ r = (r - 3/2)^2 + c₀` for `r ≥ 2`, with `c₀ ≥ 0`.

It is the profile used to smooth FS's kinked kinetic symbol `def:tau` (see
`BOSE_BOXFOCK_LEAD.md` §2.2).  The construction is the convolution `(·₊)² ⋆ K` of the
kink `(·₊)²` with a smooth normalised bump `K` supported in `[-1/4, 1/4]`, evaluated at
`r - 3/2`: smoothness is `HasCompactSupport.contDiff_convolution_right`, and the three
requirements above are the integral identities `∫K = 1`, `∫t K = 0` (evenness) and
`0 ≤ ∫t²K ≤ 1/16` (support in `[-1/4,1/4]`).

The bump is Mathlib's `ContDiffBump.normed` at `rIn = 1/8`, `rOut = 1/4`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-! ## 1. The smoothing kernel -/

/-- A smooth bump with support in `[-1/4,1/4]` (`rIn = 1/8`, `rOut = 1/4`). -/
noncomputable def tauBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / 8, rOut := 1 / 4, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The normalised smoothing kernel: `K = tauBump / ∫ tauBump`, so `∫ K = 1`. -/
noncomputable def tauKer (t : ℝ) : ℝ := tauBump.normed volume t

lemma tauKer_def (t : ℝ) : tauKer t = tauBump t / ∫ s, tauBump s := rfl

lemma tauKer_contDiff : ContDiff ℝ (⊤ : ℕ∞) tauKer := tauBump.contDiff_normed

lemma tauKer_continuous : Continuous tauKer := tauBump.continuous_normed

lemma tauKer_hasCompactSupport : HasCompactSupport tauKer := tauBump.hasCompactSupport_normed

lemma tauKer_nonneg (t : ℝ) : 0 ≤ tauKer t := tauBump.nonneg_normed t

lemma tauKer_integral : ∫ t, tauKer t = 1 := tauBump.integral_normed

lemma tauKer_neg (t : ℝ) : tauKer (-t) = tauKer t := tauBump.normed_neg t

/-- `K` vanishes off the ball of radius `1/4`. -/
lemma tauKer_eq_zero_of (t : ℝ) (ht : 1 / 4 ≤ |t|) : tauKer t = 0 := by
  rw [tauKer_def]
  have h : tauBump t = 0 := by
    apply ContDiffBump.zero_of_le_dist (f := tauBump)
    rw [Real.dist_eq, sub_zero]
    exact ht
  rw [h, zero_div]

lemma tauKer_integrable : Integrable tauKer volume := tauBump.integrable_normed

/-- Integrability of `p · K` for any continuous `p`. -/
lemma tauKer_mul_integrable (p : ℝ → ℝ) (hp : Continuous p) :
    Integrable (fun t => p t * tauKer t) :=
  (hp.mul tauKer_continuous).integrable_of_hasCompactSupport
    (tauKer_hasCompactSupport.mul_left)

lemma tauKer_abs_lt (t : ℝ) (h : tauKer t ≠ 0) : |t| < 1 / 4 :=
  not_le.1 fun hc => h (tauKer_eq_zero_of t hc)

/-- The kernel is even, so its first moment vanishes. -/
lemma tauKer_moment1 : ∫ t, t * tauKer t = 0 := by
  set F : ℝ → ℝ := fun s => s * tauKer s with hF
  have hodd : ∀ t, F (-t) = -F t := by
    intro t
    simp only [hF, tauKer_neg, neg_mul]
  have hneg : ∫ t, F (-t) = ∫ t, F t := integral_neg_eq_self F volume
  have h2 : ∫ t, F (-t) = -∫ t, F t := by
    rw [show (fun t => F (-t)) = fun t => -F t from funext hodd, integral_neg]
  linarith [hneg, h2]

lemma tauKer_moment2_nonneg : 0 ≤ ∫ t, t ^ 2 * tauKer t :=
  integral_nonneg fun t => mul_nonneg (sq_nonneg t) (tauKer_nonneg t)

lemma tauKer_moment2_le : ∫ t, t ^ 2 * tauKer t ≤ 1 / 16 := by
  have hle : ∀ t, t ^ 2 * tauKer t ≤ (1 / 16 : ℝ) * tauKer t := by
    intro t
    rcases eq_or_ne (tauKer t) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · have hlt : |t| < 1 / 4 := tauKer_abs_lt t h0
      have hsq : t ^ 2 ≤ 1 / 16 := by
        have h := abs_lt.1 hlt
        nlinarith [h.1, h.2]
      exact mul_le_mul_of_nonneg_right hsq (tauKer_nonneg t)
  calc ∫ t, t ^ 2 * tauKer t ≤ ∫ t, (1 / 16 : ℝ) * tauKer t :=
        integral_mono (tauKer_mul_integrable (fun t => t ^ 2) (by fun_prop))
          (tauKer_integrable.const_mul _) hle
    _ = (1 / 16 : ℝ) * ∫ t, tauKer t := integral_const_mul _ _
    _ = 1 / 16 := by rw [tauKer_integral, mul_one]

/-! ## 2. The kernel moment identity -/

/-- The key integral identity: the `K`-average of `(a - t)^2` is `a^2 + ∫t²K`. -/
lemma integral_sq_sub_mul (a : ℝ) :
    ∫ t, (a - t) ^ 2 * tauKer t
      = a ^ 2 * (∫ t, tauKer t) - 2 * a * (∫ t, t * tauKer t)
        + (∫ t, t ^ 2 * tauKer t) := by
  have hi0 : Integrable tauKer volume := tauKer_integrable
  have hi1 : Integrable (fun t => t * tauKer t) volume :=
    tauKer_mul_integrable (fun t => t) continuous_id
  have hi2 : Integrable (fun t => t ^ 2 * tauKer t) volume :=
    tauKer_mul_integrable (fun t => t ^ 2) (by fun_prop)
  have hA : Integrable (fun s => a ^ 2 * tauKer s) volume := hi0.const_mul _
  have hB : Integrable (fun s => (2 * a) * (s * tauKer s)) volume := hi1.const_mul _
  have hpt : ∀ t, (a - t) ^ 2 * tauKer t
      = (fun s => a ^ 2 * tauKer s) t - (fun s => (2 * a) * (s * tauKer s)) t
        + (fun s => s ^ 2 * tauKer s) t := by
    intro t; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add (f := fun t => a ^ 2 * tauKer t - (2 * a) * (t * tauKer t))
    (g := fun t => t ^ 2 * tauKer t) (hA.sub hB) hi2]
  rw [integral_sub (f := fun t => a ^ 2 * tauKer t)
    (g := fun t => (2 * a) * (t * tauKer t)) hA hB]
  have hI1 : ∫ t, a ^ 2 * tauKer t = a ^ 2 * ∫ t, tauKer t := integral_const_mul _ _
  have hI2 : ∫ t, (2 * a) * (t * tauKer t) = (2 * a) * ∫ t, t * tauKer t :=
    integral_const_mul _ _
  rw [hI1, hI2]

/-! ## 3. The profile -/

/-- The kinked profile `(·₊)^2`. -/
noncomputable def tauH (x : ℝ) : ℝ := (max 0 x) ^ 2

lemma tauH_continuous : Continuous tauH := by unfold tauH; fun_prop

lemma tauH_nonneg (x : ℝ) : 0 ≤ tauH x := sq_nonneg _

lemma tauH_mono : Monotone tauH := by
  intro x y hxy
  unfold tauH
  exact pow_le_pow_left₀ (le_max_left 0 x) (max_le_max (le_refl 0) hxy) 2

lemma tauH_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : tauH x = 0 := by
  unfold tauH
  rw [max_eq_left hx]; norm_num

/-- **The smoothed profile**: `φ r = ∫ t, (max 0 (r - 3/2 - t))^2 K t`. -/
noncomputable def tauPhi (r : ℝ) : ℝ :=
  convolution tauH tauKer (ContinuousLinearMap.mul ℝ ℝ) volume (r - 3 / 2)

lemma tauPhi_contDiff : ContDiff ℝ (⊤ : ℕ∞) tauPhi := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (convolution tauH tauKer (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    tauKer_hasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      tauH_continuous.locallyIntegrable tauKer_contDiff
  exact h.comp (by fun_prop)

/-- The profile as an integral (via the substitution `t ↦ (r-3/2) - t`). -/
lemma tauPhi_eq_integral (r : ℝ) :
    tauPhi r = ∫ t, tauH (r - 3 / 2 - t) * tauKer t := by
  have hmain : ∀ x : ℝ,
      tauH (r - 3 / 2 - x) * tauKer (r - 3 / 2 - (r - 3 / 2 - x))
        = tauH (r - 3 / 2 - x) * tauKer x := by
    intro x
    rw [show r - 3 / 2 - (r - 3 / 2 - x) = x by ring]
  have h := integral_sub_left_eq_self
    (fun s : ℝ => tauH s * tauKer (r - 3 / 2 - s)) volume (r - 3 / 2)
  rw [show (∫ x, tauH (r - 3 / 2 - x) * tauKer (r - 3 / 2 - (r - 3 / 2 - x)))
      = ∫ x, tauH (r - 3 / 2 - x) * tauKer x from
        integral_congr_ae (Filter.Eventually.of_forall hmain)] at h
  have hconv : (∫ t, (ContinuousLinearMap.mul ℝ ℝ) (tauH t) (tauKer (r - 3 / 2 - t)))
      = ∫ t, tauH t * tauKer (r - 3 / 2 - t) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => rfl)
  rw [tauPhi, convolution_def, hconv, h]

lemma tauPhi_nonneg (r : ℝ) : 0 ≤ tauPhi r := by
  rw [tauPhi_eq_integral]
  exact integral_nonneg fun t => mul_nonneg (tauH_nonneg _) (tauKer_nonneg t)

lemma tauPhi_mono : Monotone tauPhi := by
  intro r r' hrr'
  rw [tauPhi_eq_integral r, tauPhi_eq_integral r']
  refine integral_mono
    (tauKer_mul_integrable (fun t => tauH (r - 3 / 2 - t)) (tauH_continuous.comp (by fun_prop)))
    (tauKer_mul_integrable (fun t => tauH (r' - 3 / 2 - t)) (tauH_continuous.comp (by fun_prop)))
    (fun t => ?_)
  exact mul_le_mul_of_nonneg_right
    (tauH_mono (by linarith : r - 3 / 2 - t ≤ r' - 3 / 2 - t)) (tauKer_nonneg t)

lemma tauPhi_zero_of_le_one (r : ℝ) (hr : r ≤ 1) : tauPhi r = 0 := by
  rw [tauPhi_eq_integral]
  have hzero : (fun t => tauH (r - 3 / 2 - t) * tauKer t) = 0 := by
    funext t
    rcases eq_or_ne (tauKer t) 0 with h0 | h0
    · change tauH (r - 3 / 2 - t) * tauKer t = 0
      rw [h0, mul_zero]
    · rw [tauH_eq_zero_of_nonpos (by have := abs_lt.1 (tauKer_abs_lt t h0); linarith [this.1]),
        zero_mul]
      rfl
  rw [hzero]
  simp

lemma tauPhi_quad (r : ℝ) (hr : 2 ≤ r) :
    tauPhi r = (r - 3 / 2) ^ 2 + ∫ t, t ^ 2 * tauKer t := by
  rw [tauPhi_eq_integral]
  have hpt : ∀ t, tauH (r - 3 / 2 - t) * tauKer t = (r - 3 / 2 - t) ^ 2 * tauKer t := by
    intro t
    rcases eq_or_ne (tauKer t) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · unfold tauH
      rw [max_eq_right (by have := abs_lt.1 (tauKer_abs_lt t h0); linarith [this.1])]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sq_sub_mul,
    tauKer_integral, tauKer_moment1]
  ring

lemma tauPhi_ge (r : ℝ) : (max 0 (r - 2)) ^ 2 ≤ tauPhi r := by
  rcases lt_or_ge r 2 with hr | hr
  · rw [max_eq_left (by linarith : r - 2 ≤ 0)]
    simpa using tauPhi_nonneg r
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ r - 2), tauPhi_quad r hr]
    have hsq : (r - 2) ^ 2 ≤ (r - 3 / 2) ^ 2 := by nlinarith [hr]
    linarith [hsq, tauKer_moment2_nonneg]

lemma tauPhi_le (r : ℝ) : tauPhi r ≤ (max 0 (r - 1)) ^ 2 := by
  rcases lt_or_ge r 1 with hr | hr
  · rw [tauPhi_zero_of_le_one r hr.le, max_eq_left (by linarith : r - 1 ≤ 0)]
    exact sq_nonneg _
  · have hr1 : 0 ≤ r - 1 := by linarith
    rw [max_eq_right hr1, tauPhi_eq_integral]
    have hpt : ∀ t, tauH (r - 3 / 2 - t) * tauKer t ≤ (r - 1) ^ 2 * tauKer t := by
      intro t
      rcases eq_or_ne (tauKer t) 0 with h0 | h0
      · rw [h0, mul_zero, mul_zero]
      · have hx : r - 3 / 2 - t ≤ r - 1 := by
          have := abs_lt.1 (tauKer_abs_lt t h0)
          linarith [this.1]
        refine mul_le_mul_of_nonneg_right ?_ (tauKer_nonneg t)
        calc tauH (r - 3 / 2 - t) ≤ tauH (r - 1) := tauH_mono hx
          _ = (r - 1) ^ 2 := by unfold tauH; rw [max_eq_right hr1]
    calc ∫ t, tauH (r - 3 / 2 - t) * tauKer t ≤ ∫ t, (r - 1) ^ 2 * tauKer t :=
          integral_mono
            (tauKer_mul_integrable (fun t => tauH (r - 3 / 2 - t))
              (tauH_continuous.comp (by fun_prop)))
            (tauKer_integrable.const_mul _) hpt
      _ = (r - 1) ^ 2 * ∫ t, tauKer t := integral_const_mul _ _
      _ = (r - 1) ^ 2 := by rw [tauKer_integral, mul_one]

/-- **The main result**: an explicit smooth monotone kinetic profile `τ̃`. -/
theorem exists_tauProf : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ Monotone φ ∧
    (∀ r, (max 0 (r - 2)) ^ 2 ≤ φ r) ∧ (∀ r, φ r ≤ (max 0 (r - 1)) ^ 2) ∧
    (∀ r, r ≤ 1 → φ r = 0) ∧ ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ r, 2 ≤ r → φ r = (r - 3 / 2) ^ 2 + c₀ :=
  ⟨tauPhi, tauPhi_contDiff, tauPhi_mono, tauPhi_ge, tauPhi_le, tauPhi_zero_of_le_one,
    ⟨∫ t, t ^ 2 * tauKer t, tauKer_moment2_nonneg, tauPhi_quad⟩⟩

end Work.BoseBoxFock
