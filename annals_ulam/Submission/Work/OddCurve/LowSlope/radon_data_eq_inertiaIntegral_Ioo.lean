import Mathlib
import Submission.Work.OddCurve.LowSlope.CruxStatements
import Submission.Work.OddCurve.LowSlope.radon_data_interface
import Submission.Work.OddCurve.LowSlope.section_ibp
import Submission.Work.OddRadon.Core

/-!
# `radon_data_eq_inertiaIntegral_Ioo`

The one-dimensional spherical-Radon identity of Prop. `workHARD1` (the inertia data of a body of
revolution are the second moments of its central sections), in the form the low-slope pipeline
consumes, but with the profile only assumed `C¹` on the **open** interval `(-1,1)` instead of the
closed `[-1,1]`.

The proof of `Work.OddCurve.LowSlope.RadonDataEqInertiaIntegral` (`radon_data_identity.lean`) and
of `Work.OddCurve.LowSlope.radonProfile_data_eq_inertiaIntegral` (`radon_data_interface.lean`) only
ever differentiates `f` at points strictly inside the chord `(-(x s), y s) ⊆ (-1, 1)`, so the
closed-interval hypothesis is not needed.  This file reproduces those two proofs with the open
hypothesis:

* `section_ibp_Ioo` — `SectionIBP` with `ContDiffOn ℝ 1 f (Ioo (-1) 1)`;
* `radon_data_Ioo_form` — the identity in `radonProfile`-free form;
* `radon_data_eq_inertiaIntegral_Ioo` — the requested statement.

This weakening matters: a profile meeting the axis with a vertical tangent (the semicircle at
`t = ±1`) is `C¹` on `(-1,1)` but not on `[-1,1]`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- `x ^ n * √x = x ^ (n + 1/2)` for `x ≥ 0` (local copy of the private helper of
`LowSlope/section_ibp.lean`). -/
private lemma pow_mul_sqrt_eq_rpow' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.sqrt x = x ^ ((n : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x n]
  exact (Real.rpow_add' hx (by positivity)).symm

/-- **The integration-by-parts identity of Prop. `workHARD1`**, with the profile only `C¹` on the
open interval `(-1,1)`. -/
theorem section_ibp_Ioo (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) (x y s : ℝ)
    (hs : 0 < s) (hf : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1))
    (hx : -(x) ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hxy : -(x) < y)
    (hfy : f y = s * y) (hfx : f (-(x)) = -(s * (-(x))))
    (hpos : ∀ t ∈ Set.Ioo (-(x)) y, 0 < rad0 f s t)
    (hintA : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x)) y)
    (hintB : IntervalIntegrable (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(x)) y) :
    (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
      = (2 * (n : ℝ) + 2) * (∫ t in (-(x))..y, t ^ 2 * rad0 f s t ^ (n - 1) *
        Real.sqrt (rad0 f s t)) := by
  have hfcont : ContinuousOn f (Set.Ioo (-1 : ℝ) 1) := hf.continuousOn
  have hx0 : -1 < -(x) := hx.1
  have hy1 : y < 1 := hy.2
  -- the radicand
  set R : ℝ → ℝ := fun t => rad0 f s t with hR
  have hRy : R y = 0 := by
    simp only [hR, rad0, hfy]; ring
  have hRx : R (-(x)) = 0 := by
    simp only [hR, rad0]; rw [hfx]; ring
  -- differentiability of `f` strictly inside the chord
  have hfd : ∀ t ∈ Set.Ioo (-(x)) y, HasDerivAt f (deriv f t) t := by
    intro t ht
    have ht1 : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx0 ht.1, lt_trans ht.2 hy1⟩
    exact ((hf.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds ht1)).hasDerivAt
  -- the derivative of the radicand
  have hRd : ∀ t ∈ Set.Ioo (-(x)) y, HasDerivAt R (2 * f t * deriv f t - 2 * s ^ 2 * t) t := by
    intro t ht
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    have h1 : HasDerivAt (fun u : ℝ => f u ^ 2) (2 * f t * deriv f t) t := by
      have hh := (hfd t ht).pow 2
      refine hh.congr_deriv ?_
      rw [h21, pow_one]; ring
    have h2 : HasDerivAt (fun u : ℝ => (s * u) ^ 2) (2 * s ^ 2 * t) t := by
      have hbase : HasDerivAt (fun u : ℝ => s * u) s t := by
        simpa using (hasDerivAt_id t).const_mul s
      have hh : HasDerivAt (fun u : ℝ => (s * u) * (s * u)) (s * (s * t) + (s * t) * s) t :=
        hbase.mul hbase
      have hh2 : HasDerivAt (fun u : ℝ => (s * u) ^ 2) (s * (s * t) + (s * t) * s) t :=
        hh.congr_of_eventuallyEq (Eventually.of_forall (fun u => pow_two (s * u)))
      refine hh2.congr_deriv ?_
      ring
    have h3 : HasDerivAt (fun u : ℝ => f u ^ 2 - (s * u) ^ 2)
        (2 * f t * deriv f t - 2 * s ^ 2 * t) t := h1.sub h2
    have hfun : R = fun u : ℝ => f u ^ 2 - (s * u) ^ 2 := by
      funext u; simp only [hR, rad0]
    rw [hfun]
    exact h3
  -- rewrite the two integrands of the statement in terms of `R`
  have hAeq : (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
      Real.sqrt (rad0 f s t))
      = (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) / Real.sqrt (R t)) := by
    funext t; simp only [hR]
  have hBeq : (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
      = (fun t : ℝ => t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t)) := by
    funext t; simp only [hR]
  rw [hAeq, hBeq]
  have hintA' : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      R t ^ (n - 1) / Real.sqrt (R t)) volume (-(x)) y := by
    rw [← hAeq]; exact hintA
  have hintB' : IntervalIntegrable (fun t : ℝ => t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t))
      volume (-(x)) y := by
    rw [← hBeq]; exact hintB
  -- the exponent `p = (n-1) + 1/2`
  have hp : (((n - 1 : ℕ) : ℝ) + 1 / 2) = (2 * (n : ℝ) - 1) / 2 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  -- the primitive
  set F : ℝ → ℝ := fun t => t ^ 3 * (R t ^ (n - 1) * Real.sqrt (R t)) with hF
  have hpoint : ∀ t ∈ Set.Ioo (-(x)) y,
      HasDerivAt F ((2 * (n : ℝ) + 2) * (t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))) t := by
    intro t ht
    have hr : 0 < R t := hpos t ht
    have hrne : R t ≠ 0 := ne_of_gt hr
    -- chain rule through `y ↦ y ^ p`
    have hin : HasDerivAt (fun u : ℝ => R u ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
        ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
          (2 * f t * deriv f t - 2 * s ^ 2 * t)) t :=
      (Real.hasDerivAt_rpow_const (Or.inl hrne)).comp t (hRd t ht)
    -- the positivity of `R` nearby
    have hRcontAt : ContinuousAt R t := by
      have h1 : ContinuousAt (fun u : ℝ => f u ^ 2 - (s * u) ^ 2) t :=
        (((hfcont.continuousAt (isOpen_Ioo.mem_nhds
            ⟨lt_trans hx0 ht.1, lt_trans ht.2 hy1⟩)).pow 2).sub
          (((continuous_const.mul continuous_id).continuousAt).pow 2))
      refine h1.congr ?_
      filter_upwards with u
      simp only [hR, rad0]
    have hnear : ∀ᶠ u in 𝓝 t, 0 < R u := hRcontAt.eventually (isOpen_Ioi.mem_nhds hr)
    have hsmooth : HasDerivAt (fun u : ℝ => R u ^ (n - 1) * Real.sqrt (R u))
        ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
          (2 * f t * deriv f t - 2 * s ^ 2 * t)) t := by
      refine hin.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with u hu
      exact pow_mul_sqrt_eq_rpow' hu.le (n - 1)
    have hFd := (((hasDerivAt_id t).pow 3).mul hsmooth)
    have hFun : F = fun u : ℝ => u ^ 3 * (R u ^ (n - 1) * Real.sqrt (R u)) := by
      funext u; simp only [hF]
    rw [hFun]
    refine hFd.congr_deriv ?_
    -- the value identity
    have hpow : R t ^ (n - 1) * Real.sqrt (R t) = R t ^ ((2 * (n : ℝ) - 1) / 2) :=
      (pow_mul_sqrt_eq_rpow' hr.le (n - 1)).trans (by rw [show ((n - 1 : ℕ) : ℝ) + 1 / 2
        = (2 * (n : ℝ) - 1) / 2 by rw [Nat.cast_sub hn]; push_cast; ring])
    have hpow' : R t ^ (n - 1) / Real.sqrt (R t) = R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (R t) (n - 1), ← Real.rpow_sub hr]
      congr 1
      rw [Nat.cast_sub hn]; push_cast; ring
    have hRM : R t * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) = R t ^ ((2 * (n : ℝ) - 1) / 2) := by
      have h := Real.rpow_add hr (1 : ℝ) ((2 * (n : ℝ) - 1) / 2 - 1)
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have hkey2 : t ^ 2 * f t * (f t - t * deriv f t)
        = t ^ 2 * (R t - t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      simp only [hR, rad0]; ring
    -- the two sides of the value identity, in the `(2n-1)/2` exponent form
    have hB' : t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t) = t ^ 2 * R t ^ ((2 * (n : ℝ) - 1) / 2) := by
      rw [mul_assoc, hpow]
    have hA' : t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) / Real.sqrt (R t)
        = t ^ 2 * f t * (f t - t * deriv f t) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) := by
      rw [mul_div_assoc, hpow']
    have htarget : (2 * (n : ℝ) + 2) * (t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t)) -
          (2 * (n : ℝ) - 1) * (t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
            Real.sqrt (R t))
        = 3 * t ^ 2 * R t ^ ((2 * (n : ℝ) - 1) / 2) +
          t ^ 3 * (((2 * (n : ℝ) - 1) / 2) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      rw [hB', hA', hkey2]
      rw [show t ^ 2 * (R t - t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) *
            R t ^ ((2 * (n : ℝ) - 1) / 2 - 1)
          = t ^ 2 * (R t * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1))
            - t ^ 2 * (t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) *
                R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) by ring]
      rw [hRM]
      ring
    have hLHS : (3 * t ^ (3 - 1) * 1) * (R t ^ (n - 1) * Real.sqrt (R t)) +
          t ^ 3 * ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t))
        = 3 * t ^ 2 * R t ^ ((2 * (n : ℝ) - 1) / 2) +
          t ^ 3 * (((2 * (n : ℝ) - 1) / 2) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      rw [hp, hpow]
      ring
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    rw [hLHS, ← htarget]
  -- continuity of the primitive on the chord
  have hRcontOn : ContinuousOn R (Set.Icc (-(x)) y) := by
    have h1 : ContinuousOn (fun u : ℝ => f u ^ 2 - (s * u) ^ 2) (Set.Icc (-(x)) y) :=
      ((hfcont.mono (by
          intro u hu
          exact ⟨lt_of_lt_of_le hx0 hu.1, lt_of_le_of_lt hu.2 hy1⟩)).pow 2).sub
        (((continuous_const.mul continuous_id).continuousOn).pow 2)
    exact h1.congr (fun u _ => by simp only [hR, rad0])
  have hcontF : ContinuousOn F (Set.Icc (-(x)) y) := by
    have hfun : F = fun t : ℝ => t ^ 3 * (R t ^ (n - 1) * Real.sqrt (R t)) := by
      funext t; simp only [hF]
    rw [hfun]
    exact ((continuous_id.pow 3).continuousOn).mul
      (((continuous_id.pow (n - 1)).mul Real.continuous_sqrt).comp_continuousOn hRcontOn)
  -- the derivative is interval-integrable
  have hintD : IntervalIntegrable (fun t : ℝ =>
      (2 * (n : ℝ) + 2) * (t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))) volume (-(x)) y :=
    (hintB'.const_mul (2 * (n : ℝ) + 2)).sub (hintA'.const_mul (2 * (n : ℝ) - 1))
  -- the fundamental theorem of calculus
  have hFTC : (∫ t in (-(x))..y, ((2 * (n : ℝ) + 2) * (t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t)) -
      (2 * (n : ℝ) - 1) * (t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
        Real.sqrt (R t)))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hxy) hcontF
      (fun t ht => hpoint t ht) hintD]
    have hFy : F y = 0 := by simp only [hF, hRy, Real.sqrt_zero, mul_zero]
    have hFx : F (-(x)) = 0 := by simp only [hF, hRx, Real.sqrt_zero, mul_zero]
    rw [hFy, hFx, sub_zero]
  -- split the integral and conclude
  have hsplit : (∫ t in (-(x))..y, ((2 * (n : ℝ) + 2) * (t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t)) -
      (2 * (n : ℝ) - 1) * (t ^ 2 * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
        Real.sqrt (R t))))
      = (2 * (n : ℝ) + 2) * (∫ t in (-(x))..y, t ^ 2 * R t ^ (n - 1) * Real.sqrt (R t))
        - (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t ^ 2 * f t * (f t - t * deriv f t) *
            R t ^ (n - 1) / Real.sqrt (R t)) := by
    rw [intervalIntegral.integral_sub (hintB'.const_mul (2 * (n : ℝ) + 2))
        (hintA'.const_mul (2 * (n : ℝ) - 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]

/-- The identity of Prop. `workHARD1` in the raw `sphereArea * ∫` form, with the profile only `C¹`
on the open interval.  This is the tail of `radon_data_eq_inertiaIntegral` with the hypothesis
weakened. -/
private theorem radon_data_Ioo_form (n : ℕ) (hn : 1 ≤ n) (f ρ x y : ℝ → ℝ) (s : ℝ)
    (hs : 0 < s) (hfC1 : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hderiv_nonneg : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
      0 ≤ ρ u + u * deriv ρ u)
    (hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s)
    (hend_x : ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s))
    (hφmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈
        Set.Ioo (-(x s)) (y s))
    (hxI : -(x s) ∈ Set.Ioo (-1 : ℝ) 1) (hyI : y s ∈ Set.Ioo (-1 : ℝ) 1)
    (hfy : f (y s) = s * y s) (hfx : f (-(x s)) = s * x s)
    (huniqy : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = y s)
    (huniqx : ∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(x s))
    (hxy : -(x s) < y s)
    (hrad : ∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < rad0 f s t)
    (hintA : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x s)) (y s))
    (hintB : IntervalIntegrable (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(x s)) (y s)) :
    Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ 2 *
            ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2))
      = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) *
        Real.sqrt (1 + s ^ 2) * inertiaIntegral n f x y s := by
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcpos : 0 < c := by rw [hc]; positivity
  have hfact : (1 : ℝ) < 1 + s ^ 2 := by nlinarith [hs, sq_nonneg s]
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) hfact
  have hsc : Real.sqrt (1 + s ^ 2) * c = 1 := by
    rw [hc]; exact mul_inv_cancel₀ (ne_of_gt hspos)
  have hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1, c * ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro ν hν
    constructor <;> nlinarith [hcpos, hclt, hν.1, hν.2]
  have hρd : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt ρ (deriv ρ u) u := by
    intro u hu
    exact ((hρC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) (fun v hv => hv))).hasDerivAt
  have hfd : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt f (deriv f t) t := by
    intro t ht
    exact ((hfC1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hpoint : ∀ ν ∈ Set.uIcc (-1 : ℝ) 1,
      (1 - ν ^ 2) ^ (n - 1) * ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2)
        = Real.sqrt (1 + s ^ 2) *
          ((fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν)) *
            (c * (ρ (c * ν) + c * ν * deriv ρ (c * ν)))) := by
    intro ν hν
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
    rcases eq_or_lt_of_le hν.2 with h1 | hlt
    · subst h1
      have hy0 : rad0 f s (y s) = 0 := by rw [rad0, hfy]; ring
      have hφ1 : ρ (c * 1) * (c * 1) = y s := by rw [mul_one]; exact hend_y
      simp only [hφ1, hy0]
      have h11 : (1 : ℝ) - 1 ^ 2 = 0 := by norm_num
      rw [h11, Real.sqrt_zero]
      simp only [div_zero, zero_mul, mul_zero]
    · rcases eq_or_lt_of_le (show -ν ≤ 1 from by linarith [hν.1]) with h2 | hgt
      · have hνm : ν = -1 := by linarith
        subst hνm
        have hx0 : rad0 f s (-(x s)) = 0 := by rw [rad0, hfx]; ring
        have hφm1 : ρ (c * (-1)) * (c * (-1)) = -(x s) := by
          have hcm : c * (-1 : ℝ) = -c := by ring
          rw [hcm]; exact hend_x
        simp only [hφm1, hx0]
        have hm11 : (1 : ℝ) - (-1) ^ 2 = 0 := by norm_num
        rw [hm11, Real.sqrt_zero]
        simp only [div_zero, zero_mul, mul_zero]
      · have hνIoo : ν ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hlt⟩
        have hu : c * ν ∈ Set.Ioo (-1 : ℝ) 1 := hmem ν hνIoo
        have hφmemν : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-(x s)) (y s) := hφmem ν hνIoo
        have hchord : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-1 : ℝ) 1 :=
          ⟨lt_trans (by linarith [hxI.1]) hφmemν.1, lt_trans hφmemν.2 hyI.2⟩
        have hRpos : 0 < rad0 f s (ρ (c * ν) * (c * ν)) := hrad _ hφmemν
        have hs1 : 0 < 1 - ν ^ 2 := by nlinarith [hνIoo.1, hνIoo.2]
        have hcc : c * c * (1 + s ^ 2) = 1 := by
          rw [hc]; field_simp; rw [Real.sq_sqrt (by positivity)]
        have huv : (c * ν) ^ 2 * (1 + s ^ 2) = ν ^ 2 := by
          calc (c * ν) ^ 2 * (1 + s ^ 2) = (c * c * (1 + s ^ 2)) * ν ^ 2 := by ring
            _ = ν ^ 2 := by rw [hcc, one_mul]
        have hRcalc : rad0 f s (ρ (c * ν) * (c * ν)) = ρ (c * ν) ^ 2 * (1 - ν ^ 2) := by
          have hrel : ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2) = f (ρ (c * ν) * (c * ν)) :=
            hρ (c * ν) hu
          rw [rad0, ← hrel]
          have hsqu : Real.sqrt (1 - (c * ν) ^ 2) ^ 2 = 1 - (c * ν) ^ 2 :=
            Real.sq_sqrt (by nlinarith [hu.1, hu.2, sq_nonneg (c * ν)])
          calc (ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2)) ^ 2 - (s * (ρ (c * ν) * (c * ν))) ^ 2
              = ρ (c * ν) ^ 2 * (1 - (c * ν) ^ 2) - s ^ 2 * (ρ (c * ν) * (c * ν)) ^ 2 := by
                rw [mul_pow, hsqu]; ring
            _ = ρ (c * ν) ^ 2 * (1 - ν ^ 2) := by
                rw [show ρ (c * ν) ^ 2 * (1 - (c * ν) ^ 2) - s ^ 2 * (ρ (c * ν) * (c * ν)) ^ 2
                    = ρ (c * ν) ^ 2 * (1 - (c * ν) ^ 2 * (1 + s ^ 2)) from by ring, huv]
        have hradinst : f (ρ (c * ν) * (c * ν)) *
            (f (ρ (c * ν) * (c * ν)) - ρ (c * ν) * (c * ν) * deriv f (ρ (c * ν) * (c * ν))) *
            (ρ (c * ν) + c * ν * deriv ρ (c * ν)) = ρ (c * ν) ^ 3 :=
          radial_identity hu (hρpos _ hu) (hρd _ hu) (hfd _ hchord) hρ
        exact pointwise_radon_core n hn hsc (hρpos _ hu) hRpos hs1 hRcalc hradinst
  have hint : (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
        ((c * ν) ^ 2 * ρ (c * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2))
      = Real.sqrt (1 + s ^ 2) *
        (∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν)) *
          (c * (ρ (c * ν) + c * ν * deriv ρ (c * ν)))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hpoint
  have hcv := radon_change_of_variables n hs hρpos hρC1 hmono hρ hderiv_nonneg hend_y hend_x
  rw [← hc] at hcv
  have hibp := section_ibp_Ioo n hn f (x s) (y s) s hs hfC1 hxI hyI hxy hfy (by rw [hfx]; ring) hrad hintA hintB
  have hne : (2 * (n : ℝ) - 1) ≠ 0 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hIf : (∫ t in (-(x s))..(y s),
        (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) t)
      = ((2 * (n : ℝ) + 2) * inertiaIntegral n f x y s) / (2 * (n : ℝ) - 1) := by
    rw [eq_div_iff hne]
    calc (∫ t in (-(x s))..(y s), (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
          rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) t) * (2 * (n : ℝ) - 1)
        = (2 * (n : ℝ) - 1) * (∫ t in (-(x s))..(y s), (fun t : ℝ => t ^ 2 * f t *
            (f t - t * deriv f t) * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) t) := by ring
      _ = (2 * (n : ℝ) + 2) * inertiaIntegral n f x y s := by
        simpa only [inertiaIntegral] using hibp
  have hsph : Work.OddRadon.sphereArea (2 * n - 2) = (2 * (n : ℝ) - 1) * ballVol (2 * n - 1) := by
    rw [sphereArea_eq_ballVol (2 * n - 2)]
    have h2 : 2 ≤ 2 * n := by omega
    have hcast : (((2 * n - 2 : ℕ)) : ℝ) + 1 = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub h2]; push_cast; ring
    have h3 : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    rw [hcast, h3]
  rw [hint, hcv, hIf, hsph]
  field_simp

/-- **Prop. `workHARD1` in one dimension**, with the profile only `C¹` on the open interval
`(-1,1)`: the spherical-Radon data of a body of revolution are the second moments of its central
sections, i.e. they equal `(2n+2)|B^{2n-1}|√(1+s²)` times the low-slope inertia integral. -/
theorem radon_data_eq_inertiaIntegral_Ioo (n : ℕ) (hn : 1 ≤ n) :
    ∀ (f ρ x y : ℝ → ℝ) (s : ℝ), 0 < s → ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) → (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) → ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) → StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) → (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u)) → (∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹, 0 ≤ ρ u + u * deriv ρ u) → ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s → ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s) → (∀ ν ∈ Set.Ioo (-1 : ℝ) 1, ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈ Set.Ioo (-(x s)) (y s)) → -(x s) ∈ Set.Ioo (-1 : ℝ) 1 → y s ∈ Set.Ioo (-1 : ℝ) 1 → f (y s) = s * y s → f (-(x s)) = s * x s → (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = y s) → (∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(x s)) → -(x s) < y s → (∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < Work.OddCurve.LowSlope.rad0 f s t) → IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) / Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t)) volume (-(x s)) (y s) → IntervalIntegrable (fun t : ℝ => t ^ 2 * Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t)) volume (-(x s)) (y s) → Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) ((Real.sqrt (1 + s ^ 2))⁻¹) = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) * Work.OddCurve.LowSlope.inertiaIntegral n f x y s := by
  intro f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderiv_nonneg hend_y hend_x hφmem hxI hyI
    hfy hfx huniqy huniqx hxy hrad hintA hintB
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by positivity
  rw [radonProfile_eq_natpow n hn (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) hcpos]
  exact radon_data_Ioo_form n hn f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderiv_nonneg hend_y
    hend_x hφmem hxI hyI hfy hfx huniqy huniqx hxy hrad hintA hintB

end

end Work.OddCurve.LowSlope
