import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddCurve.LowSlope.radon_change_gen
import Submission.Work.OddCurve.LowSlope.radial_identity
import Submission.Work.OddRadon.intervalIntegrable_one_sub_sq_rpow
import Submission.Work.OddCurve.LowSlope.intervalIntegrable_nu_integrand

/-!
# The interval-integrability side conditions of Prop. `workHARD1`

`Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral_Ioo` and
`Work.OddCurve.LowSlope.radon_data_eq_centIntegral_Ioo` state the one-dimensional
spherical-Radon identity of Ryabogin's Prop. `workHARD1` under `IntervalIntegrable`
hypotheses on the chord.  This file *derives* those hypotheses from the hypotheses that are
already available in the application.

The two `1/√(rad0)` integrands are singular at the endpoints `-(x s)`, `y s`; the substitution
`t = ρ(cν)·(cν)`, `c = (√(1+s²))⁻¹`, is a nondecreasing `C¹` bijection of `(-1,1)` onto the chord
whose Jacobian cancels the singularity exactly, so the integrands become
`(1-ν²)^(n-1)φ(ν)/√(1-ν²)` with `φ` continuous on `[-1,1]` — integrable.  Integrability then
transfers back by `intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- `x ∈ Ioo (min a b) (max a b)` implies `x ∈ Ioo a b` when `a ≤ b`. -/
private lemma mem_Ioo_of_mem_Ioo_minmax {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Ioo (min a b) (max a b)) : x ∈ Set.Ioo a b := by
  rwa [min_eq_left hab, max_eq_right hab] at hx

/-- `x ∈ Ioo (min a b) (max a b)` implies `x ∈ uIcc a b` when `a ≤ b`. -/
private lemma mem_uIcc_of_mem_Ioo_minmax {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Ioo (min a b) (max a b)) : x ∈ Set.uIcc a b := by
  rw [min_eq_left hab, max_eq_right hab] at hx
  rw [Set.uIcc_of_le hab]
  exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩


/-- The pointwise algebra of the centroid part of Prop. `workHARD1`, with `f` only `C¹` on the
open interval `(-1,1)`. -/
private lemma key_identity_cent (n : ℕ) (hn : 1 ≤ n) {f ρ : ℝ → ℝ} {s c ν : ℝ}
    (hs : 0 < s)
    (hc : c = (Real.sqrt (1 + s ^ 2))⁻¹)
    (hfC1 : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1))
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hν : ν ∈ Set.Ioo (-1 : ℝ) 1)
    (ht1 : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)) / Real.sqrt (1 - ν ^ 2)
      = (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
        * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := by
    apply Real.sqrt_pos.2
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    have h : (1 : ℝ) < 1 + s ^ 2 := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
  have hcsq : c ^ 2 * (1 + s ^ 2) = 1 := by
    have h : c * c * (1 + s ^ 2) = 1 := by
      rw [hc]; field_simp; rw [Real.sq_sqrt (by positivity)]
    rwa [pow_two]
  have hcu : c * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [hν.1, hcpos, hclt], by nlinarith [hν.2, hcpos, hclt]⟩
  have h1nu : 0 < 1 - ν ^ 2 := by nlinarith [hν.1, hν.2]
  have hrp : 0 < ρ (c * ν) := hρpos _ hcu
  have hρd : HasDerivAt ρ (deriv ρ (c * ν)) (c * ν) :=
    ((hρC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hcu) (fun u hu => hu))).hasDerivAt
  have hfd : HasDerivAt f (deriv f (ρ (c * ν) * (c * ν))) (ρ (c * ν) * (c * ν)) :=
    ((hfC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ht1)).hasDerivAt
  have hrad := radial_identity hcu hrp hρd hfd hρ
  have hf_eq : f (ρ (c * ν) * (c * ν)) = ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2) :=
    (hρ _ hcu).symm
  have h1mu : 0 < 1 - (c * ν) ^ 2 := by nlinarith [hcu.1, hcu.2]
  have hRu : (c * ν) ^ 2 * (1 + s ^ 2) = ν ^ 2 := by
    rw [mul_pow]
    linear_combination (ν ^ 2) * hcsq
  have hR : rad0 f s (ρ (c * ν) * (c * ν)) = (ρ (c * ν)) ^ 2 * (1 - ν ^ 2) := by
    rw [rad0, hf_eq]
    have h1 : (ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2)) ^ 2
        = (ρ (c * ν)) ^ 2 * (1 - (c * ν) ^ 2) := by rw [mul_pow, Real.sq_sqrt h1mu.le]
    have h2 : (s * (ρ (c * ν) * (c * ν))) ^ 2 = s ^ 2 * (ρ (c * ν)) ^ 2 * (c * ν) ^ 2 := by
      ring
    rw [h1, h2]
    nlinarith [hRu]
  have hsqrtR : Real.sqrt (rad0 f s (ρ (c * ν) * (c * ν)))
      = ρ (c * ν) * Real.sqrt (1 - ν ^ 2) := by
    rw [hR, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hrp.le]
  have hwn : Real.sqrt (1 - ν ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1nu)
  have hrn : ρ (c * ν) ≠ 0 := ne_of_gt hrp
  beta_reduce
  rw [hsqrtR, hR]
  have hreord : (ρ (c * ν) * (c * ν)) * f (ρ (c * ν) * (c * ν))
        * (f (ρ (c * ν) * (c * ν)) - (ρ (c * ν) * (c * ν)) * deriv f (ρ (c * ν) * (c * ν)))
        * ((ρ (c * ν)) ^ 2 * (1 - ν ^ 2)) ^ (n - 1)
        / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2))
        * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν))
      = (ρ (c * ν) * (c * ν))
          * (f (ρ (c * ν) * (c * ν))
            * (f (ρ (c * ν) * (c * ν)) - (ρ (c * ν) * (c * ν)) * deriv f (ρ (c * ν) * (c * ν)))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)))
          * ((ρ (c * ν)) ^ 2 * (1 - ν ^ 2)) ^ (n - 1)
          / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2)) := by ring
  rw [hreord, hrad, mul_pow ((ρ (c * ν)) ^ 2) (1 - ν ^ 2) (n - 1), ← pow_mul]
  have hpow4 : (ρ (c * ν)) * (ρ (c * ν)) ^ 3 * (ρ (c * ν)) ^ (2 * (n - 1))
      = (ρ (c * ν)) ^ (2 * n + 2) := by
    rw [show 2 * n + 2 = 1 + 3 + 2 * (n - 1) by omega, pow_add, pow_add]
    ring
  have hpow5 : (ρ (c * ν)) ^ (2 * n + 1) * ρ (c * ν) = (ρ (c * ν)) ^ (2 * n + 2) := by
    rw [← pow_succ (ρ (c * ν)) (2 * n + 1), show (2 * n + 1) + 1 = 2 * n + 2 by omega]
  rw [div_eq_div_iff hwn (mul_ne_zero hrn hwn)]
  have hL : ((1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)))
        * (ρ (c * ν) * Real.sqrt (1 - ν ^ 2))
      = (c * ν) * ((ρ (c * ν)) ^ (2 * n + 1) * ρ (c * ν))
        * ((1 - ν ^ 2) ^ (n - 1) * Real.sqrt (1 - ν ^ 2)) := by ring
  have hR' : ((ρ (c * ν) * (c * ν)) * (ρ (c * ν)) ^ 3
        * ((ρ (c * ν)) ^ (2 * (n - 1)) * (1 - ν ^ 2) ^ (n - 1)))
        * Real.sqrt (1 - ν ^ 2)
      = (c * ν) * ((ρ (c * ν)) * (ρ (c * ν)) ^ 3 * (ρ (c * ν)) ^ (2 * (n - 1)))
        * ((1 - ν ^ 2) ^ (n - 1) * Real.sqrt (1 - ν ^ 2)) := by ring
  rw [hL, hR', hpow5, hpow4]

/-- **The four interval-integrability side conditions of Prop. `workHARD1`.**

`Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral_Ioo` and
`Work.OddCurve.LowSlope.radon_data_eq_centIntegral_Ioo` (both proved, sorry-free) state the
one-dimensional spherical-Radon identity of Ryabogin's Prop. `workHARD1` under two
`IntervalIntegrable` hypotheses on the chord `(-(x s), y s)`, where
`rad0 f s t = f t ^ 2 - (s * t) ^ 2`:

* `t ↦ t^2 * f t * (f t - t * deriv f t) * rad0 ^ (n-1) / sqrt (rad0)` (inertia), and
* `t ↦ t * f t * (f t - t * deriv f t) * rad0 ^ (n-1) / sqrt (rad0)` (centroid),

and analogously with `t` replaced by `rad0 ^ (n-1) * sqrt (rad0)` (these last two are trivial:
the integrand is continuous on the closed interval `[-(x s), y s]`, since `rad0` is continuous
there).  The present statement *derives* all four from the hypotheses that are already available
in the application, so that the identity can be used without asking the caller for integrability.

The two `1/sqrt (rad0)` integrands are singular at the two endpoints `-(x s)` and `y s`; for
`n = 1` this is an integrable `(endpoint distance)^{-1/2}` singularity.  The proof: the
substitution `t = ρ(cν)·(cν)`, `c = (√(1+s²))⁻¹`, is a `C¹` nondecreasing bijection of `(-1,1)`
onto `(-(x s), y s)` (`hend_x`, `hend_y`, `hderivn`), and its Jacobian exactly cancels the
singularity: by `Work.OddCurve.LowSlope.radial_identity` (public), for `ν ∈ (-1,1)`

  `A(ρ (c ν) * (c ν)) * (c * (ρ (c ν) + c ν * deriv ρ (c ν))) = c * (1 - ν^2)^(n-1) * ((c ν) * ρ (c ν)^(2n+1)) / sqrt (1 - ν^2)`,

where `A` is the centroid integrand (and the same with
`t * f t * (f t - t * deriv f t)` replaced by `t ^ 2 * f t * (f t - t * deriv f t)` for the
inertia integrand).  The fully assembled version of this algebra, including the constant
bookkeeping, is `key_identity` in `Submission/Work/OddCurve/LowSlope/radon_data_identity.lean`
and `key_identity_cent_Ioo` in
`Submission/Work/OddCurve/LowSlope/radon_data_eq_centIntegral_weak.lean`; both are `private`, so
copy and re-expose them (that is by far the cheapest route).

The right-hand side is `(1 - ν^2)^(n - 3/2)` times a function continuous on `[-1,1]`, hence
interval integrable on `(-1,1)` (`Work.OddRadon.intervalIntegrable_one_sub_sq_rpow` on `(0,1)`
plus evenness, or domination by `C * (1-ν^2)^(n-3/2)` with `IntervalIntegrable.mono_fun'`).
Integrability of the composed function then transfers to `IntervalIntegrable A volume (-(x s)) (y s)`
by `intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg` (Mathlib, with
`f = fun ν => ρ (cν) * (cν)`, `f' = fun ν => c * (ρ (cν) + cν * deriv ρ (cν))`).  The inertia
version follows from the centroid one by `|t| ≤ 1` on the chord (`IntervalIntegrable.norm` +
`IntervalIntegrable.mono_fun'`).

WARNING: do NOT use any module whose file contains `sorry` (e.g.
`Submission/Work/OddVolterra/Existence/anchor_cap_data.lean`,
`Submission/Work/OddRadon/contDiffOn_radonProfile.lean`); that would make the result depend on
`sorryAx`. -/
theorem intervalIntegrable_radonIntegrands (n : ℕ) (hn : 1 ≤ n) {f ρ x y : ℝ → ℝ} {s : ℝ}
    (hs : 0 < s)
    (hfC1 : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hderivn : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
      0 ≤ ρ u + u * deriv ρ u)
    (hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) = y s)
    (hend_x : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) = -(x s))
    (hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈ Set.Ioo (-(x s)) (y s))
    (hmx : -(x s) ∈ Set.Ioo (-1 : ℝ) 1) (hy : y s ∈ Set.Ioo (-1 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
        Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) / Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t))
        volume (-(x s)) (y s) ∧
      IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
        Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) / Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t))
        volume (-(x s)) (y s) ∧
      IntervalIntegrable (fun t : ℝ => t ^ 2 * Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t)) volume (-(x s)) (y s) ∧
      IntervalIntegrable (fun t : ℝ => t * Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t)) volume (-(x s)) (y s) := by
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hfact : (1 : ℝ) < 1 + s ^ 2 := by nlinarith [hs, sq_nonneg s]
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) hfact
  -- points of the closed unit interval are mapped inside `(-1,1)`
  have hmemc : ∀ ν ∈ Set.uIcc (-1 : ℝ) 1, c * ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro ν hν
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
    exact ⟨by nlinarith [hcpos, hclt, hν.1], by nlinarith [hcpos, hclt, hν.2]⟩
  have hmemcIcc : ∀ ν ∈ Set.Icc (-1 : ℝ) 1, c * ν ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro ν hν
    exact hmemc ν (by rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])
  -- chord membership, in terms of `ρ (c * ν) * (c * ν)`
  have hchord : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ (c * ν) * (c * ν) ∈ Set.Ioo (-(x s)) (y s) := by
    intro ν hν
    simpa only [hc] using hmem ν hν
  -- the substitution `ν ↦ φ ν = ρ (cν) (cν)` and its derivative `ψ`
  set φ : ℝ → ℝ := fun ν => ρ (c * ν) * (c * ν) with hφ
  set ψ : ℝ → ℝ := fun ν => c * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) with hψ
  have hφcont : ContinuousOn φ (Set.uIcc (-1 : ℝ) 1) := by
    have h1 : ContinuousOn (fun x : ℝ => ρ (c * x)) (Set.uIcc (-1 : ℝ) 1) :=
      hρC1.continuousOn.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun x hx => hmemc x hx)
    have hfun : φ = fun x : ℝ => ρ (c * x) * (c * x) := by funext x; simp only [hφ]
    rw [hfun]
    exact h1.mul ((continuous_const.mul continuous_id).continuousOn)
  have hφd : ∀ ν ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt φ (ψ ν) ν := by
    intro ν hν
    have hu : c * ν ∈ Set.Ioo (-1 : ℝ) 1 := hmemc ν hν
    have hρd : HasDerivAt ρ (deriv ρ (c * ν)) (c * ν) :=
      ((hρC1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
    have hinner : HasDerivAt (fun x : ℝ => c * x) c ν := by
      simpa using (hasDerivAt_id ν).const_mul c
    have h1 : HasDerivAt (fun x : ℝ => ρ (c * x)) (deriv ρ (c * ν) * c) ν := by
      have h := HasDerivAt.comp ν hρd hinner
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with x
      simp [Function.comp]
    have h3 := h1.mul hinner
    have hfun : φ = fun x : ℝ => ρ (c * x) * (c * x) := by funext x; simp only [hφ]
    rw [hfun]
    refine h3.congr_deriv ?_
    simp only [hψ]
    ring
  have hψnn : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ ψ ν := by
    intro ν hν
    have hu : c * ν ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹ := by
      rw [← hc]
      exact ⟨by nlinarith [hcpos, hν.1], by nlinarith [hcpos, hν.2]⟩
    simp only [hψ]
    exact mul_nonneg hcpos.le (hderivn (c * ν) hu)
  have hφ1 : φ 1 = y s := by
    have h : c * (1 : ℝ) = (Real.sqrt (1 + s ^ 2))⁻¹ := by rw [hc]; ring
    simp only [hφ, h]
    exact hend_y
  have hφm1 : φ (-1) = -(x s) := by
    have h : c * (-1 : ℝ) = -((Real.sqrt (1 + s ^ 2))⁻¹) := by rw [hc]; ring
    simp only [hφ, h]
    exact hend_x
  -- the `ν`-integrand of the centroid part is interval integrable
  have hφ0cont : ContinuousOn (fun ν : ℝ => (c * ν) * ρ (c * ν) ^ (2 * n + 1))
      (Set.Icc (-1 : ℝ) 1) := by
    have h1 : ContinuousOn (fun x : ℝ => ρ (c * x)) (Set.Icc (-1 : ℝ) 1) :=
      hρC1.continuousOn.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun x hx => hmemcIcc x hx)
    exact ((continuous_const.mul continuous_id).continuousOn).mul (h1.pow (2 * n + 1))
  have hNu : IntervalIntegrable
      (fun ν : ℝ => (1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)) /
        Real.sqrt (1 - ν ^ 2)) volume (-1 : ℝ) 1 :=
    intervalIntegrable_nu_integrand n hn hφ0cont
  -- the centroid `ν`-integrand
  have hcomp : IntervalIntegrable
      (fun ν : ℝ => (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (φ ν) * ψ ν) volume (-1 : ℝ) 1 := by
    refine IntervalIntegrable.congr_uIoo (hNu.const_mul c) ?_
    intro ν hν
    have hν' : ν ∈ Set.Ioo (-1 : ℝ) 1 := mem_Ioo_of_mem_Ioo_minmax (by norm_num) hν
    have hpt : φ ν ∈ Set.Ioo (-1 : ℝ) 1 := by
      have h := hchord ν hν'
      exact ⟨lt_trans hmx.1 h.1, lt_trans h.2 hy.2⟩
    have hki := key_identity_cent n hn hs hc hfC1 hρC1 hρpos hρ hν'
      (by simpa only [hφ] using hpt)
    beta_reduce
    rw [hki]
    simp only [hψ, hφ]
    ring
  -- transfer back to the chord
  have hIoo_sub : ∀ ν ∈ Set.Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1), ν ∈ Set.uIcc (-1 : ℝ) 1 :=
    fun ν hν => mem_uIcc_of_mem_Ioo_minmax (by norm_num) hν
  have hIoo_eq : ∀ ν ∈ Set.Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1), ν ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun ν hν => mem_Ioo_of_mem_Ioo_minmax (by norm_num) hν
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := φ) (f' := ψ)
    (g := fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
      Real.sqrt (rad0 f s t))
    hφcont (fun ν hν => hφd ν (hIoo_sub ν hν)) (fun ν hν => hψnn ν (hIoo_eq ν hν))
  rw [hφ1, hφm1] at hiff
  have hcent : IntervalIntegrable
      (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
        Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) :=
    hiff.mp (by simpa [Function.comp] using hcomp)
  -- the inertia `ν`-integrand, dominated by the centroid one
  have hAiNu : IntervalIntegrable
      (fun ν : ℝ => (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (φ ν) * ψ ν) volume (-1 : ℝ) 1 := by
    refine IntervalIntegrable.mono_fun' (f := fun ν : ℝ =>
        (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) (φ ν) * ψ ν)
      (g := fun ν : ℝ => ‖(fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) (φ ν) * ψ ν‖) hcomp.norm ?_ ?_
    · have hφmeas : AEStronglyMeasurable φ (volume.restrict (Set.uIoc (-1 : ℝ) 1)) :=
        (hφcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
      have hprod : AEStronglyMeasurable (fun ν : ℝ => φ ν *
          ((fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (φ ν) * ψ ν))
          (volume.restrict (Set.uIoc (-1 : ℝ) 1)) :=
        hφmeas.mul hcomp.aestronglyMeasurable_restrict_uIoc
      refine hprod.congr ?_
      filter_upwards with ν
      ring
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with ν hν
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
      have hle : |φ ν| ≤ 1 := by
        rcases lt_or_eq_of_le hν.2 with hlt | heq
        · have hpt : φ ν ∈ Set.Ioo (-(x s)) (y s) := by
            have h := hmem ν (⟨hν.1, hlt⟩ : ν ∈ Set.Ioo (-1 : ℝ) 1)
            simpa only [hφ, hc] using h
          exact abs_le.mpr ⟨le_of_lt (lt_trans hmx.1 hpt.1), le_of_lt (lt_trans hpt.2 hy.2)⟩
        · rw [heq, hφ1]
          exact abs_le.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      have hb : ‖(fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (φ ν)‖
          ≤ ‖(fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (φ ν)‖ := by
        have heq : (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (φ ν)
            = φ ν * ((fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (φ ν)) := by
          ring
        rw [Real.norm_eq_abs, Real.norm_eq_abs, heq, abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) (le_of_eq (one_mul _))
      calc ‖(fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (φ ν) * ψ ν‖
          = ‖(fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (φ ν)‖ * ‖ψ ν‖ := norm_mul _ _
        _ ≤ ‖(fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (φ ν)‖ * ‖ψ ν‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = ‖(fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (φ ν) * ψ ν‖ := (norm_mul _ _).symm
  have hiff2 := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := φ) (f' := ψ)
    (g := fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
      Real.sqrt (rad0 f s t))
    hφcont (fun ν hν => hφd ν (hIoo_sub ν hν)) (fun ν hν => hψnn ν (hIoo_eq ν hν))
  rw [hφ1, hφm1] at hiff2
  have hAi : IntervalIntegrable
      (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
        Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) :=
    hiff2.mp (by simpa [Function.comp] using hAiNu)
  -- the two continuous integrands
  have hradcont : ContinuousOn (fun t : ℝ => rad0 f s t) (Set.uIcc (-(x s)) (y s)) := by
    have hsub : Set.uIcc (-(x s)) (y s) ⊆ Set.Ioo (-1 : ℝ) 1 := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hmx.1 h1, lt_of_le_of_lt h2 hy.2⟩
      · exact ⟨lt_of_lt_of_le hy.1 h1, lt_of_le_of_lt h2 hmx.2⟩
    have hfcont : ContinuousOn f (Set.uIcc (-(x s)) (y s)) := hfC1.continuousOn.mono hsub
    have hfun : (fun t : ℝ => rad0 f s t) = fun t : ℝ => f t ^ 2 - (s * t) ^ 2 := by
      funext t; rw [rad0]
    rw [hfun]
    exact (hfcont.pow 2).sub (((continuous_const.mul continuous_id).continuousOn).pow 2)
  have h3 : IntervalIntegrable
      (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
      volume (-(x s)) (y s) := by
    have hcont : ContinuousOn
        (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
        (Set.uIcc (-(x s)) (y s)) := by
      fun_prop
    exact hcont.intervalIntegrable
  have h4 : IntervalIntegrable
      (fun t : ℝ => t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
      volume (-(x s)) (y s) := by
    have hcont : ContinuousOn
        (fun t : ℝ => t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
        (Set.uIcc (-(x s)) (y s)) := by
      fun_prop
    exact hcont.intervalIntegrable
  exact ⟨hAi, hcent, h3, h4⟩

end

end Work.OddCurve.LowSlope
