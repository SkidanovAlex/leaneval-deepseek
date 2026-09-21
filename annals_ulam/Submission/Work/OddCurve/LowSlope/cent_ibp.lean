import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs

/-!
# The centroid integration-by-parts identity of Prop. `workHARD1`

The companion of `Work.OddCurve.LowSlope.section_ibp` for the *centroid* integral `(cmass)`:
with `R = rad0 f s ·` and `p = (2n-1)/2`, the primitive `F t = t² R t ^ p` satisfies

`F' = 2t R^p + p t² R' R^{p-1}`,

and `f (f - t f') = R - (t/2) R'`, so the difference of the two integrands is exactly `F'`.
The fundamental theorem of calculus over the chord (where `R = 0`, hence `F = 0` at both ends)
gives `(2n-1) ∫ t f (f - t f') R^{n-1}/√R = (2n+1) ∫ t R^{n-1} √R`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

private lemma pow_mul_sqrt_eq_rpow'' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.sqrt x = x ^ ((n : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x n]
  exact (Real.rpow_add' hx (by positivity)).symm

/-- **The centroid integration-by-parts identity.** -/
theorem cent_ibp (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℝ} {x y s : ℝ}
    (hs : 0 < s)
    (hf : ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1))
    (hx : -(x) ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hxy : -(x) < y)
    (hfy : f y = s * y) (hfx : f (-(x)) = -(s * (-(x))))
    (hpos : ∀ t ∈ Set.Ioo (-(x)) y, 0 < rad0 f s t)
    (hintA : IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x)) y)
    (hintB : IntervalIntegrable (fun t : ℝ => t * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(x)) y) :
    (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
      = (2 * (n : ℝ) + 1) * (∫ t in (-(x))..y, t * rad0 f s t ^ (n - 1) *
        Real.sqrt (rad0 f s t)) := by
  have hfcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1) := hf.continuousOn
  have hf_diff : DifferentiableOn ℝ f (Set.Icc (-1 : ℝ) 1) := hf.differentiableOn (by norm_num)
  have hx0 : -1 < -(x) := hx.1
  have hy1 : y < 1 := hy.2
  set R : ℝ → ℝ := fun t => rad0 f s t with hR
  have hRy : R y = 0 := by simp only [hR, rad0, hfy]; ring
  have hRx : R (-(x)) = 0 := by simp only [hR, rad0]; rw [hfx]; ring
  have hfd : ∀ t ∈ Set.Ioo (-(x)) y, HasDerivAt f (deriv f t) t := by
    intro t ht
    have ht1 : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx0 ht.1, lt_trans ht.2 hy1⟩
    exact (hf_diff.differentiableAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht1)
      (fun u hu => ⟨hu.1.le, hu.2.le⟩))).hasDerivAt
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
  have hAeq : (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
      Real.sqrt (rad0 f s t))
      = (fun t : ℝ => t * f t * (f t - t * deriv f t) * R t ^ (n - 1) / Real.sqrt (R t)) := by
    funext t; simp only [hR]
  have hBeq : (fun t : ℝ => t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
      = (fun t : ℝ => t * R t ^ (n - 1) * Real.sqrt (R t)) := by
    funext t; simp only [hR]
  rw [hAeq, hBeq]
  have hintA' : IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
      R t ^ (n - 1) / Real.sqrt (R t)) volume (-(x)) y := by
    rw [← hAeq]; exact hintA
  have hintB' : IntervalIntegrable (fun t : ℝ => t * R t ^ (n - 1) * Real.sqrt (R t))
      volume (-(x)) y := by
    rw [← hBeq]; exact hintB
  have hp : (((n - 1 : ℕ) : ℝ) + 1 / 2) = (2 * (n : ℝ) - 1) / 2 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  set F : ℝ → ℝ := fun t => t ^ 2 * (R t ^ (n - 1) * Real.sqrt (R t)) with hF
  have hpoint : ∀ t ∈ Set.Ioo (-(x)) y,
      HasDerivAt F ((2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))) t := by
    intro t ht
    have hr : 0 < R t := hpos t ht
    have hrne : R t ≠ 0 := ne_of_gt hr
    have hin : HasDerivAt (fun u : ℝ => R u ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
        ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
          (2 * f t * deriv f t - 2 * s ^ 2 * t)) t :=
      (Real.hasDerivAt_rpow_const (Or.inl hrne)).comp t (hRd t ht)
    have hRcontAt : ContinuousAt R t := by
      have h1 : ContinuousAt (fun u : ℝ => f u ^ 2 - (s * u) ^ 2) t :=
        (((hfcont.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds
            ⟨lt_trans hx0 ht.1, lt_trans ht.2 hy1⟩) (fun u hu => ⟨hu.1.le, hu.2.le⟩))).pow 2).sub
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
      exact pow_mul_sqrt_eq_rpow'' hu.le (n - 1)
    have hFd := (((hasDerivAt_id t).pow 2)).mul hsmooth
    have hFun : F = fun u : ℝ => u ^ 2 * (R u ^ (n - 1) * Real.sqrt (R u)) := by
      funext u; simp only [hF]
    rw [hFun]
    refine hFd.congr_deriv ?_
    have hpow : R t ^ (n - 1) * Real.sqrt (R t) = R t ^ ((2 * (n : ℝ) - 1) / 2) :=
      (pow_mul_sqrt_eq_rpow'' hr.le (n - 1)).trans (by rw [show ((n - 1 : ℕ) : ℝ) + 1 / 2
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
    have hkey2 : t * f t * (f t - t * deriv f t)
        = t * (R t - t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      simp only [hR, rad0]; ring
    have hB' : t * R t ^ (n - 1) * Real.sqrt (R t) = t * R t ^ ((2 * (n : ℝ) - 1) / 2) := by
      rw [mul_assoc, hpow]
    have hA' : t * f t * (f t - t * deriv f t) * R t ^ (n - 1) / Real.sqrt (R t)
        = t * f t * (f t - t * deriv f t) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) := by
      rw [mul_div_assoc, hpow']
    have htarget : (2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
          (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
            Real.sqrt (R t))
        = 2 * t * R t ^ ((2 * (n : ℝ) - 1) / 2) +
          t ^ 2 * (((2 * (n : ℝ) - 1) / 2) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      rw [hB', hA', hkey2]
      rw [show t * (R t - t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) *
            R t ^ ((2 * (n : ℝ) - 1) / 2 - 1)
          = t * (R t * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1))
            - t * (t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) *
                R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) by ring]
      rw [hRM]
      ring
    have hLHS : (2 * t ^ (2 - 1) * 1) * (R t ^ (n - 1) * Real.sqrt (R t)) +
          t ^ 2 * ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t))
        = 2 * t * R t ^ ((2 * (n : ℝ) - 1) / 2) +
          t ^ 2 * (((2 * (n : ℝ) - 1) / 2) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      rw [hp, hpow]
      ring
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    rw [hLHS, ← htarget]
  have hRcontOn : ContinuousOn R (Set.Icc (-(x)) y) := by
    have h1 : ContinuousOn (fun u : ℝ => f u ^ 2 - (s * u) ^ 2) (Set.Icc (-(x)) y) :=
      ((hfcont.mono (by
          intro u hu
          exact ⟨le_trans hx0.le hu.1, le_trans hu.2 hy1.le⟩)).pow 2).sub
        (((continuous_const.mul continuous_id).continuousOn).pow 2)
    exact h1.congr (fun u _ => by simp only [hR, rad0])
  have hcontF : ContinuousOn F (Set.Icc (-(x)) y) := by
    have hfun : F = fun t : ℝ => t ^ 2 * (R t ^ (n - 1) * Real.sqrt (R t)) := by
      funext t; simp only [hF]
    rw [hfun]
    exact ((continuous_id.pow 2).continuousOn).mul
      (((continuous_id.pow (n - 1)).mul Real.continuous_sqrt).comp_continuousOn hRcontOn)
  have hintD : IntervalIntegrable (fun t : ℝ =>
      (2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))) volume (-(x)) y :=
    (hintB'.const_mul (2 * (n : ℝ) + 1)).sub (hintA'.const_mul (2 * (n : ℝ) - 1))
  have hFTC : (∫ t in (-(x))..y,
      ((2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t)))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hxy) hcontF
      (fun t ht => hpoint t ht) hintD]
    have hFy : F y = 0 := by simp only [hF, hRy, Real.sqrt_zero, mul_zero]
    have hFx : F (-(x)) = 0 := by simp only [hF, hRx, Real.sqrt_zero, mul_zero]
    rw [hFy, hFx, sub_zero]
  have hsplit : (∫ t in (-(x))..y,
      ((2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))))
      = (2 * (n : ℝ) + 1) * (∫ t in (-(x))..y, t * R t ^ (n - 1) * Real.sqrt (R t))
        - (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t * f t * (f t - t * deriv f t) *
            R t ^ (n - 1) / Real.sqrt (R t)) := by
    rw [intervalIntegral.integral_sub (hintB'.const_mul (2 * (n : ℝ) + 1))
        (hintA'.const_mul (2 * (n : ℝ) - 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]

end

end Work.OddCurve.LowSlope
