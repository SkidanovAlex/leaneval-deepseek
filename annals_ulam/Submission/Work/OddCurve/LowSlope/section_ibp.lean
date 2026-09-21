import Mathlib
import Submission.Work.OddCurve.LowSlope.CruxStatements
import Submission.Work.OddCurve.hasDerivAt_max_pow_sqrt

/-!
# `section_ibp`: the integration-by-parts identity of Prop. `workHARD1`

Statement: `Work.OddCurve.LowSlope.SectionIBP` (`LowSlope/CruxStatements.lean`).

Write `p = (n-1) + 1/2` (so `R^{n-1}√R = R^p` and `R^{n-1}/√R = R^{p-1}` for `R > 0`) and
`R' t = 2 f t f' t - 2 s² t`.  The function `F t = t³ R t^p` has

`F' = 3t² R^p + t³ p R^{p-1} R'`,

and, since `f (f - t f') = R - (t/2) R'` (`ring`), the *difference* of the two integrands of the
statement is

`(2n+2) t² R^p - (2n-1) t² f (f - t f') R^{p-1} = 3t² R^p + ((2n-1)/2) t³ R' R^{p-1} = F'`,

because `p = (2n-1)/2`.  The fundamental theorem of calculus over the chord, with `R = 0` at both
ends (hence `F = 0` there), gives the identity.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

private lemma pow_mul_sqrt_eq_rpow' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.sqrt x = x ^ ((n : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x n]
  exact (Real.rpow_add' hx (by positivity)).symm

theorem section_ibp : SectionIBP := by
  intro n hn f x y s hs hf hx hy hxy hfy hfx hpos hintA hintB
  have hfcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1) := hf.continuousOn
  have hf_diff : DifferentiableOn ℝ f (Set.Icc (-1 : ℝ) 1) := hf.differentiableOn (by norm_num)
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
    exact (hf_diff.differentiableAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht1)
      (fun u hu => ⟨hu.1.le, hu.2.le⟩))).hasDerivAt
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
          exact ⟨le_trans hx0.le hu.1, le_trans hu.2 hy1.le⟩)).pow 2).sub
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

end

end Work.OddCurve.LowSlope
