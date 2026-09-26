import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDiscDefs
import Submission.Work.Core.torusMap_eq_iff

namespace Work.Drive.EpsForm

/-! ## Auxiliary facts for the simplicity of the curve `κ` -/

/-- An integer multiple of a positive real `c` is smaller than `c` in absolute value only
for the zero multiple. -/
private lemma int_eq_zero_of_abs_mul_lt {j : ℤ} {c : ℝ} (hc : 0 < c) (h : |(j:ℝ) * c| < c) :
    j = 0 := by
  have h1 : |(j:ℝ)| * c < c := by rw [abs_mul, abs_of_pos hc] at h; exact h
  have h2 : |(j:ℝ)| < 1 := lt_of_mul_lt_mul_right (by simpa using h1) hc.le
  have h3 : (((|j| : ℤ)) : ℝ) < 1 := by rw [Int.cast_abs]; exact h2
  exact Int.abs_lt_one_iff.mp (by exact_mod_cast h3)

/-- `dlt` is positive strictly inside the chord range. -/
private lemma dlt_pos_of_lt {t : ℝ} (h1 : u0 < t) (h2 : t < v0) : 0 < dlt t := by
  have := bump_pos h1 h2
  unfold dlt; linarith

/-- `dlt` is at most `1/2`. -/
private lemma dlt_le_half (t : ℝ) : dlt t ≤ 1 / 2 := by
  have := Real.sin_le_one (Real.pi * (t - u0) / (v0 - u0))
  unfold dlt bump; linarith

/-- For `s ∈ (0, 2π)`, `s ≠ π`, the longitude parameter lies strictly inside the chord
range. -/
private lemma kapTheta_mem_open {s : ℝ} (h0 : 0 < s) (h2 : s < 2 * Real.pi)
    (hne : s ≠ Real.pi) : u0 < kapTheta s ∧ kapTheta s < v0 := by
  have hsin_pos : 0 < Real.sin (s / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_lt : Real.sin (s / 2) < 1 := by
    rcases lt_or_eq_of_le (Real.sin_le_one (s / 2)) with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨j, hj⟩ := Real.sin_eq_one_iff.mp heq
      -- hj : π/2 + j * 2π = s/2
      have hjeq : (j:ℝ) * (2 * Real.pi) = s / 2 - Real.pi / 2 := by linarith
      have hjabs : |(j:ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
        rw [hjeq, abs_lt]
        constructor <;> linarith [h0, h2, Real.pi_pos]
      have hj0 : j = 0 := int_eq_zero_of_abs_mul_lt (by positivity : (0:ℝ) < 2 * Real.pi) hjabs
      rw [hj0] at hj
      simp at hj
      apply hne
      linarith
  have hlen : 0 < v0 - u0 := by rw [v0_sub_u0]; positivity
  rw [kapTheta_eq_sin h0.le h2.le]
  constructor <;> nlinarith

/-- **Simplicity of the curve `κ`.**  The curve `kapGamma s = torusMap (kapTheta s)
(kapPhi s)` is injective on `[0, 2π)`.  Equivalently, `kapCurve` is a simple closed curve
of the standard torus.

Route: `kapTheta s = u0 + (v0-u0)|sin (s/2)|` is a triangular wave, so on `[0,2π]` we have
`kapTheta s = kapTheta s'` iff `s = s'` or `s + s' = 2π`; and for `s ∈ [0,π]` the tube
angle is `phLift (kapTheta s)` while for `s ∈ [π,2π]` it is `phLift (kapTheta s) + dlt
(kapTheta s)` (with `dlt ≥ 0` vanishing only at the endpoints of the range, i.e. at
`s ∈ πℤ`).  Two parameters giving the same torus point differ by multiples of `2π` in
both coordinates (`Work.Core.torusMap_eq_iff`); the bounds
`kapTheta ∈ [u0,v0] ⊂ (-2π/3, 2π/3)` and `phLift (kapTheta s) ≤ kapPhi s ≤
phLift (kapTheta s) + 1/2` kill the nonzero multiples of `2π`. -/
theorem kapGamma_injOn : Set.InjOn kapGamma (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs s' hs' heq
  obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ :=
    (Work.Core.torusMap_eq_iff (kapTheta s) (kapPhi s) (kapTheta s') (kapPhi s')).mp heq
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  -- Step 1: the longitude parameters differ by a multiple of `2π`, but both lie in `(-π,π]`.
  have hkabs : |(k:ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
    have hkeq : (k:ℝ) * (2 * Real.pi) = kapTheta s - kapTheta s' := by linarith [hk]
    rw [hkeq, abs_lt]
    exact ⟨by linarith [neg_pi_lt_kapTheta s, kapTheta_le_pi s', Real.pi_pos],
           by linarith [neg_pi_lt_kapTheta s', kapTheta_le_pi s, Real.pi_pos]⟩
  have hk0 : k = 0 := int_eq_zero_of_abs_mul_lt h2pi hkabs
  have hΘeq : kapTheta s = kapTheta s' := by rw [hk0] at hk; simpa using hk
  -- Step 2: `kapTheta` is the triangular wave, `2`-to-`1` except at `π`.
  have hsinEq : Real.sin (s / 2) = Real.sin (s' / 2) := by
    have h1 := kapTheta_eq_sin hs.1 hs.2.le
    have h2 := kapTheta_eq_sin hs'.1 hs'.2.le
    rw [h1, h2] at hΘeq
    have hlen : v0 - u0 ≠ 0 := by rw [v0_sub_u0]; positivity
    exact mul_left_cancel₀ hlen (by linarith)
  have hss : s = s' ∨ s + s' = 2 * Real.pi := by
    obtain ⟨j, hj | hj⟩ := Real.sin_eq_sin_iff.mp hsinEq
    · left
      have hj4 : (j:ℝ) * (4 * Real.pi) = s' - s := by linarith [hj]
      have hjabs : |(j:ℝ) * (4 * Real.pi)| < 4 * Real.pi := by
        rw [hj4, abs_lt]
        exact ⟨by linarith [hs'.1, hs.2, Real.pi_pos],
               by linarith [hs.1, hs'.2, Real.pi_pos]⟩
      have hj0 : j = 0 := int_eq_zero_of_abs_mul_lt (by positivity : (0:ℝ) < 4 * Real.pi) hjabs
      rw [hj0] at hj4; simp at hj4; linarith
    · right
      have hj4 : (j:ℝ) * (4 * Real.pi) = s + s' - 2 * Real.pi := by linarith [hj]
      have hjabs : |(j:ℝ) * (4 * Real.pi)| < 4 * Real.pi := by
        rw [hj4, abs_lt]
        exact ⟨by linarith [hs.1, hs'.1, Real.pi_pos],
               by linarith [hs.2, hs'.2, Real.pi_pos]⟩
      have hj0 : j = 0 := int_eq_zero_of_abs_mul_lt (by positivity : (0:ℝ) < 4 * Real.pi) hjabs
      rw [hj0] at hj4; simp at hj4; linarith
  rcases hss with h | h
  · exact h
  · by_cases hsame : s = s'
    · exact hsame
    · -- `s + s' = 2π` and `s ≠ s'`: the meridian parameters differ by `± dlt (kapTheta s)`,
      -- a nonzero number of absolute value `< 2π`, contradicting `φ = φ' + 2π m`.
      exfalso
      have hs_pos : 0 < s := by
        by_contra hcon
        have h0 : s = 0 := le_antisymm (not_lt.mp hcon) hs.1
        rw [h0, zero_add] at h
        linarith [hs'.2, h]
      have hs_ne_pi : s ≠ Real.pi := by
        intro hpi
        apply hsame
        rw [hpi] at h ⊢
        linarith
      have hθopen := kapTheta_mem_open hs_pos hs.2 hs_ne_pi
      have hdlt_pos : 0 < dlt (kapTheta s) := dlt_pos_of_lt hθopen.1 hθopen.2
      have hdlt_nonneg : 0 ≤ dlt (kapTheta s) := hdlt_pos.le
      have hsin' : Real.sin s' = -Real.sin s := by
        have hs'e : s' = 2 * Real.pi - s := by linarith
        rw [hs'e, Real.sin_two_pi_sub]
      have hsin_ne : Real.sin s ≠ 0 := by
        rcases lt_or_gt_of_ne hs_ne_pi with hlt | hgt
        · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hs_pos hlt)
        · have hy : 0 < 2 * Real.pi - s := by linarith [hgt, hs.2]
          have hy' : 2 * Real.pi - s < Real.pi := by linarith [Real.pi_pos]
          have hpos : 0 < Real.sin (2 * Real.pi - s) := Real.sin_pos_of_pos_of_lt_pi hy hy'
          have hs_eq : Real.sin s = -Real.sin (2 * Real.pi - s) := by
            have := Real.sin_two_pi_sub (2 * Real.pi - s)
            rwa [show 2 * Real.pi - (2 * Real.pi - s) = s by ring] at this
          rw [hs_eq]; linarith
      have hPhi_s : kapPhi s = phLift (kapTheta s) +
          (if 0 < Real.sin s then (0:ℝ) else dlt (kapTheta s)) := by
        unfold kapPhi
        split_ifs <;> ring
      have hPhi_s' : kapPhi s' = phLift (kapTheta s) +
          (if 0 < Real.sin s' then (0:ℝ) else dlt (kapTheta s)) := by
        unfold kapPhi
        rw [← hΘeq]
        split_ifs <;> ring
      have hdiffabs : |kapPhi s - kapPhi s'| = dlt (kapTheta s) := by
        have hdiff : kapPhi s - kapPhi s' =
            (if 0 < Real.sin s then (0:ℝ) else dlt (kapTheta s)) -
            (if 0 < Real.sin s' then (0:ℝ) else dlt (kapTheta s)) := by
          rw [hPhi_s, hPhi_s']; ring
        rw [hdiff]
        rcases lt_or_gt_of_ne hsin_ne with hlt | hgt
        · have hs'_pos : 0 < Real.sin s' := by rw [hsin']; linarith
          rw [if_neg (not_lt.mpr hlt.le), if_pos hs'_pos, sub_zero]
          exact abs_of_nonneg hdlt_nonneg
        · have hs'_neg : ¬ (0 < Real.sin s') := by rw [hsin']; linarith
          rw [if_pos hgt, if_neg hs'_neg, zero_sub, abs_neg]
          exact abs_of_nonneg hdlt_nonneg
      have hm' : (m:ℝ) * (2 * Real.pi) = kapPhi s - kapPhi s' := by linarith [hm]
      have hmabs : |(m:ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
        rw [hm', hdiffabs]
        have := dlt_le_half (kapTheta s)
        linarith [Real.pi_gt_three]
      have hm0 : m = 0 := int_eq_zero_of_abs_mul_lt h2pi hmabs
      have hPhieq : kapPhi s = kapPhi s' := by rw [hm0] at hm; simpa using hm
      have : dlt (kapTheta s) = 0 := by rw [← hdiffabs, hPhieq]; simp
      linarith [hdlt_pos, this]

end Work.Drive.EpsForm
