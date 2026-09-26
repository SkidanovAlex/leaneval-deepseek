import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2
import Submission.Work.Drive.EpsForm.profX_injOn

namespace Work.Drive.EpsForm

open Set

noncomputable section

/-! ## Elementary facts about the radius `2 + (profX t s).1`

The radius of the tube-coordinate map `eFunX` is `ρ(t,s) = 2 + (profX t s).1`.  It vanishes
exactly at the axis point `W1 = (-2,0)`, i.e. at `s = 0`; on `0 < s ≤ 1` it is strictly
positive (`profX_fst_gt`).  This is what makes the azimuth visible in the image. -/

/-- The radius is nonnegative on the parameter rectangle `[0,1]`. -/
theorem two_add_profX_fst_nonneg (t : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 2 + (profX t s).1 := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0, profX_zero]
    simp [W1]
  · have := profX_fst_gt t s h0 hs.2
    linarith

/-- The radius is strictly positive at every `s ≠ 0` of the parameter rectangle. -/
theorem two_add_profX_fst_pos (t : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (h : s ≠ 0) :
    0 < 2 + (profX t s).1 := by
  have h0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h)
  have := profX_fst_gt t s h0 hs.2
  linarith

/-- The radius vanishes only at `s = 0`. -/
theorem two_add_profX_fst_eq_zero (t : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (h : 2 + (profX t s).1 = 0) : s = 0 := by
  by_contra hne
  have := two_add_profX_fst_pos t hs hne
  linarith

/-- **Injectivity of the corrected tube-coordinate map on the parameter rectangle.**
`eFunX t s` is the point of `ℝ³` with azimuth `t`, radius `2 + (profX t s).1` and
height `(profX t s).2`.  On the rectangle `(-π,π] × [0,1]` the map `(t,s) ↦ eFunX t s` is
injective up to the axis collapse: equal images force `s = s'`, and then either `s = 0`
(both points are the origin; the azimuth is not visible) or `t = t'`.

Route: write out the three components (`eFunX_eq_iff` in the imported file), square-add
the first two to get `(2 + u)² = (2 + u')²`, and use `profX_fst_gt`
(`0 < s → -2 < u`, proved in the imported file, so `2 + u = 0` forces `s = 0`) together
with `profX_injOn` (`Work.Drive.EpsForm.profX_injOn`, in the imported file: the profile is
injective in `s`, and only `s = 0` hits `W1`) and
`Work.Core.cos_sin_eq_iff_exists_int` (`cos t = cos t' ∧ sin t = sin t'` forces `t = t'`
because `t, t' ∈ (-π,π]`). -/
theorem eFunX_injOn_rect :
    ∀ t ∈ Set.Ioc (-Real.pi) Real.pi, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t' ∈ Set.Ioc (-Real.pi) Real.pi, ∀ s' ∈ Set.Icc (0 : ℝ) 1,
        eFunX t s = eFunX t' s' → s = s' ∧ (s = 0 ∨ t = t') := by
  intro t ht s hs t' ht' s' hs' heq
  obtain ⟨h0, h1, h2⟩ := (eFunX_eq_iff t s t' s').1 heq
  -- the two radii have equal squares (adding the squares of the first two components)
  have hsq : (2 + (profX t s).1) ^ 2 = (2 + (profX t' s').1) ^ 2 := by
    have hm0 : ((2 + (profX t s).1) * Real.cos t) ^ 2
        = ((2 + (profX t' s').1) * Real.cos t') ^ 2 := by rw [h0]
    have hm1 : ((2 + (profX t s).1) * Real.sin t) ^ 2
        = ((2 + (profX t' s').1) * Real.sin t') ^ 2 := by rw [h1]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq t']
  have hA : 0 ≤ 2 + (profX t s).1 := two_add_profX_fst_nonneg t hs
  have hA' : 0 ≤ 2 + (profX t' s').1 := two_add_profX_fst_nonneg t' hs'
  -- both radii are nonnegative, so equal squares give equal radii
  have hAA : 2 + (profX t s).1 = 2 + (profX t' s').1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · linarith
  by_cases hsz : s = 0
  · -- axis collapse: the point is the origin, so `s' = 0` as well
    have hA0 : 2 + (profX t s).1 = 0 := by
      rw [hsz, profX_zero]
      simp [W1]
    have hA'0 : 2 + (profX t' s').1 = 0 := by
      have h : (2 + (profX t' s').1) ^ 2 = 0 := by rw [← hsq, hA0]; ring
      exact sq_eq_zero_iff.mp h
    have hs'0 : s' = 0 := two_add_profX_fst_eq_zero t' hs' hA'0
    exact ⟨by rw [hsz, hs'0], Or.inl hsz⟩
  · -- the radius is positive, so the azimuth is visible
    have hpos : 0 < 2 + (profX t s).1 := two_add_profX_fst_pos t hs hsz
    have hpos' : 0 < 2 + (profX t' s').1 := by linarith [hAA, hpos]
    have hcos : Real.cos t = Real.cos t' := by
      have h := h0
      rw [hAA] at h
      exact mul_left_cancel₀ (ne_of_gt hpos') h
    have hsin : Real.sin t = Real.sin t' := by
      have h := h1
      rw [hAA] at h
      exact mul_left_cancel₀ (ne_of_gt hpos') h
    obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int t t').1 ⟨hcos, hsin⟩
    -- `t - t'` is a multiple of `2π` lying in `(-2π, 2π)`, so the multiple is `0`
    have hk_eq : (k : ℝ) * (2 * Real.pi) = t - t' := by linarith
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have hlt : |t - t'| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    have hk0 : k = 0 := by
      by_contra hkne
      have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hkne
      have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hk1
      have habs : |(k : ℝ)| * (2 * Real.pi) = |t - t'| := by
        rw [← hk_eq, abs_mul, abs_of_pos h2π]
      nlinarith
    have htt : t = t' := by
      rw [hk0] at hk
      simpa using hk
    -- same azimuth and same radius: the profile points agree
    have hprof : profX t' s = profX t' s' := by
      refine Prod.ext ?_ ?_
      · have hpt : (profX t' s).1 = (profX t s).1 := by rw [htt]
        linarith
      · have hpt : (profX t' s).2 = (profX t s).2 := by rw [htt]
        linarith
    have hss : s = s' := (profX_injOn ht'.1 ht'.2).1 hs hs' hprof
    exact ⟨hss, Or.inr htt⟩

end

end Work.Drive.EpsForm
