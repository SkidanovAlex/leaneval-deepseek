import Mathlib
import Submission.Work.Sweep.Defs

namespace Work.Sweep.PureInterval

open MeasureTheory Set ENNReal

/-- `min a b + max 0 (b - a) = b`: splitting a number off against a lower bound. -/
private lemma min_add_max_sub (a b : ℝ) : min a b + max 0 (b - a) = b := by
  rcases le_total b a with h | h
  · rw [min_eq_right h, max_eq_left (by linarith : b - a ≤ 0)]; ring
  · rw [min_eq_left h, max_eq_right (by linarith : 0 ≤ b - a)]; ring

/-- `max 0 x - max 0 (-x) = x`. -/
private lemma max_zero_sub_max_zero_neg (x : ℝ) : max 0 x - max 0 (-x) = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : 0 ≤ -x)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith : -x ≤ 0)]; ring

/-- `ofReal` only depends on the positive part. -/
private lemma ofReal_eq_ofReal_max_zero (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max 0 x) := by
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
  exact (max_eq_right bot_le).symm

/-- **The circular arc estimate.**  For `0 ≤ u₀ ≤ L` and `r ≥ 0`, the set of
points `u ∈ [0, L]` whose *circular* distance to `u₀` on the circle of
circumference `L` is at most `r` — i.e. `min |u - u₀| (L - |u - u₀|) ≤ r` —
has Lebesgue measure at most `2r`.

This is the pure one-dimensional estimate underlying the sweep argument: an arc
of circular radius `r` has length at most `2r`. -/
theorem volume_circ_arc_le (L u₀ r : ℝ) (hu₀ : 0 ≤ u₀) (hu₀L : u₀ ≤ L) (hr : 0 ≤ r) :
    MeasureTheory.volume {u : ℝ | u ∈ Set.Icc 0 L ∧ min |u - u₀| (L - |u - u₀|) ≤ r} ≤
      ENNReal.ofReal (2 * r) := by
  -- The three intervals covering the set: the "near" arc around `u₀`, and the two
  -- pieces at the ends `0`, `L` that are within circular distance `r` by wrapping.
  set P₀ := Set.Icc 0 L ∩ Set.Icc (u₀ - r) (u₀ + r) with hP0
  set P₁ := Set.Icc (u₀ + L - r) L with hP1
  set P₂ := Set.Icc 0 (u₀ - L + r) with hP2
  have hsub : {u : ℝ | u ∈ Set.Icc 0 L ∧ min |u - u₀| (L - |u - u₀|) ≤ r}
      ⊆ P₀ ∪ (P₁ ∪ P₂) := by
    intro u hu
    obtain ⟨huI, hum⟩ := hu
    rw [min_le_iff] at hum
    rcases hum with hd | hd
    · -- circular distance realized near `u₀`
      left
      rw [hP0]
      refine ⟨huI, ?_⟩
      rw [abs_le] at hd
      exact ⟨by linarith [hd.1], by linarith [hd.2]⟩
    · -- circular distance realized by wrapping around the ends
      right
      have hd' : L - r ≤ |u - u₀| := by linarith
      rcases le_total u₀ u with huv | huv
      · left
        rw [hP1]
        rw [abs_of_nonneg (by linarith : 0 ≤ u - u₀)] at hd'
        exact ⟨by linarith, huI.2⟩
      · right
        have habs : |u - u₀| = u₀ - u := by
          rw [abs_of_nonpos (by linarith : u - u₀ ≤ 0)]; ring
        rw [hP2]
        rw [habs] at hd'
        exact ⟨huI.1, by linarith⟩
  -- Exact measures of the three intervals.
  have hvolP0 : MeasureTheory.volume P₀
      = ENNReal.ofReal (min L (u₀ + r) - max 0 (u₀ - r)) := by
    rw [hP0, Set.Icc_inter_Icc, Real.volume_Icc]
  have hvolP1 : MeasureTheory.volume P₁ = ENNReal.ofReal (max 0 (r - u₀)) := by
    rw [hP1, Real.volume_Icc, show L - (u₀ + L - r) = r - u₀ by ring]
    exact ofReal_eq_ofReal_max_zero (r - u₀)
  have hvolP2 : MeasureTheory.volume P₂ = ENNReal.ofReal (max 0 (u₀ - L + r)) := by
    rw [hP2, Real.volume_Icc, show u₀ - L + r - 0 = u₀ - L + r by ring]
    exact ofReal_eq_ofReal_max_zero (u₀ - L + r)
  have hunion : MeasureTheory.volume (P₁ ∪ P₂)
      ≤ MeasureTheory.volume P₁ + MeasureTheory.volume P₂ :=
    MeasureTheory.measure_union_le P₁ P₂
  have hvol : MeasureTheory.volume {u : ℝ | u ∈ Set.Icc 0 L ∧ min |u - u₀| (L - |u - u₀|) ≤ r}
      ≤ ENNReal.ofReal (min L (u₀ + r) - max 0 (u₀ - r))
        + ENNReal.ofReal (max 0 (r - u₀)) + ENNReal.ofReal (max 0 (u₀ - L + r)) := by
    calc MeasureTheory.volume {u : ℝ | u ∈ Set.Icc 0 L ∧ min |u - u₀| (L - |u - u₀|) ≤ r}
        ≤ MeasureTheory.volume (P₀ ∪ (P₁ ∪ P₂)) := MeasureTheory.measure_mono hsub
      _ ≤ MeasureTheory.volume P₀ + MeasureTheory.volume (P₁ ∪ P₂) :=
            MeasureTheory.measure_union_le _ _
      _ ≤ MeasureTheory.volume P₀ + (MeasureTheory.volume P₁ + MeasureTheory.volume P₂) :=
            add_le_add le_rfl hunion
      _ = ENNReal.ofReal (min L (u₀ + r) - max 0 (u₀ - r))
            + ENNReal.ofReal (max 0 (r - u₀)) + ENNReal.ofReal (max 0 (u₀ - L + r)) := by
            rw [hvolP0, hvolP1, hvolP2, add_assoc]
  -- The three exact measures total exactly `2r`.
  have hL0 : 0 ≤ L := le_trans hu₀ hu₀L
  have ha : 0 ≤ min L (u₀ + r) - max 0 (u₀ - r) := by
    have h1 : max 0 (u₀ - r) ≤ min L (u₀ + r) := by
      apply max_le
      · exact le_min hL0 (by linarith)
      · exact le_min (by linarith) (by linarith)
    linarith
  have hb : 0 ≤ max 0 (r - u₀) := le_max_left 0 (r - u₀)
  have hc : 0 ≤ max 0 (u₀ - L + r) := le_max_left 0 (u₀ - L + r)
  have habc : (min L (u₀ + r) - max 0 (u₀ - r)) + max 0 (r - u₀) + max 0 (u₀ - L + r)
      = 2 * r := by
    have h1 := min_add_max_sub L (u₀ + r)
    have h2 := max_zero_sub_max_zero_neg (r - u₀)
    rw [show -(r - u₀) = u₀ - r by ring] at h2
    rw [show u₀ - L + r = (u₀ + r) - L by ring]
    linarith
  have hsum : ENNReal.ofReal (min L (u₀ + r) - max 0 (u₀ - r))
        + ENNReal.ofReal (max 0 (r - u₀)) + ENNReal.ofReal (max 0 (u₀ - L + r))
      = ENNReal.ofReal (2 * r) := by
    rw [← ENNReal.ofReal_add ha hb,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (min L (u₀ + r) - max 0 (u₀ - r))
          + max 0 (r - u₀)) hc,
        habc]
  exact le_trans hvol (le_of_eq hsum)

end Work.Sweep.PureInterval
