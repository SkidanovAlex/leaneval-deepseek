import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs

namespace Work.RPB1a.Caratheodory.Brouwer

set_option autoImplicit false

open Set Metric

/-- The downward vertical ray from `w`: the set of points on the line `x = 0` whose second
coordinate is at most `w.2`.  It is the image of the interval `Iic w.2` under the (isometric)
embedding `t ↦ (0, t)`, hence preconnected, and it is unbounded. -/
private theorem isPreconnected_ray_down (w : ℝ × ℝ) :
    IsPreconnected {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} := by
  have himg : (fun t : ℝ => ((0 : ℝ), t)) '' (Set.Iic w.2)
      = {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} := by
    ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rfl, ht⟩
    · rintro ⟨h1, h2⟩
      exact ⟨p.2, h2, by rw [← h1]⟩
  rw [← himg]
  exact isPreconnected_Iic.image _
    (continuous_const.prodMk continuous_id).continuousOn

/-- A point of `K`'s complement below the bottommost point of `K` on the vertical line `x = 0` lies
in an unbounded component. -/
theorem not_isBounded_componentIn_below
    (K : Set (ℝ × ℝ)) (hK : K ⊆ Work.RPB1a.Caratheodory.Brouwer.rect)
    (j w : ℝ × ℝ) (hj : ∀ p ∈ K, p.1 = 0 → j.2 ≤ p.2)
    (hw1 : w.1 = 0) (hwj : w.2 < j.2) (hwK : w ∉ K) :
    ¬ Bornology.IsBounded (connectedComponentIn (Kᶜ) w) := by
  have _hK := hK
  have _hwK := hwK
  -- The downward ray from `w` avoids `K`, since every point of `K` on `x = 0` lies above `j`.
  have hSconn : IsPreconnected {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} :=
    isPreconnected_ray_down w
  have hwS : w ∈ {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} := ⟨hw1, le_refl w.2⟩
  have hSsub : {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} ⊆ Kᶜ := by
    intro p hp hpK
    have hle : j.2 ≤ p.2 := hj p hpK hp.1
    linarith [hp.2, hle, hwj]
  -- Hence the ray lies in the connected component of `w` in `Kᶜ`; it is unbounded, so that
  -- component is unbounded.
  have hsub : {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} ⊆ connectedComponentIn (Kᶜ) w :=
    hSconn.subset_connectedComponentIn hwS hSsub
  intro hb
  have hbS : Bornology.IsBounded {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} := hb.subset hsub
  obtain ⟨r, hrpos, hrball⟩ := hbS.subset_ball_lt 0 ((0 : ℝ), (0 : ℝ))
  set t : ℝ := w.2 - (r + |w.2| + 1) with htdef
  have htle : t ≤ w.2 := by
    rw [htdef]
    have : 0 ≤ r + |w.2| + 1 := by positivity
    linarith
  have hpS : ((0 : ℝ), t) ∈ {p : ℝ × ℝ | p.1 = 0 ∧ p.2 ≤ w.2} := ⟨rfl, htle⟩
  have hball := hrball hpS
  rw [Metric.mem_ball, Prod.dist_eq] at hball
  simp only [Real.dist_eq, sub_zero, abs_zero, max_eq_right (abs_nonneg t)] at hball
  have htneg : t < 0 := by
    rw [htdef]
    linarith [le_abs_self w.2, hrpos]
  have habs : |t| = r + |w.2| + 1 - w.2 := by
    rw [abs_of_neg htneg, htdef]; ring
  have hge : r < |t| := by
    rw [habs]
    linarith [le_abs_self w.2]
  linarith

end Work.RPB1a.Caratheodory.Brouwer
