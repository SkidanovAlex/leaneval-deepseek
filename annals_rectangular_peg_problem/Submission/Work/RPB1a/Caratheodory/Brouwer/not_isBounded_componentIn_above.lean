import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs

namespace Work.RPB1a.Caratheodory.Brouwer

set_option autoImplicit false

/-- A point of `K`'s complement above the topmost point of `K` on the vertical line `x = 0` lies in
an unbounded component. -/
theorem not_isBounded_componentIn_above
    (K : Set (ℝ × ℝ)) (hK : K ⊆ Work.RPB1a.Caratheodory.Brouwer.rect)
    (m w : ℝ × ℝ) (hm : ∀ p ∈ K, p.1 = 0 → p.2 ≤ m.2)
    (hw1 : w.1 = 0) (hwm : m.2 < w.2) (hwK : w ∉ K) :
    ¬ Bornology.IsBounded (connectedComponentIn (Kᶜ) w) := by
  -- The vertical ray `R = {(0,t) | t ≥ w.2}` is disjoint from `K`: a point of `K` on the line
  -- `x = 0` has second coordinate at most `m.2 < w.2`.  It is connected, contains `w`, and is
  -- unbounded, so it forces the component of `w` to be unbounded.
  -- (The hypotheses `hK` and `hwK` are not needed: the ray argument below shows that `w ∉ K`
  -- directly, and it never uses the hypothesis that `K` is contained in the rectangle.)
  have _ : w ∉ K := hwK
  have _ : K ⊆ Work.RPB1a.Caratheodory.Brouwer.rect := hK
  intro hbdd
  set R : Set (ℝ × ℝ) := (fun t : ℝ => ((0 : ℝ), t)) '' Set.Ici w.2 with hRdef
  have hRpre : IsPreconnected R := by
    rw [hRdef]
    exact isPreconnected_Ici.image _ (continuous_const.prodMk continuous_id).continuousOn
  have hwR : w ∈ R := by
    rw [hRdef]
    exact ⟨w.2, Set.mem_Ici.mpr (le_refl _), Prod.ext (by simp [hw1]) rfl⟩
  have hRsub : R ⊆ Kᶜ := by
    intro p hp
    rw [hRdef] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    intro hpK
    have h1 : t ≤ m.2 := hm (0, t) hpK rfl
    have h2 : w.2 ≤ t := ht
    linarith
  have hRcc : R ⊆ connectedComponentIn (Kᶜ) w :=
    hRpre.subset_connectedComponentIn hwR hRsub
  have hbR : Bornology.IsBounded R := hbdd.subset hRcc
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hbR
  set t : ℝ := max w.2 (max 0 (C + 1)) with ht
  have ht_ge : w.2 ≤ t := le_max_left _ _
  have ht0 : 0 ≤ t := le_trans (le_max_left (0 : ℝ) (C + 1)) (le_max_right w.2 _)
  have htC : C < t := by
    have h2 : C + 1 ≤ max (0 : ℝ) (C + 1) := le_max_right _ _
    have h3 : max (0 : ℝ) (C + 1) ≤ t := le_max_right _ _
    linarith
  have hmem : ((0 : ℝ), t) ∈ R := by
    rw [hRdef]; exact ⟨t, Set.mem_Ici.mpr ht_ge, rfl⟩
  have hdist : dist ((0 : ℝ), t) (0 : ℝ × ℝ) = t := by
    simp only [dist_eq_norm, sub_zero, Prod.norm_def, norm_zero, Real.norm_eq_abs]
    rw [max_eq_right (abs_nonneg t), abs_of_nonneg ht0]
  have hlt := hC hmem
  rw [Metric.mem_ball, hdist] at hlt
  linarith

end Work.RPB1a.Caratheodory.Brouwer
