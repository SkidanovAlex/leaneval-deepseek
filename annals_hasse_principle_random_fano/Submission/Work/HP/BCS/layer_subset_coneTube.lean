import Mathlib
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.exists_coneSurf_le_dist
import Submission.Work.HP.BCS.lt_norm_of_lt_abs_inner

/-!
# `Work.HP.BCS.layer_subset_coneTube`

A point `x` of the `R`-boundary layer of the cone slice
`K_T = {y : |⟪a,y⟫| ≤ c‖y‖, |⟪b,y⟫| ≤ d‖y‖, ‖y‖ ≤ T}` satisfies `‖x‖ ≤ T + R`, and either

* `T - 3R < ‖x‖` (the layer only reflects the truncation `‖y‖ ≤ T`), or
* the cone surface `{|⟪a,y⟫| = c‖y‖}` passes within `3R` of `x` (and then necessarily `c < ‖a‖`), or
* the cone surface `{|⟪b,y⟫| = d‖y‖}` does.

## Proof

Since `x` lies in `K_T + B_R`, write `x = u + v` with `u ∈ K_T` and `‖v‖ < R`; the triangle
inequality gives `‖x‖ ≤ T + R` and `R > 0`. Since `x` is *not* in the erosion
`{z : z + B_R ⊆ K_T}`, there is `w` with `‖w‖ < R` and `t := x + w ∉ K_T`.

* If `‖t‖ > T`, then `‖x‖ ≥ ‖t‖ - ‖w‖ > T - R > T - 3R`.
* Otherwise `‖t‖ ≤ T`, so `t ∉ K_T` forces `t ∉ coneSet a c` or `t ∉ coneSet b d`; say the
  former. Then `c‖t‖ < |⟪a,t⟫|`, so Cauchy–Schwarz (`lt_norm_of_lt_abs_inner`) gives
  `c < ‖a‖`; and since `u ∈ coneSet a c` while `t ∉ coneSet a c`, the continuous function
  `|⟪a,·⟫| - c‖·‖` changes sign on the segment from `u` to `t`, so by the intermediate value
  theorem the surface `{|⟪a,y⟫| = c‖y‖}` meets the segment
  (`exists_coneSurf_le_dist`), at a point `y` with
  `‖x - y‖ ≤ max (‖x - u‖, ‖x - t‖) < R ≤ 3R`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.BCS

theorem layer_subset_coneTube (k : ℕ) (a b : EuclideanSpace ℝ (Fin k)) (c d T R : ℝ)
    {x : EuclideanSpace ℝ (Fin k)}
    (hx : x ∈ Work.HP.BCS.layer {y : EuclideanSpace ℝ (Fin k) |
      y ∈ Work.HP.BCS.coneSet a c ∧ y ∈ Work.HP.BCS.coneSet b d ∧ ‖y‖ ≤ T} R) :
    ‖x‖ ≤ T + R ∧
      (T - 3 * R < ‖x‖ ∨ (c < ‖a‖ ∧ x ∈ Work.HP.BCS.coneTube a c (T + R) (3 * R))
        ∨ (d < ‖b‖ ∧ x ∈ Work.HP.BCS.coneTube b d (T + R) (3 * R))) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin k)) :=
    {y : EuclideanSpace ℝ (Fin k) | y ∈ coneSet a c ∧ y ∈ coneSet b d ∧ ‖y‖ ≤ T} with hKdef
  unfold layer at hx
  rw [Set.mem_sdiff] at hx
  obtain ⟨hxmem, hxnot⟩ := hx
  -- `x = u + v` with `u ∈ K` and `‖v‖ < R`
  rw [Set.mem_add] at hxmem
  obtain ⟨u, huK, v, hvball, huv⟩ := hxmem
  have hvlt : ‖v‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hvball; exact hvball
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg v) hvlt
  -- `x` is not in the erosion, so `x + w ∉ K` for some `‖w‖ < R`
  simp only [erode, Set.mem_ofPred_eq] at hxnot
  push Not at hxnot
  obtain ⟨w, hwball, hwK⟩ := hxnot
  have hwlt : ‖w‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hwball; exact hwball
  rw [hKdef] at huK
  simp only [Set.mem_ofPred_eq] at huK
  have huC : |inner ℝ a u| ≤ c * ‖u‖ := huK.1
  have huD : |inner ℝ b u| ≤ d * ‖u‖ := huK.2.1
  have huT : ‖u‖ ≤ T := huK.2.2
  -- the norm bound
  have hnorm_le : ‖x‖ ≤ T + R := by
    rw [← huv]
    calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
      _ ≤ T + R := add_le_add huT (le_of_lt hvlt)
  set t : EuclideanSpace ℝ (Fin k) := x + w with ht
  rw [hKdef] at hwK
  simp only [Set.mem_ofPred_eq] at hwK
  have hxw : ‖x - t‖ ≤ R := by
    have h1 : x - t = -w := by rw [ht]; simp
    rw [h1, norm_neg]; exact le_of_lt hwlt
  have hxu : ‖x - u‖ ≤ R := by
    have h1 : x - u = v := by rw [← huv]; simp
    rw [h1]; exact le_of_lt hvlt
  refine ⟨hnorm_le, ?_⟩
  by_cases hTle : ‖t‖ ≤ T
  · -- `t ∉ K` and `‖t‖ ≤ T`: one of the two cone conditions fails
    have hdisj : t ∉ coneSet a c ∨ t ∉ coneSet b d := by
      by_contra h
      push Not at h
      exact hwK ⟨h.1, h.2, hTle⟩
    rcases hdisj with hac | hbd
    · -- the `a`-cone
      have htgt : c * ‖t‖ < |inner ℝ a t| := by
        simp only [coneSet, Set.mem_ofPred_eq, not_le] at hac; exact hac
      have hclt : c < ‖a‖ := lt_norm_of_lt_abs_inner a c htgt
      have hsurf : ∃ y, |inner ℝ a y| = c * ‖y‖ ∧ ‖x - y‖ ≤ 3 * R := by
        obtain ⟨y, hy1, hy2⟩ := exists_coneSurf_le_dist a c R huC htgt hxu hxw
        exact ⟨y, hy1, le_trans hy2 (by linarith)⟩
      exact Or.inr (Or.inl ⟨hclt, hnorm_le, hsurf⟩)
    · -- the `b`-cone
      have htgt : d * ‖t‖ < |inner ℝ b t| := by
        simp only [coneSet, Set.mem_ofPred_eq, not_le] at hbd; exact hbd
      have hdlt : d < ‖b‖ := lt_norm_of_lt_abs_inner b d htgt
      have hsurf : ∃ y, |inner ℝ b y| = d * ‖y‖ ∧ ‖x - y‖ ≤ 3 * R := by
        obtain ⟨y, hy1, hy2⟩ := exists_coneSurf_le_dist b d R huD htgt hxu hxw
        exact ⟨y, hy1, le_trans hy2 (by linarith)⟩
      exact Or.inr (Or.inr ⟨hdlt, hnorm_le, hsurf⟩)
  · -- `‖t‖ > T`: the norm lower bound
    push Not at hTle
    left
    have hxlow : ‖x‖ ≥ ‖t‖ - ‖w‖ := by
      have h1 : ‖t‖ ≤ ‖t - w‖ + ‖w‖ := by
        have h2 := norm_add_le (t - w) w
        rwa [sub_add_cancel] at h2
      have h3 : ‖x‖ = ‖t - w‖ := by
        have h4 : x = t - w := by rw [ht]; simp
        rw [h4]
      rw [h3]; linarith
    linarith

end Work.HP.BCS
