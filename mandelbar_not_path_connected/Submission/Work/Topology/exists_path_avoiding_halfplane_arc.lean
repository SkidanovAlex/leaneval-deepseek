import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Topology

open Set Metric

/-- The point of the plane with real part `u` and imaginary part `s * (1 - u ^ 2) / 2`.
For `s = -1` (resp. `s = 1`) and `u ^ 2 < 1` it is a point of the open unit disc lying in the
open lower (resp. upper) half plane. -/
noncomputable def arc (s u : ℝ) : ℂ := ⟨u, s * (1 - u^2) / 2⟩

lemma arc_re (s u : ℝ) : (arc s u).re = u := rfl

lemma arc_im (s u : ℝ) : (arc s u).im = s * (1 - u^2) / 2 := rfl

/-- The structure constructor of `ℂ` compared with the `a + b * I` presentation. -/
lemma arc_eq_ofReal_add (u b : ℝ) : (⟨u, b⟩ : ℂ) = (u : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- `arc s` is continuous, `s` being fixed. -/
lemma continuous_arc (s : ℝ) : Continuous (arc s) := by
  have h : arc s = fun (u : ℝ) => (u : ℂ) + (((s * (1 - u^2) / 2 : ℝ)) : ℂ) * Complex.I := by
    funext u
    rw [arc]
    exact arc_eq_ofReal_add u (s * (1 - u^2) / 2)
  rw [h]
  fun_prop

lemma normSq_arc_neg (u : ℝ) : Complex.normSq (arc (-1) u) = ((1 + u^2) / 2) ^ 2 := by
  simp only [Complex.normSq_apply, arc]
  ring

lemma normSq_arc_pos (u : ℝ) : Complex.normSq (arc 1 u) = ((1 + u^2) / 2) ^ 2 := by
  simp only [Complex.normSq_apply, arc]
  ring

/-- The lower arc lies strictly inside the open unit disc. -/
lemma norm_arc_neg_lt_one (u : ℝ) (hu : u ^ 2 < 1) : ‖arc (-1) u‖ < 1 := by
  have h1 := normSq_arc_neg u
  rw [← Complex.sq_norm] at h1
  have h2 : ((1 + u ^ 2) / 2) ^ 2 < 1 := by nlinarith
  nlinarith [norm_nonneg (arc (-1) u)]

/-- The upper arc lies strictly inside the open unit disc. -/
lemma norm_arc_pos_lt_one (u : ℝ) (hu : u ^ 2 < 1) : ‖arc 1 u‖ < 1 := by
  have h1 := normSq_arc_pos u
  rw [← Complex.sq_norm] at h1
  have h2 : ((1 + u ^ 2) / 2) ^ 2 < 1 := by nlinarith
  nlinarith [norm_nonneg (arc 1 u)]

lemma arc_neg_im_neg (u : ℝ) (hu : u ^ 2 < 1) : (arc (-1) u).im < 0 := by
  simp only [arc]
  nlinarith

lemma arc_one_im_pos (u : ℝ) (hu : u ^ 2 < 1) : 0 < (arc 1 u).im := by
  simp only [arc]
  nlinarith

/-- **A path from `-1` to `1` inside the open disc avoiding an arc that lies in one closed half
plane.**  If the image of `β` is contained in the closed upper or in the closed lower half plane,
then the opposite open half plane carries a path from `-1` to `1` whose interior lies in the open
unit disc and which misses the image of `β` entirely. -/
theorem exists_path_avoiding_halfplane_arc {β : C(Set.Icc (0:ℝ) 1, ℂ)}
    (hsgn : (∀ t : Set.Icc (0:ℝ) 1, 0 ≤ (β t).im) ∨
      (∀ t : Set.Icc (0:ℝ) 1, (β t).im ≤ 0)) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℂ), γ 0 = -1 ∧ γ 1 = 1 ∧
      ∀ t : Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 →
        γ t ∈ Metric.ball (0:ℂ) 1 ∧ γ t ∉ Set.range β := by
  have hcont : Continuous fun t : Set.Icc (0:ℝ) 1 => 2 * (t : ℝ) - 1 := by fun_prop
  rcases hsgn with hup | hdn
  · -- the graph of `β` stays in the closed upper half plane: use the lower arc
    refine ⟨⟨fun t => arc (-1) (2 * (t : ℝ) - 1), (continuous_arc (-1)).comp hcont⟩, ?_, ?_, ?_⟩
    · apply Complex.ext <;> norm_num [arc]
    · apply Complex.ext <;> norm_num [arc]
    · intro t ht0 ht1
      have h0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun h => ht0 (Subtype.ext h.symm))
      have h1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht1 (Subtype.ext h))
      have hu : (2 * (t : ℝ) - 1) ^ 2 < 1 := by nlinarith
      constructor
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact norm_arc_neg_lt_one _ hu
      · rintro ⟨s, hs⟩
        have hβ : 0 ≤ (β s).im := hup s
        have hγ : (β s).im < 0 := by
          rw [hs]
          exact arc_neg_im_neg _ hu
        linarith
  · -- the graph of `β` stays in the closed lower half plane: use the upper arc
    refine ⟨⟨fun t => arc 1 (2 * (t : ℝ) - 1), (continuous_arc 1).comp hcont⟩, ?_, ?_, ?_⟩
    · apply Complex.ext <;> norm_num [arc]
    · apply Complex.ext <;> norm_num [arc]
    · intro t ht0 ht1
      have h0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun h => ht0 (Subtype.ext h.symm))
      have h1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht1 (Subtype.ext h))
      have hu : (2 * (t : ℝ) - 1) ^ 2 < 1 := by nlinarith
      constructor
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact norm_arc_pos_lt_one _ hu
      · rintro ⟨s, hs⟩
        have hβ : (β s).im ≤ 0 := hdn s
        have hγ : 0 < (β s).im := by
          rw [hs]
          exact arc_one_im_pos _ hu
        linarith

end Work.Topology
