import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.cthickening_pos_of_isCompact
import Submission.Work.Diff.EXT.quadForm_pos_of_unit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A positive-definite tube across the seam `t = 0`

This file proves `Work.Diff.EXT.posDef_tube_of_continuous_seam`: if a matrix-valued function
`W : ℝ × E → MatE` (`E` finite dimensional over `ℝ`) is continuous on the slab
`Ioo (-a) a ×ˢ U` (`a > 0`, `U` open) and its quadratic form at the *seam* `t = 0` is positive
definite on all of `U`, then on a whole two-sided tube `Ioo (-a') a' ×ˢ U'` around `{0} × {y₀}`
the quadratic form is strictly positive at every nonzero coefficient vector.

The proof has three ingredients.

* `continuousOn_quadForm`: the function
  `p ↦ ∑ i, ∑ j, p.2 i * p.2 j * W p.1 i j` is continuous on `(Ioo (-a) a ×ˢ U) ×ˢ univ`
  (finite sums of products of continuous functions).
* `Work.Diff.EXT.cthickening_pos_of_isCompact`: on a compact set contained in an open set where a
  function is continuous, strict positivity upgrades to positivity on a `cthickening` of the compact
  set.  It is applied to the compact set `{0} ×ˢ closedBall y₀ (r/2) ×ˢ sphere 0 1`.
* `Work.Diff.EXT.quadForm_pos_of_unit`: positivity on the unit sphere upgrades to all nonzero
  vectors by the degree-two homogeneity `Q (c • v) = c ^ 2 * Q v` of the quadratic form.

Since the finrank-`0` case has no nonzero coefficient vector, the statement is vacuous there and is
handled by a `Subsingleton` argument.
-/

namespace Work.Diff.EXT

private lemma mem_sphere_zero_one_iff {n : ℕ} {v : Fin n → ℝ} :
    v ∈ Metric.sphere (0 : Fin n → ℝ) 1 ↔ ‖v‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]

private lemma continuousOn_quadForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ℝ} {W : ℝ × E → MatE (E := E)} {U : Set E}
    (hWc : ContinuousOn W (Set.Ioo (-a) a ×ˢ U)) :
    ContinuousOn (fun p : (ℝ × E) × (Fin (Module.finrank ℝ E) → ℝ) =>
      ∑ i, ∑ j, p.2 i * p.2 j * W p.1 i j) ((Set.Ioo (-a) a ×ˢ U) ×ˢ Set.univ) := by
  have hWp : ContinuousOn (fun p : (ℝ × E) × (Fin (Module.finrank ℝ E) → ℝ) => W p.1)
      ((Set.Ioo (-a) a ×ˢ U) ×ˢ Set.univ) :=
    hWc.comp continuous_fst.continuousOn (fun p hp => hp.1)
  refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
  refine continuousOn_finsetSum Finset.univ (fun j _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact (continuous_apply i).comp_continuousOn (continuous_snd.continuousOn)
  · exact (continuous_apply j).comp_continuousOn (continuous_snd.continuousOn)
  · exact ((continuous_apply j).comp (continuous_apply i)).comp_continuousOn hWp

theorem posDef_tube_of_continuous_seam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ℝ} (ha : 0 < a) {W : ℝ × E → Work.Diff.EXT.MatE (E := E)} {U : Set E}
    (hU : IsOpen U) {y₀ : E} (hy₀ : y₀ ∈ U)
    (hWc : ContinuousOn W ((Set.Ioo (-a) a) ×ˢ U))
    (hW0 : ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
        0 < ∑ i, ∑ j, v i * v j * W (0, y) i j) :
    ∃ a' > 0, ∃ U' : Set E, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧
      ∀ t ∈ Set.Ioo (-a') a', ∀ y ∈ U', ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
        0 < ∑ i, ∑ j, v i * v j * W (t, y) i j := by
  classical
  by_cases hNT : Nontrivial (Fin (Module.finrank ℝ E) → ℝ)
  · -- In the nontrivial case there is a unit vector, and a compact set of unit vectors to
    -- which the positivity at the seam can be propagated.
    obtain ⟨e, he⟩ : ∃ e : Fin (Module.finrank ℝ E) → ℝ, ‖e‖ = 1 := by
      obtain ⟨x, y, hxy⟩ := @exists_pair_ne (Fin (Module.finrank ℝ E) → ℝ) hNT
      have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
      refine ⟨‖x - y‖⁻¹ • (x - y), ?_⟩
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
      simpa using norm_ne_zero_iff.mpr hne
    -- a closed ball around `y₀` inside `U`
    obtain ⟨r, hr, hrc⟩ : ∃ r > 0, Metric.closedBall y₀ (r / 2) ⊆ U := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy₀)
      exact ⟨ε, hε, (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
    have hKcomp : IsCompact ((({0} : Set ℝ) ×ˢ Metric.closedBall y₀ (r / 2)) ×ˢ
        Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1) :=
      (isCompact_singleton.prod (isCompact_closedBall y₀ (r / 2))).prod
        (isCompact_sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1)
    have hKne : ((({0} : Set ℝ) ×ˢ Metric.closedBall y₀ (r / 2)) ×ˢ
        Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1).Nonempty :=
      ⟨((0, y₀), e), Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨by simp,
        Metric.mem_closedBall.mpr (by rw [dist_self]; linarith)⟩,
        mem_sphere_zero_one_iff.mpr he⟩⟩
    have hKsub : ((({0} : Set ℝ) ×ˢ Metric.closedBall y₀ (r / 2)) ×ˢ
        Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1) ⊆
        (Set.Ioo (-a) a ×ˢ U) ×ˢ Set.univ := by
      rintro ⟨⟨t, y⟩, v⟩ hp
      rw [Set.mem_prod] at hp
      obtain ⟨hp1, -⟩ := hp
      rw [Set.mem_prod] at hp1
      obtain ⟨ht, hyc⟩ := hp1
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨⟨neg_lt_zero.mpr ha, ha⟩, hrc hyc⟩,
        Set.mem_univ _⟩
    have hKpos : ∀ p ∈ ((({0} : Set ℝ) ×ˢ Metric.closedBall y₀ (r / 2)) ×ˢ
        Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1),
        0 < ∑ i, ∑ j, p.2 i * p.2 j * W p.1 i j := by
      rintro ⟨⟨t, y⟩, v⟩ hp
      rw [Set.mem_prod] at hp
      obtain ⟨hp1, hvsph⟩ := hp
      rw [Set.mem_prod] at hp1
      obtain ⟨ht, hyc⟩ := hp1
      rw [Set.mem_singleton_iff] at ht
      subst ht
      refine hW0 y (hrc hyc) v (fun h0 => ?_)
      rw [h0] at hvsph
      simp at hvsph
    have hAopen : IsOpen ((Set.Ioo (-a) a ×ˢ U) ×ˢ
        (Set.univ : Set (Fin (Module.finrank ℝ E) → ℝ))) :=
      (isOpen_Ioo.prod hU).prod isOpen_univ
    have hcontF := continuousOn_quadForm (E := E) (a := a) (W := W) (U := U) hWc
    obtain ⟨δ, hδpos, hδ⟩ :=
      cthickening_pos_of_isCompact hKcomp hKne hAopen hKsub hcontF hKpos
    refine ⟨min δ a, lt_min hδpos ha, Metric.ball y₀ (r / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by linarith), Metric.ball_subset_closedBall.trans hrc, ?_⟩
    intro t ht y hy v hv
    -- the tube points are within `δ` of the compact set, hence in its `cthickening`
    have htabs : |t| ≤ δ := by
      obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp ht
      exact le_of_lt (lt_of_lt_of_le (abs_lt.mpr ⟨h1, h2⟩) (min_le_left δ a))
    have hunit : ∀ w : Fin (Module.finrank ℝ E) → ℝ, ‖w‖ = 1 →
        0 < ∑ i, ∑ j, w i * w j * W (t, y) i j := by
      intro w hw
      have hmem : ((t, y), w) ∈ Metric.cthickening δ ((({0} : Set ℝ) ×ˢ
          Metric.closedBall y₀ (r / 2)) ×ˢ
          Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1) := by
        refine Metric.mem_cthickening_of_dist_le ((t, y), w) ((0, y), w) δ _ ?_ ?_
        · exact Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨by simp, Metric.ball_subset_closedBall hy⟩,
            mem_sphere_zero_one_iff.mpr hw⟩
        · rw [Prod.dist_eq, Prod.dist_eq]
          refine max_le (max_le ?_ ?_) ?_
          · rw [Real.dist_eq, sub_zero]; exact htabs
          · rw [dist_self]; linarith
          · rw [dist_self]; linarith
      exact hδ ((t, y), w) hmem
    exact quadForm_pos_of_unit (p := (t, y)) hunit v hv
  · -- no nonzero coefficient vector: the claim is vacuous
    haveI : Subsingleton (Fin (Module.finrank ℝ E) → ℝ) :=
      not_nontrivial_iff_subsingleton.mp hNT
    exact ⟨a, ha, U, hU, hy₀, subset_rfl,
      fun t ht y hy v hv => absurd (Subsingleton.elim v 0) hv⟩

end Work.Diff.EXT
