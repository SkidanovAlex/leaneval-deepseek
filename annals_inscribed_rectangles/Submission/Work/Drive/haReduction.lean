import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.clampedSweep

/-!
# The radial non-degeneracy `ha` of the triple-count engine, discharged

The assembled parity identity of the counting lane, `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion`
(`planeClassDeriv_eq_mfderiv.lean`), carries four hypotheses: `ha` (radial non-degeneracy of the
sweeps at a triple point), `hc` (the plane presentation is an immersion), `hV` (the three class
planes are in general position) and `hface` (boundary genericity).  `GENERICITY_ASSEMBLY_STATUS.md`
§5 lists `ha` as "elementary: it holds as soon as `deriv ψ ≠ 0` and `r k ≠ c k`".  This file proves
that, and proves that the levels `c` can always be chosen so that `r k ≠ c k` holds:

* `Work.Drive.ha_of_deriv_ne_of_level_ne` — if `deriv ψ` does not vanish on the parameter interval
  `[0,1]` and no point of the `k`-th plane has level `c k`, then `ha` holds;
* `Work.Drive.exists_common_level_ne_levelOf` — if the union of the level ranges of the planes is
  bounded above (which holds whenever the planes are compact, i.e. for the concrete folded planes
  `diskPlane Q`), then there is a single positive level avoiding all of them.

So `ha` is not an extra geometric input: it is `deriv ψ ≠ 0` (a choice of the sweep profile) plus a
choice of the (common, so that the end faces of the three sweeps meet in one level `ℝP³`) level.
-/

namespace Work.Drive

/-- **`ha` from a non-vanishing sweep derivative and a level missed by the planes.**  This is exactly
the `ha` hypothesis of `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion`,
with the radial coefficient `deriv ψ (x k 2) * (log (c k) - log (levelOf (P k …)))` of the `k`-th
sweep shown non-zero. -/
theorem ha_of_deriv_ne_of_level_ne
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hψ : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcpos : ∀ k, 0 < c k)
    (hclev : ∀ k (y : EuclideanSpace ℝ (Fin 2)), levelOf (P k y) ≠ c k) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      (clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1)) →
      (clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2)) →
      ∀ k, deriv ψ (x k 2) * (Real.log (c k)
        - Real.log (levelOf (P k (mk2 (x k 0) (x k 1))))) ≠ 0 := by
  intro x hx _ _ k
  refine mul_ne_zero (hψ (x k 2) ((hx k) 2)) ?_
  rw [sub_ne_zero]
  intro hlog
  exact hclev k _ ((Real.log_injOn_pos (Set.mem_Ioi.mpr (hcpos k))
    (Set.mem_Ioi.mpr (levelOf_pos _)) hlog).symm)

/-- **A common level above the level ranges.**  If the union of the level ranges of the planes
`P k` is bounded above, there is a single positive level `c` not attained by any of them.  For the
concrete planes of the chain route (`P k = rotCapping u k ∘ diskPlane Q`, with compact images) the
boundedness hypothesis is `IsCompact.bddAbove` of the level range.

A *common* `c` is what the end computation of `ENDS_AND_SEAMS_NOTES.md` §2 needs: the three bottom
faces are then shadows in one and the same level `≅ ℝP³`, whose triple intersection number is
`1`. -/
theorem exists_common_level_ne_levelOf {ι : Type*} [Nonempty ι]
    (P : ι → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hbdd : BddAbove (Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => levelOf (P p.1 p.2)))) :
    ∃ c : ℝ, 0 < c ∧ ∀ k y, levelOf (P k y) ≠ c := by
  refine ⟨(⨆ p : ι × EuclideanSpace ℝ (Fin 2), levelOf (P p.1 p.2)) + 1, ?_, ?_⟩
  · have h := le_ciSup hbdd ((Classical.arbitrary ι), (0 : EuclideanSpace ℝ (Fin 2)))
    have h2 := levelOf_pos (P (Classical.arbitrary ι) (0 : EuclideanSpace ℝ (Fin 2)))
    linarith
  · intro k y
    have h := le_ciSup hbdd ((k), (y))
    linarith

/-- The level function is continuous (`levelOf` is the first coordinate of the capping homeomorphism). -/
theorem continuous_levelOf : Continuous levelOf := by
  unfold levelOf
  fun_prop

/-- The union of the level ranges of a compact family of planes is bounded above. -/
theorem bddAbove_range_levelOf_of_isCompact {ι : Type*}
    (P : ι → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (h : IsCompact (Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => P p.1 p.2))) :
    BddAbove (Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => levelOf (P p.1 p.2))) := by
  have hc : IsCompact
      (levelOf '' Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => P p.1 p.2)) :=
    h.image continuous_levelOf
  have hr : Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => levelOf (P p.1 p.2))
      = levelOf '' Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => P p.1 p.2) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨P p.1 p.2, ⟨p, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
  rw [hr]
  exact hc.bddAbove

/-- **A common level avoiding compact planes.**  For a nonempty family of planes with compact image
there is a single positive level `c` not attained by any of them (combine
`bddAbove_range_levelOf_of_isCompact` with `exists_common_level_ne_levelOf`). -/
theorem exists_common_level_ne_levelOf_of_isCompact {ι : Type*} [Nonempty ι]
    (P : ι → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (h : IsCompact (Set.range (fun p : ι × EuclideanSpace ℝ (Fin 2) => P p.1 p.2))) :
    ∃ c : ℝ, 0 < c ∧ ∀ k y, levelOf (P k y) ≠ c :=
  exists_common_level_ne_levelOf P (bddAbove_range_levelOf_of_isCompact P h)

/-- The concrete sweep profile `ψ t = 1 - t`: it takes the value `1` at the bottom face `t = 0` (so
that face is the shadow on the level `c`) and `0` at the top face `t = 1` (so that face is the plane
itself), and its derivative is non-zero, which is the other hypothesis of
`Work.Drive.ha_of_deriv_ne_of_level_ne`. -/
theorem one_sub_zero : (fun t : ℝ => 1 - t) 0 = 1 := by norm_num

theorem one_sub_one : (fun t : ℝ => 1 - t) 1 = 0 := by norm_num

theorem deriv_one_sub_ne_zero (t : ℝ) : deriv (fun s : ℝ => 1 - s) t ≠ 0 := by
  have h : deriv (fun s : ℝ => 1 - s) t = -1 := by
    simpa using (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub (hasDerivAt_id t)
  rw [h]; norm_num

end Work.Drive
