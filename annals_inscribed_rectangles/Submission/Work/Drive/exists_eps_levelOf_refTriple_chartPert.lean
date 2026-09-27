import Mathlib
import Submission.Work.Drive.refTripleLocalAssembly
import Submission.Work.Drive.chartPertTransfer

/-!
# The level bound of the perturbed reference triple

`Work.Drive.chartPert τ : CappingSpace → CappingSpace` acts on the transparent coordinates
`cappingSpaceHomeoProj` as `(level ↦ levelScale τ level, class ↦ classMap τ class)`, and the level of a
perturbed point is

  `levelOf (chartPert τ p) = exp (log (levelOf p) + τ 0)`

(`Work.Drive.levelOf_chartPert`, `Work.Drive.levelScale_apply`).  Since the level of `p` is bounded
below on the reference triple — `cQ` for the two rotated presentations of the chart (`le_levelOf_rotPresentation`)
and `cR` for the reference plane — and since the level coordinate `(blk k t) 0` of the `k`-th block of the
parameter is at most `‖blk k t‖ ≤ ‖t‖` in absolute value (`norm_blk_le`), a uniform `ε` makes the
perturbed level exceed `cblk 0` at every point of the reference triple.

This is the producer of the hypothesis `hlev` of
`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleLocal`, and hence of the corresponding clause of the
`hn2` engine: the design's level `cblk 0` is a *truncation level below* `cQ` and `cR`, and after the
perturbation by the blocks it must remain below every level of the perturbed reference triple.  Note
that the `t`-uniform statement is exactly what the engine consumes: the perturbation parameter must
serve *all three* blocks and *all* points `y` simultaneously.
-/

namespace Work.Drive

noncomputable section

/-- **The perturbed level coordinate.**  The level coordinate of the `k`-th block of a small parameter
`t` is smaller in absolute value than `‖t‖`. -/
lemma abs_coord_blk_le (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    |(blk k t).ofLp 0| ≤ ‖t‖ :=
  calc |(blk k t).ofLp 0| = ‖(blk k t).ofLp 0‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖blk k t‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖t‖ := norm_blk_le k t

/-- **The level of the reference triple is bounded below** by `min cQ cR`. -/
lemma min_le_levelOf_refTriple
    (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) {cQ cR : ℝ}
    (hQ : ∀ z : ℂ, ‖z‖ ≤ 1 → cQ ≤ levelOf (Q z))
    (hR : ∀ y : EuclideanSpace ℝ (Fin 2), cR ≤ levelOf (R y)) :
    ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      min cQ cR ≤ levelOf (refTriple Q R u v k y) := by
  intro k y
  fin_cases k
  · simpa [refTriple] using
      le_trans (min_le_left cQ cR) (le_levelOf_rotPresentation Q hQ u y)
  · simpa [refTriple] using
      le_trans (min_le_left cQ cR) (le_levelOf_rotPresentation Q hQ v y)
  · simpa [refTriple] using le_trans (min_le_right cQ cR) (hR y)

/-- **The level bound of the perturbed reference triple.**  There is a `t`-ball on which *every*
point of every member of the reference triple `![P_u, P_v, R]`, after the perturbation by the
corresponding block `blk k t`, has level strictly above `cblk 0`.

The bound `ε` is the logarithmic gap `log (min cQ cR) - log (cblk 0) > 0` between the level of the
truncation and the levels of the unperturbed triple: the level coordinate of a block contribution is
at most `‖t‖` and `exp` is strictly increasing. -/
theorem exists_eps_levelOf_refTriple_chartPert
    (Q : ℂ → Work.Drive.CappingSpace)
    (R : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcblk0 : 0 < cblk 0)
    {cQ cR : ℝ} (hcQ : 0 < cQ) (hcQc : cblk 0 < cQ) (hcRc : cblk 0 < cR)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ 1 → cQ ≤ Work.Drive.levelOf (Q z))
    (hR : ∀ y : EuclideanSpace ℝ (Fin 2), cR ≤ Work.Drive.levelOf (R y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        cblk 0 < Work.Drive.levelOf
          (Work.Drive.chartPert (Work.Drive.blk k t) (Work.Drive.refTriple Q R u v k y)) := by
  have hL := min_le_levelOf_refTriple Q R u v (cQ := cQ) (cR := cR) hQ hR
  have hcRpos : 0 < cR := lt_trans hcblk0 hcRc
  refine ⟨Real.log (min cQ cR) - Real.log (cblk 0), ?_, ?_⟩
  · exact sub_pos.mpr (Real.log_lt_log hcblk0 (lt_min hcQc hcRc))
  · intro t ht k y
    have hx : -(Real.log (min cQ cR) - Real.log (cblk 0)) < (blk k t).ofLp 0 := by
      have h1 : -((blk k t).ofLp 0) ≤ |(blk k t).ofLp 0| := neg_le_abs _
      linarith [abs_coord_blk_le k t]
    have hlog : Real.log (cblk 0)
        < Real.log (levelOf (refTriple Q R u v k y)) + (blk k t).ofLp 0 := by
      have h1 := Real.log_le_log (lt_min hcQ hcRpos) (hL k y)
      linarith
    rw [levelOf_chartPert, levelScale_apply]
    calc cblk 0 = Real.exp (Real.log (cblk 0)) := (Real.exp_log hcblk0).symm
      _ < _ := Real.exp_lt_exp.mpr hlog

end

end Work.Drive
