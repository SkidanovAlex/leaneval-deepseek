import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PCFU.aemeasurable_fibre_lintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PCFU

/-- **A.e. measurability of the cube-restricted squared fibre `lintegral`.**

This is the centred-cube version of the PROVED result `Work.PCFU.aemeasurable_fibre_lintegral`
(`Submission/Work/PCFU/aemeasurable_fibre_lintegral.lean`), which controls the fibre integral over
*all* of `ℝ³`:

    AEMeasurable (fun x => ∫⁻ u : ℝ³, ENNReal.ofReal ((V (Function.update x j u))^2)) volume .

Here the inner integration is restricted to the centred cube `acube ℓ`, which is what the geometric
peels (`Work.PCFU.abox_cube_peel`) produce and what the Hölder step in
`Work.PCFU.chDslot_le_of_kernel` consumes.

Suggested route: reduce to the unrestricted statement by replacing `V` with
`V' := fun y : X n => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) (y j) * V y`
(which is `AEMeasurable` because `fun y => y j` is measurable, `acube ℓ` is measurable via
`Submission.BoseGases.acube_measurable ℓ`, and `V` is a.e.-measurable).  For this `V'` one has
`V' (Function.update x j u) = (acube ℓ).indicator (fun _ => (1:ℝ)) u * V (Function.update x j u)`,
so `ENNReal.ofReal ((V' (Function.update x j u))^2)` is exactly the `acube ℓ`-indicator of
`ENNReal.ofReal ((V (Function.update x j u))^2)`; then `MeasureTheory.lintegral_indicator` turns
`∫⁻ u in acube ℓ, g u` into `∫⁻ u, (acube ℓ).indicator g u`, and the unrestricted result applied to
`V'` together with a final `AEMeasurable.congr` (`Filter.Eventually.of_forall`) gives the claim.

`n = 0` is vacuous (`j : Fin 0`), so `Fin.elim0` handles it; note the result is stated for
`n : ℕ` and `j : Fin n` via `cases n`.  `Submission.BoseGases.acube_measurable ℓ` holds for every
real `ℓ` (no `0 < ℓ` needed), and the statement is a genuine strengthening of the source result at
`ℓ`, so it is stated without an `hℓ`. -/
theorem aemeasurable_fibre_lintegral_cube {n : ℕ} (j : Fin n) {ℓ : ℝ}
    {V : Submission.BoseGases.X n → ℝ}
    (hV : AEMeasurable V (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :
    AEMeasurable (fun x : Submission.BoseGases.X n =>
        ∫⁻ u in Submission.BoseGases.acube ℓ,
          ENNReal.ofReal ((V (Function.update x j u)) ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
  classical
  cases n with
  | zero => exact j.elim0
  | succ k =>
    -- The cube indicator, as a function of the peeled coordinate.
    let χ : EuclideanSpace ℝ (Fin 3) → ℝ :=
      (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ))
    have hχ : Measurable χ :=
      measurable_const.indicator (Submission.BoseGases.acube_measurable ℓ)
    -- The windowed potential `V' = χ(y j) · V y`.
    have hV' : AEMeasurable (fun y : Submission.BoseGases.X (k + 1) => χ (y j) * V y)
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (k + 1))) :=
      (hχ.comp (measurable_pi_apply j)).aemeasurable.mul hV
    have hres := Work.PCFU.aemeasurable_fibre_lintegral
      (V := fun y : Submission.BoseGases.X (k + 1) => χ (y j) * V y) j hV'
    -- `ENNReal.ofReal ((V' ∘ update x j) u ^ 2)` is the cube indicator of
    -- `ENNReal.ofReal ((V ∘ update x j) u ^ 2)`, pointwise.
    have hpt : ∀ x : Submission.BoseGases.X (k + 1),
        (fun u : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal
          ((χ ((Function.update x j u) j) * V (Function.update x j u)) ^ 2))
        = fun u : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.acube ℓ).indicator
            (fun v => ENNReal.ofReal ((V (Function.update x j v)) ^ 2)) u := by
      intro x
      funext u
      dsimp only [χ]
      rw [Function.update_self]
      by_cases hu : u ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, one_mul]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
        simp
    have hfun : (fun x : Submission.BoseGases.X (k + 1) => ∫⁻ u : EuclideanSpace ℝ (Fin 3),
          ENNReal.ofReal ((χ ((Function.update x j u) j) * V (Function.update x j u)) ^ 2))
        = fun x : Submission.BoseGases.X (k + 1) => ∫⁻ u in Submission.BoseGases.acube ℓ,
          ENNReal.ofReal ((V (Function.update x j u)) ^ 2) := by
      funext x
      rw [hpt x, MeasureTheory.lintegral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    exact hres.congr (Filter.Eventually.of_forall fun x => congrFun hfun x)

end Work.PCFU
