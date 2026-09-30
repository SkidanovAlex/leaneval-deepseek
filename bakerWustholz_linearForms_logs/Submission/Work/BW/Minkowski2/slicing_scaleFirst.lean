import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.slicingDefs
import Submission.Work.BW.Minkowski2.volume_addSet_scaleFirst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The slicing inequality `volume (M + S) ≤ volume (M + scaleFirst i ρ '' S)`

`Work.BW.Minkowski2.slicing_scaleFirst` is the "slicing" comparison used in Minkowski's second
theorem: if the points of the finite set `M ⊆ ℝᵈ` vanish on the coordinates `j` with `i ≤ j`, and
`S` is convex and measurable, then dilating the first `i` coordinates by `ρ ≥ 1` does not decrease
the volume of the Minkowski sum `M + S`.

The proof splits `ℝᵈ` as `(Xidx d i → ℝ) × (Yidx d i → ℝ)` along the reindexing equivalence
`Work.BW.Minkowski2.Phi d i` (`slicingDefs`).  Under `Phi`, the finite set `M` becomes a finite set
of points of the product with vanishing second coordinate, `S` becomes a convex measurable set of
the product, and `scaleFirst i ρ` becomes the dilation `scaleX ρ` of the first coordinate; since
`Phi` is a measure preserving additive equivalence, this reduces the claim to the product statement
`Work.BW.Minkowski2.volume_addSet_scaleX_le`.  The resulting inequality of `ℝ≥0∞`-measures is then
converted to the `Measure.real` inequality of the statement: either `volume S = ⊤`, in which case
`volume (M + S) = ⊤` and both real volumes are `0`, or `volume S ≠ ⊤`, in which case
`volume (M + scaleFirst i ρ '' S)` is finite (finitely many translates of `scaleFirst i ρ '' S`,
whose volume is `ofReal |det (scaleFirst i ρ)| * volume S` by
`Measure.addHaar_image_linearMap`) and `ENNReal.toReal_mono` applies.
-/

namespace Work.BW.Minkowski2

open MeasureTheory

theorem slicing_scaleFirst {d : ℕ} (i : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (M : Finset (Fin d → ℝ)) (hM : ∀ x ∈ M, ∀ j : Fin d, i ≤ (j : ℕ) → x j = 0)
    (S : Set (Fin d → ℝ)) (hSconv : Convex ℝ S) (hSmeas : MeasurableSet S) :
    MeasureTheory.volume.real (Work.BW.addSet (M : Set (Fin d → ℝ)) S)
      ≤ MeasureTheory.volume.real
        (Work.BW.addSet (M : Set (Fin d → ℝ)) (Work.BW.scaleFirst i ρ '' S)) := by
  classical
  have hρne : ρ ≠ 0 := by linarith
  have hTmeas : MeasurableSet (Work.BW.scaleFirst i ρ '' S) :=
    measurableSet_scaleFirst_image d i hρne hSmeas
  have hAmeas : MeasurableSet (Work.BW.addSet (M : Set (Fin d → ℝ)) S) :=
    measurableSet_addSet d M hSmeas
  have hBmeas : MeasurableSet (Work.BW.addSet (M : Set (Fin d → ℝ))
      (Work.BW.scaleFirst i ρ '' S)) := measurableSet_addSet d M hTmeas
  -- transfer to the product `(Xidx d i → ℝ) × (Yidx d i → ℝ)`
  have hXTmeas : MeasurableSet
      (scaleX (ι := Xidx d i) (κ := Yidx d i) ρ '' (Phi d i '' S)) := by
    rw [← Phi_image_scaleFirst d i ρ S]
    exact measurableSet_image_Phi d i hTmeas
  have hL : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S)
      = MeasureTheory.volume (Work.BW.addSet (M.image (Phi d i) : Set _) (Phi d i '' S)) := by
    rw [← volume_image_Phi hAmeas, Phi_image_addSet]
  have hR : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ))
        (Work.BW.scaleFirst i ρ '' S))
      = MeasureTheory.volume (Work.BW.addSet (M.image (Phi d i) : Set _)
          (scaleX (ι := Xidx d i) (κ := Yidx d i) ρ '' (Phi d i '' S))) := by
    rw [← volume_image_Phi hBmeas, Phi_image_addSet, Phi_image_scaleFirst]
  have hEnn : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S)
      ≤ MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ))
          (Work.BW.scaleFirst i ρ '' S)) := by
    rw [hL, hR]
    exact volume_addSet_scaleX_le hρ (M.image (Phi d i)) (Phi_snd_eq_zero d i M hM)
      (Phi d i '' S) (convex_image_Phi d i hSconv) (measurableSet_image_Phi d i hSmeas) hXTmeas
  -- convert the `ℝ≥0∞` inequality into the `Measure.real` inequality
  by_cases hStop : MeasureTheory.volume S = ⊤
  · rw [Measure.real_def]
    have hA0 : (MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S)).toReal = 0 := by
      rcases M.eq_empty_or_nonempty with hM0 | ⟨x0, hx0⟩
      · rw [hM0]; simp [Work.BW.addSet]
      · have htop : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S) = ⊤ := by
          refine top_le_iff.mp ?_
          rw [← hStop]
          calc MeasureTheory.volume S
              = MeasureTheory.volume ((fun s : Fin d → ℝ => x0 + s) '' S) := by
                rw [Set.image_add_left]; simp
            _ ≤ MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S) :=
                measure_mono (by
                  rintro z ⟨s, hs, rfl⟩
                  exact ⟨x0, hx0, s, hs, rfl⟩)
        rw [htop]; simp
    rw [hA0]
    exact ENNReal.toReal_nonneg
  · have hTS : MeasureTheory.volume (Work.BW.scaleFirst (d := d) i ρ '' S)
        = ENNReal.ofReal |LinearMap.det (Work.BW.scaleFirst (d := d) i ρ)|
            * MeasureTheory.volume S :=
      Measure.addHaar_image_linearMap (MeasureTheory.volume : Measure (Fin d → ℝ))
        (Work.BW.scaleFirst (d := d) i ρ) S
    have hBlt : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ))
        (Work.BW.scaleFirst i ρ '' S)) < ⊤ := by
      refine lt_of_le_of_lt (volume_addSet_le_card_mul M _) ?_
      rw [hTS]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hStop))
    rw [Measure.real_def, Measure.real_def]
    exact ENNReal.toReal_mono hBlt.ne hEnn

end Work.BW.Minkowski2
