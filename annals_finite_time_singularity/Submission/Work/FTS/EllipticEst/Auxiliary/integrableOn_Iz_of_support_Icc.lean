import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary

/-- **Extending integrability from `Icc 0 R` to `Iz = [0,∞)` for functions vanishing past `R`.**

If `f` is integrable on `[0,R]` and vanishes for `z ≥ R`, it is integrable on
`Iz = [0,∞)` (`R ≥ 0`).

Route.  `Iz = Set.Ici 0 = Set.Icc 0 R ∪ Set.Ici R` (using `hR`), so
`MeasureTheory.IntegrableOn.union` applies: on `Ici R` the function `f` is (pointwise) equal to
the zero function, use `MeasureTheory.IntegrableOn.congr_fun` with `IntegrableOn (fun _ => 0) _`
and `MeasurableSet.Ici`. -/
theorem integrableOn_Iz_of_support_Icc {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : MeasureTheory.IntegrableOn f (Set.Icc 0 R)) (h0 : ∀ z, R ≤ z → f z = 0) :
    MeasureTheory.IntegrableOn f Work.Spaces.Iz := by
  have hset : Set.Icc (0 : ℝ) R ∪ Set.Ici R = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · exact le_trans hR h2
    · intro hx
      rcases lt_or_ge x R with hxR | hxR
      · exact Or.inl ⟨hx, le_of_lt hxR⟩
      · exact Or.inr hxR
  rw [Work.Spaces.Iz, ← hset]
  refine MeasureTheory.IntegrableOn.union h ?_
  refine MeasureTheory.IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
    (s := Set.Ici R) ?_ ?_ measurableSet_Ici
  · exact (MeasureTheory.integrable_zero ℝ ℝ MeasureTheory.volume).integrableOn
  · intro x hx
    exact (h0 x hx).symm

end Work.FTS.EllipticEst.Auxiliary
