import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.junctionGoodAux
import Submission.Work.Drive.Mono.fibreMax_continuous

namespace Work.Drive.Mono

/-- Every value of a `2π`-periodic curve is attained somewhere in the fundamental interval
`[0, 2π)`. -/
lemma exists_curve_eq_mem_Ico_two_pi (K : LeanEval.KnotTheory.PardonDistortion.Knot) (t : ℝ) :
    ∃ q ∈ Set.Ico 0 (2 * Real.pi), K.curve q = K.curve t := by
  have hc : (0:ℝ) < 2 * Real.pi := by positivity
  have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  refine ⟨Int.fract (t / (2 * Real.pi)) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact mul_nonneg (Int.fract_nonneg _) hc.le
  · have h1 : Int.fract (t / (2 * Real.pi)) < 1 := Int.fract_lt_one _
    have h2 := mul_lt_mul_of_pos_right h1 hc
    simpa using h2
  · have h2 : Int.fract (t / (2 * Real.pi)) * (2 * Real.pi)
        + (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = t := by
      rw [← add_mul, Int.fract_add_floor, div_mul_cancel₀ t (ne_of_gt hc)]
    have hstep : K.curve (Int.fract (t / (2 * Real.pi)) * (2 * Real.pi)
        + (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        = K.curve (Int.fract (t / (2 * Real.pi)) * (2 * Real.pi)) :=
      hper.int_mul ⌊t / (2 * Real.pi)⌋ _
    have : K.curve t = K.curve (Int.fract (t / (2 * Real.pi)) * (2 * Real.pi)) := by
      conv_lhs => rw [← h2]
      exact hstep
    exact this.symm

/-- **No corner event lies on the knot, off a null set of half-widths.**  A corner event requires
the point of the surface to be on the box sphere and on a slab face; for a point of the knot on the
box sphere the half-width is pinned to `|slabFn|`, and the box sphere trace of the knot is finite
(`hS`).  Hence the set of `(h, τ)` at which a corner event lies on the knot is contained in
`F × ℝ`, with `F` the (finite) set of `|slabFn|`-values of the knot on the box sphere, and is null. -/
theorem g3_corner_event_bad_null (ψ : Submission.Diffeo)
    (K : LeanEval.KnotTheory.PardonDistortion.Knot) (s u : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (hS : ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}).Finite) :
    MeasureTheory.volume {x : ℝ × ℝ | ∃ t : ℝ,
        K.curve t ∈ closure (Submission.PBox s c σ) ∧
        Submission.boxNorm c σ (K.curve t) = s ∧
        |Work.Drive.Final.slabFn c u v (K.curve t)| = x.1} = 0 := by
  classical
  let f : ℝ → ℝ := fun t => |Work.Drive.Final.slabFn c u v (K.curve t)|
  let A : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}
  let F : Set ℝ := f '' A
  have hAfin : A.Finite := hS
  have hFfin : F.Finite := hAfin.image f
  have hsub : {x : ℝ × ℝ | ∃ t : ℝ,
        K.curve t ∈ closure (Submission.PBox s c σ) ∧
        Submission.boxNorm c σ (K.curve t) = s ∧
        |Work.Drive.Final.slabFn c u v (K.curve t)| = x.1} ⊆ {x : ℝ × ℝ | x.1 ∈ F} := by
    rintro x ⟨t, _hcl, hbn, hslab⟩
    obtain ⟨q, hq, hqeq⟩ := exists_curve_eq_mem_Ico_two_pi K t
    have hqA : q ∈ A := ⟨hq, by rw [hqeq]; exact hbn⟩
    refine ⟨q, hqA, ?_⟩
    show f q = x.1
    simp only [f]
    rw [hqeq]
    exact hslab
  refine MeasureTheory.measure_mono_null hsub ?_
  have hset : {x : ℝ × ℝ | x.1 ∈ F} = F ×ˢ (Set.univ : Set ℝ) := by
    ext x; simp
  rw [hset, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    hFfin.measure_zero MeasureTheory.volume, zero_mul]

end Work.Drive.Mono
