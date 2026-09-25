import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts
import Submission.Work.Geometry.WindowScale

/-!
# The window of radius `R - 1/2` fits into the shift-intersection window

For an element `v` of the mixed space `mixedSpace K` that has norm `1` at every infinite
place (the image of a "norm one" unit of a CM field), the window

`WindowShift K R v = Window K R ∩ {x | x + v ∈ Window K R}`

is at least as large (in Haar volume) as the window `Window K (R - 1/2)`.

The proof does **not** need the product structure of the mixed space or any volume formula.
Instead we translate by `v/2`: with `c = v/2` we have `v = c + c`, so for `x = y - c`,

* `x + c = y`, and
* `x + v = x + c + c = y + c`,

and the placewise triangle inequality turns `normAtPlace w y < R - 1/2` into
`normAtPlace w x < R` and `normAtPlace w (x + v) < R`.  Hence

`Window K (R - 1/2) ⊆ (· + c) '' WindowShift K R v`,

and translation invariance of the Haar measure `volume` on the mixed space finishes the job.
-/

set_option linter.unusedSectionVars false

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

namespace Work.Geometry

/-- Placewise triangle inequality for a difference: `|x - y|_w ≤ |x|_w + |y|_w`. -/
theorem normAtPlace_sub_le {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    (x y : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.normAtPlace w (x - y) ≤
      mixedEmbedding.normAtPlace w x + mixedEmbedding.normAtPlace w y := by
  rw [sub_eq_add_neg, ← mixedEmbedding.normAtPlace_neg w y]
  exact mixedEmbedding.normAtPlace_add_le w x (-y)

/-- `WindowShift K R v` is measurable (an intersection of two open windows). -/
theorem measurableSet_windowShift {K : Type*} [Field K] [NumberField K] (R : ℝ)
    (v : mixedEmbedding.mixedSpace K) : MeasurableSet (WindowShift K R v) := by
  unfold WindowShift
  exact (measurableSet_window R).inter
    ((isOpen_window R).preimage (continuous_id.add continuous_const)).measurableSet

/-- The Haar measure of the mixed space is invariant under translation, expressed for
images: `volume ((· + c) '' s) = volume s` for measurable `s`. -/
theorem volume_image_add_eq {K : Type*} [Field K] [NumberField K]
    (c : mixedEmbedding.mixedSpace K) (s : Set (mixedEmbedding.mixedSpace K))
    (hs : MeasurableSet s) :
    volume ((fun x : mixedEmbedding.mixedSpace K => x + c) '' s) = volume s := by
  have heq : (fun x : mixedEmbedding.mixedSpace K => x + c) '' s
      = (fun x : mixedEmbedding.mixedSpace K => (-c) +ᵥ x) ⁻¹' s := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [neg_add_cancel_comm_assoc]
    · rintro (hz : -c + z ∈ s)
      have hthis : z - c = -c + z := by rw [sub_eq_add_neg, add_comm]
      exact ⟨z - c, by rwa [← hthis] at hz, sub_add_cancel _ _⟩
  rw [heq]
  exact VAddInvariantMeasure.measure_preimage_vadd (-c) hs

/-- Translating `WindowShift K R v` by `v/2` makes it contain `Window K (R - 1/2)`. -/
theorem window_sub_half_subset_image_windowShift {K : Type*} [Field K] [NumberField K]
    {R : ℝ} {v : mixedEmbedding.mixedSpace K}
    (hv : ∀ w : InfinitePlace K, mixedEmbedding.normAtPlace w v = 1) :
    Window K (R - 1/2) ⊆ (fun x => x + (1/2 : ℝ) • v) '' WindowShift K R v := by
  set c : mixedEmbedding.mixedSpace K := (1/2 : ℝ) • v with hcdef
  have hv2 : ∀ w : InfinitePlace K, mixedEmbedding.normAtPlace w c = 1/2 := by
    intro w
    rw [hcdef, mixedEmbedding.normAtPlace_smul, hv w, mul_one]
    exact abs_of_nonneg (by norm_num)
  rintro y hy
  refine ⟨y - c, ⟨fun w => ?_, fun w => ?_⟩, sub_add_cancel _ _⟩
  · calc mixedEmbedding.normAtPlace w (y - c)
        ≤ mixedEmbedding.normAtPlace w y + mixedEmbedding.normAtPlace w c := by
          rw [sub_eq_add_neg, ← mixedEmbedding.normAtPlace_neg w c]
          exact mixedEmbedding.normAtPlace_add_le w y _
      _ = mixedEmbedding.normAtPlace w y + 1/2 := by rw [hv2 w]
      _ < (R - 1/2) + 1/2 := by linarith [hy w]
      _ = R := by ring
  · have hvc : v = c + c := by
      rw [hcdef, ← add_smul, show (1/2 : ℝ) + 1/2 = 1 by norm_num, one_smul]
    have h2 : y - c + v = y + c := by
      rw [sub_add_eq_add_sub, hvc]
      abel
    rw [h2]
    calc mixedEmbedding.normAtPlace w (y + c)
        ≤ mixedEmbedding.normAtPlace w y + mixedEmbedding.normAtPlace w c :=
          mixedEmbedding.normAtPlace_add_le w y _
      _ = mixedEmbedding.normAtPlace w y + 1/2 := by rw [hv2 w]
      _ < (R - 1/2) + 1/2 := by linarith [hy w]
      _ = R := by ring

/-- **Target lemma.** If `v` has norm `1` at every infinite place then the window of radius
`R - 1/2` has volume at most that of the shift-intersection window `WindowShift K R v`. -/
theorem volume_Window_sub_half_le_WindowShift (K : Type*) [Field K] [NumberField K]
    {R : ℝ} (hR : 1/2 < R) {v : mixedEmbedding.mixedSpace K}
    (hv : ∀ w : InfinitePlace K, mixedEmbedding.normAtPlace w v = 1) :
    volume (Window K (R - 1/2)) ≤ volume (WindowShift K R v) := by
  have h := volume_image_add_eq ((1/2 : ℝ) • v) (WindowShift K R v)
    (measurableSet_windowShift R v)
  rw [← h]
  exact measure_mono (window_sub_half_subset_image_windowShift hv)

end Work.Geometry
