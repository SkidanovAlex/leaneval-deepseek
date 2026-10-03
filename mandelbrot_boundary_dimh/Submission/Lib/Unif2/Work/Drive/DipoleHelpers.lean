import Mathlib
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs

/-!
# Elementary helpers for the dipole lemmas

Small facts shared by `Submission/Work/Drive/exists_dipoleAbove_of_not_hasWeakGreen.lean` and
`Submission/Work/Drive/exists_matched_evans_of_not_hasWeakGreen.lean`: invariance of the unit
logarithmic pole under additive constants, local boundedness of a harmonic function, and a
membership test for `univ \ {z}`.
-/

open Filter Set
open scoped _root_.Topology Manifold

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Adding a constant to a function with a unit logarithmic pole at `x₀` preserves the pole. -/
theorem hasLogPoleOn_add_const' {Ω : Set X} {x₀ : X} {E : X → ℝ} (c : ℝ)
    (h : Work.SimplyConnected.ABS.HasLogPoleOn Ω x₀ E) :
    Work.SimplyConnected.ABS.HasLogPoleOn Ω x₀ (fun x => E x + c) := by
  obtain ⟨C, V, hV, hCV⟩ := h
  refine ⟨C + |c|, V, hV, fun x hx hxΩ hxne => ?_⟩
  have h1 := hCV x hx hxΩ hxne
  have h2 : (E x + c) + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖
      = (E x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖) + c := by ring
  rw [h2]
  calc |(E x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖) + c|
      ≤ |E x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖| + |c| := abs_add_le _ _
    _ ≤ C + |c| := by linarith

/-- Subtracting a constant from a function with a unit logarithmic pole at `x₀` preserves it. -/
theorem hasLogPoleOn_sub_const' {Ω : Set X} {x₀ : X} {E : X → ℝ} (c : ℝ)
    (h : Work.SimplyConnected.ABS.HasLogPoleOn Ω x₀ E) :
    Work.SimplyConnected.ABS.HasLogPoleOn Ω x₀ (fun x => E x - c) := by
  have h' : (fun x : X => E x - c) = (fun x : X => E x + (-c)) := by funext x; ring
  rw [h']
  exact hasLogPoleOn_add_const' (-c) h

/-- A function harmonic at `x` is locally bounded near `x`. -/
theorem eventually_abs_le_of_harmonicOnX' {f : X → ℝ} {x : X}
    (h : Submission.HarmonicOnXAt f x) : ∀ᶠ y in 𝓝 x, |f y| ≤ |f x| + 1 := by
  have h1 : ∀ᶠ y in 𝓝 x, f y < |f x| + 1 :=
    h.continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds
      (lt_of_le_of_lt (le_abs_self (f x)) (lt_add_one (|f x|))))
  have h2 : ∀ᶠ y in 𝓝 x, -(|f x| + 1) < f y :=
    h.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds (lt_of_lt_of_le
      (neg_lt_neg_iff.mpr (lt_add_one (|f x|))) (neg_abs_le (f x))))
  filter_upwards [h1, h2] with y hy1 hy2
  exact abs_le.mpr ⟨le_of_lt hy2, le_of_lt hy1⟩

/-- `y` lies in `univ \ {z}` as soon as `y ≠ z`. -/
theorem mem_univ_sdiff_singleton {y z : X} (h : y ≠ z) : y ∈ (Set.univ \ {z} : Set X) :=
  ⟨mem_univ y, by simpa [Set.mem_singleton_iff] using h⟩

end Work.Drive
