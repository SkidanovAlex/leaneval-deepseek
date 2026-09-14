import Mathlib

namespace Commons.Topology.Support

open MeasureTheory

/-- A finite linear combination of compactly supported functions has compact support. -/
theorem hasCompactSupport_finset_sum {α : Type*} [TopologicalSpace α] {ι : Type*}
    (t : Finset ι) (c : ι → ℝ) (u : ι → α → ℝ) (hu : ∀ i ∈ t, HasCompactSupport (u i)) :
    HasCompactSupport (fun x => ∑ i ∈ t, c i * u i x) := by
  -- Each summand `c i * u i` has compact support (multiplying by an arbitrary function
  -- preserves compact support), and a finite sum of compactly supported functions does too.
  have h : HasCompactSupport (∑ i ∈ t, fun x => c i * u i x) :=
    HasCompactSupport.finset_sum (fun i hi => (hu i hi).mul_left (f := fun _ : α => c i))
  convert h using 1
  ext x
  simp [Finset.sum_apply]

end Commons.Topology.Support
