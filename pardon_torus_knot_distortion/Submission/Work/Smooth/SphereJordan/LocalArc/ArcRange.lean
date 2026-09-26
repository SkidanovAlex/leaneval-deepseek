import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch
import Submission.Work.Smooth.SphereJordan.LocalArc.Develop

/-!
# Arc ranges

An *arc range* in a topological space `X` is the image of `ℝ` under an injective continuous map
which sends `0` to a prescribed base point `x₀`.  In a space that is locally an arc such a range is
open (`IsArcRange.isOpen`), and it is the basic object of the classification proof: the maximal
arc range is a circle.

This file only contains the definition and its elementary properties; the extension lemma
(`exists_arc_range_strictly_larger`) and the nested-union lemma
(`isArcRange_iUnion_of_nested`) live in separate files so that they can be worked on independently.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- An **arc range**: the range of a continuous injective map `ℝ → X` sending `0` to `x₀`. -/
def IsArcRange (x₀ : X) (U : Set X) : Prop :=
  ∃ γ : ℝ → X, Continuous γ ∧ Function.Injective γ ∧ γ 0 = x₀ ∧ Set.range γ = U

theorem IsArcRange.mem {x₀ : X} {U : Set X} (h : IsArcRange x₀ U) : x₀ ∈ U := by
  obtain ⟨γ, -, -, h0, rfl⟩ := h
  exact ⟨0, h0⟩

theorem IsArcRange.isOpen [T2Space X] {x₀ : X} {U : Set X} (h : IsArcRange x₀ U)
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) : IsOpen U := by
  obtain ⟨γ, hc, hi, -, rfl⟩ := h
  exact isOpen_range_of_injective_continuous H hc hi

theorem IsArcRange.isConnected [T2Space X] {x₀ : X} {U : Set X} (h : IsArcRange x₀ U) :
    IsConnected U := by
  obtain ⟨γ, hc, -, -, rfl⟩ := h
  exact isConnected_range hc

/-- The arc range of any embedding is an arc range with the appropriate base point. -/
theorem isArcRange_range {γ : ℝ → X} (hc : Continuous γ) (hi : Function.Injective γ) (t₀ : ℝ) :
    IsArcRange (γ t₀) (Set.range γ) :=
  ⟨fun t => γ (t + t₀), hc.comp (continuous_id.add continuous_const),
    fun a b hab => by simpa [add_comm, add_left_comm, add_assoc] using hi hab,
    by simp, by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t + t₀, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s - t₀, by ring_nf⟩⟩

end

end Work.Smooth.SphereJordan.LocalArc
