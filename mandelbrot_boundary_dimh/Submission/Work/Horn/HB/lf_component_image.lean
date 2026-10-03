import Mathlib
import Submission.Work.Horn.isCoveringMapOn_restrictToPreimage
import Submission.Work.BasinSC.StepOneCrit.isConnected_diff_finite
import Submission.Work.Horn.HB.image_eq_of_proper_holomorphic

/-!
# The local component over a ball maps onto the ball, and meets the fibre over its centre

Let `g : ℂ → ℂ` be holomorphic on the open set `D` and let `ball v ρ` be a ball which does not
contain the origin.  Assume the "finite local monodromy" condition

`hLF : ∀ x ∈ D, g x ∈ ball v ρ → ∀ K ⊆ ball v ρ, IsCompact K →
        IsCompact (connectedComponentIn (D ∩ g ⁻¹' ball v ρ) x ∩ g ⁻¹' K)`

which says that every connected component of `D ∩ g ⁻¹' ball v ρ` is proper over the ball.
Then for every point `z` of such a component, that component maps **onto** the ball, and
consequently it contains a point of the fibre `g ⁻¹' {v}` (because `v` lies in its own ball).

The first half is the already proven `Work.Horn.HB.image_eq_of_proper_holomorphic`: the component
`C` is an open non-empty subset of the domain of holomorphy, it maps into the (connected, open)
ball, and by `hLF` the preimage of any compact subset of the ball is compact inside `C`; hence
`g '' C` is a non-empty clopen subset of the ball and therefore equals it.  (Note that the
covering hypothesis `hcov` is not needed for this statement; the local finiteness `hLF` alone
does the work.)
-/

namespace Work.Horn.HB

open Set Metric Filter Topology

open scoped Topology

theorem lf_component_image {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {ρ : ℝ}
    (hDo : IsOpen D) (hg : DifferentiableOn ℂ g D) (hρ : 0 < ρ) (hρv : ρ < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ (Metric.ball v ρ) → ∀ K ⊆ Metric.ball v ρ, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x ∩ g ⁻¹' K))
    {z : ℂ} (hzD : z ∈ D) (hzρ : g z ∈ Metric.ball v ρ) :
    Metric.ball v ρ ⊆ g '' connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z ∧
      (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z ∩ g ⁻¹' {v}).Nonempty := by
  set C : Set ℂ := connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) z with hC
  have hzC : z ∈ C := by
    rw [hC]
    exact mem_connectedComponentIn ⟨hzD, hzρ⟩
  -- the component is open (it is a component of an open subset of `ℂ`)
  have hWopen : IsOpen (D ∩ g ⁻¹' Metric.ball v ρ) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hwD, hwB⟩
    exact Filter.inter_mem (hDo.mem_nhds hwD)
      (((hg.differentiableAt (hDo.mem_nhds hwD)).continuousAt).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds hwB))
  have hCopen : IsOpen C := by
    rw [hC]
    exact hWopen.connectedComponentIn
  have hCW : C ⊆ D ∩ g ⁻¹' Metric.ball v ρ := by
    rw [hC]
    exact connectedComponentIn_subset _ z
  have hCD : C ⊆ D := fun w hw => (hCW hw).1
  have hCne : C.Nonempty := ⟨z, hzC⟩
  have hmaps : g '' C ⊆ Metric.ball v ρ := by
    rintro w ⟨y, hy, rfl⟩
    exact (hCW hy).2
  -- the component is proper over the ball: this is exactly `hLF` at the base point `z`
  have hprop : ∀ L : Set ℂ, L ⊆ Metric.ball v ρ → IsCompact L →
      IsCompact (C ∩ g ⁻¹' L) := by
    intro L hL hLc
    rw [hC]
    exact hLF z hzD hzρ L hL hLc
  have hEq : g '' C = Metric.ball v ρ :=
    image_eq_of_proper_holomorphic hDo hg Metric.isOpen_ball (isConnected_ball hρ)
      hCopen hCD hCne hmaps hprop
  refine ⟨?_, ?_⟩
  · rw [hEq]
  · -- `v` belongs to its own ball, and the image of `C` is the whole ball
    have hv : v ∈ g '' C := by rw [hEq]; exact Metric.mem_ball_self hρ
    obtain ⟨x, hxC, hxg⟩ := hv
    exact ⟨x, hxC, hxg⟩

end Work.Horn.HB
