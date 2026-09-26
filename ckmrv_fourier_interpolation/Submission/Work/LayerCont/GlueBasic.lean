/-
# Gluing two holomorphic charts

The core step of gluing the local charts of the layer continuation into a single holomorphic
function: two holomorphic functions on two *open* sets that agree on the intersection glue to a
holomorphic function on the union.  Iterating this over a finite chart cover gives the
`F₂` of the socket `Work.Asymptotics.exists_pair_of_propagated_F2`.

This file contains only the self-contained topological/algebraic step; the chart families and
the finite-cover bookkeeping live elsewhere.
-/
import Mathlib

noncomputable section

open UpperHalfPlane
open scoped Manifold Topology

namespace Work.LayerCont

/-- **Gluing two charts.**  If `f` is holomorphic on the open set `s`, `g` on the open set `t`,
and `f = g` on `s ∩ t`, then there is a holomorphic `F` on `s ∪ t` agreeing with `f` on `s` and
with `g` on `t`. -/
theorem exists_mdifferentiableOn_glue {s t : Set ℍ} (hs : IsOpen s) (ht : IsOpen t)
    {f g : ℍ → ℂ}
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f s) (hg : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g t)
    (h : Set.EqOn f g (s ∩ t)) :
    ∃ F : ℍ → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F (s ∪ t) ∧ Set.EqOn F f s ∧ Set.EqOn F g t := by
  classical
  refine ⟨fun x => if x ∈ s then f x else g x, ?_, ?_, ?_⟩
  · -- holomorphy on `s ∪ t`
    intro x hx
    rcases hx with hx | hx
    · -- near `x ∈ s` the glued function is `f`
      have hcongr : (fun y => if y ∈ s then f y else g y) =ᶠ[𝓝 x] f := by
        filter_upwards [hs.mem_nhds hx] with y hy
        simp only [hy, if_true]
      exact (hcongr.mdifferentiableAt_iff.mpr ((hf x hx).mdifferentiableAt (hs.mem_nhds hx))).mdifferentiableWithinAt
    · -- near `x ∈ t` the glued function is `g`
      have hcongr : (fun y => if y ∈ s then f y else g y) =ᶠ[𝓝 x] g := by
        filter_upwards [ht.mem_nhds hx] with y hy
        by_cases hys : y ∈ s
        · simp only [hys, if_true]
          exact h ⟨hys, hy⟩
        · simp only [hys, if_false]
      exact (hcongr.mdifferentiableAt_iff.mpr ((hg x hx).mdifferentiableAt (ht.mem_nhds hx))).mdifferentiableWithinAt
  · intro x hx
    simp only [hx, if_true]
  · intro x hx
    by_cases hxs : x ∈ s
    · simp only [hxs, if_true]
      exact h ⟨hxs, hx⟩
    · simp only [hxs, if_false]

end Work.LayerCont
