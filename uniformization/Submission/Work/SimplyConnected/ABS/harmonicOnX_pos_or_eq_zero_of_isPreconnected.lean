import Mathlib
import Submission.Work.SimplyConnected.Defs
import Submission.MaxPrincipleRegion

namespace Work.SimplyConnected.ABS

/-- The strong minimum principle for nonnegative harmonic functions on a preconnected open set: a
harmonic `u ≥ 0` on an open preconnected `U` is either strictly positive on `U` or identically zero
on `U`.

Proof: the zero set `S = {x ∈ U | u x = 0}` is open in `X` (local strong maximum principle applied
to the subharmonic function `-u`, i.e. `Submission.SubharmonicOnXAt.eqOn_of_le` from
`Submission.MaxPrincipleRegion`, or equivalently `Submission.SuperharmonicOnXAt.eqOn_of_ge` from
`Submission.SuperharmonicX`) and closed in `U` (continuity of `u`,
`Submission.HarmonicOnXAt.continuousAt`); by preconnectedness of `U` it is empty or all of `U`.
The same clopen-set pattern is already used, for the sweep of the Green barrier, in the proof of
`Submission.sweep_pos` in `Submission/GreenConditional.lean`. -/
theorem harmonicOnX_pos_or_eq_zero_of_isPreconnected {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U) {u : X → ℝ}
    (hu : Submission.HarmonicOnX u U) (hnn : ∀ x ∈ U, 0 ≤ u x) :
    (∀ x ∈ U, 0 < u x) ∨ (∀ x ∈ U, u x = 0) := by
  -- Work in the subspace `U`, which is preconnected by hypothesis.
  haveI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUpc
  -- The zero set of `u` inside `U`.
  let S : Set U := {y : U | u (y : X) = 0}
  have hcont : Continuous fun y : U => u (y : X) :=
    continuous_iff_continuousAt.mpr fun y =>
      ((hu y y.2).continuousAt).comp continuous_subtype_val.continuousAt
  -- `S` is closed, since `u` is continuous at every point of `U`.
  have hSclosed : IsClosed S := by
    change IsClosed {y : U | u (y : X) = 0}
    exact isClosed_eq hcont continuous_const
  -- `S` is open, by the local strong minimum principle for the harmonic function `u`.
  have hSopen : IsOpen S := by
    change IsOpen {y : U | u (y : X) = 0}
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hsub : Submission.SubharmonicOnXAt (fun y : X => -u y) (x : X) :=
      ((hu x x.2).neg).subharmonic
    have hle : ∀ y ∈ U, -u y ≤ -u (x : X) := fun y hy => by
      have h1 : (0 : ℝ) ≤ u y := hnn y hy
      have h2 : u (x : X) = 0 := hx
      linarith
    obtain ⟨V, hVn, hVeq⟩ :=
      Submission.SubharmonicOnXAt.eqOn_of_le hsub (hUo.mem_nhds x.2) hle
    refine Filter.mem_of_superset
      (continuous_subtype_val.continuousAt.preimage_mem_nhds hVn) ?_
    intro y hy
    show u (y : X) = 0
    have h2 : u (y : X) = u (x : X) := neg_inj.mp (hVeq y hy)
    rw [h2, show u (x : X) = 0 from hx]
  rcases isClopen_iff.mp (show IsClopen S from ⟨hSclosed, hSopen⟩) with h | h
  · left
    intro x hx
    have hxS : (⟨x, hx⟩ : U) ∉ S := by
      rw [h]
      exact Set.notMem_empty _
    have hne : u x ≠ 0 := fun h0 => hxS (show (⟨x, hx⟩ : U) ∈ S from h0)
    exact lt_of_le_of_ne (hnn x hx) (Ne.symm hne)
  · right
    intro x hx
    have hxS : (⟨x, hx⟩ : U) ∈ S := by
      rw [h]
      exact Set.mem_univ _
    exact hxS

end Work.SimplyConnected.ABS
