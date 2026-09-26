import Mathlib
import Submission.Work.Topology.Classical.Defs

namespace Work.Topology.Classical

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.InnermostDisk

/-- An embedded sphere `S` is homeomorphic to the round unit sphere, and the homeomorphism can be
taken to be the defining embedding: every point of the round sphere is carried to a point of `S`. -/
theorem exists_homeomorph_roundSphere (S : Set LeanEval.KnotTheory.PardonDistortion.R3)
    (hS : Work.InnermostDisk.IsEmbeddedSphere S) :
    ∃ φ : Work.Topology.Classical.RoundSphere ≃ₜ S,
      (∀ x : Work.Topology.Classical.RoundSphere,
        (φ x : LeanEval.KnotTheory.PardonDistortion.R3) ∈ S) := by
  obtain ⟨e, hinj, hrange⟩ := hS
  -- `RoundSphere` is the round unit sphere, compact because `ℝ³` is proper.
  haveI : CompactSpace RoundSphere := by
    rw [RoundSphere_eq_sphere]
    exact isCompact_iff_compactSpace.mp (isCompact_sphere (0 : R3) 1)
  -- the defining embedding of `S`, landing in the subtype `S`.
  let g : RoundSphere → S := fun x => ⟨e x, by rw [← hrange]; exact ⟨x, rfl⟩⟩
  have hg_inj : Function.Injective g := fun x y hxy => hinj (Subtype.ext_iff.mp hxy)
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ : (y : R3) ∈ Set.range e := by rw [hrange]; exact y.2
    exact ⟨x, Subtype.ext hx⟩
  let f : RoundSphere ≃ S := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hf : Continuous f := Continuous.subtype_mk e.continuous _
  -- a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism.
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := f) hf, ?_⟩
  intro x
  exact (f x).2

end Work.Topology.Classical
