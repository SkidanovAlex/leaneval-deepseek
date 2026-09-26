import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.nested_discs_of_schoenfliesData

/-!
# The nesting picture of a `SchoenfliesData`

`Work.Topology.Classical.SchoenfliesData` carries a family of Jordan curves on a set `A ⊆ ℝ³`, two
embedded discs per curve covering `A` and meeting along the curve, and a *rank* attached to the
curves.  This file draws the two consequences of the rank clause which make the datum the classical
picture of nested Jordan curves:

* `exists_innermost_of_schoenfliesData` — **an innermost curve exists**: a curve of minimal rank
  bounds a disc whose *open* part meets no other curve at all.  This is exactly the "take a curve
  innermost in `S`" step of Pardon's first innermost argument;
* `nestRel_trans_of_schoenfliesData` — **the nesting relation is transitive**: if the curve `j`
  meets the open disc of `i` and the curve `k` meets the open disc of `j`, then `k` meets the open
  disc of `i`.  (This is the classical transitivity of the nesting of disjoint Jordan curves on a
  sphere; it is what makes the rank of `SchoenfliesData` exist in the classical treatment.)
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **An innermost curve of a `SchoenfliesData`**: a curve whose open disc meets no curve of the
family.  (For its own curve this is automatic, the curve being the boundary of the disc and the
disc being embedded.) -/
theorem exists_innermost_of_schoenfliesData {A : Set R3} {ι : Type} [Fintype ι] [Nonempty ι]
    {c : ι → ℝ → R3} (D : SchoenfliesData A ι c) :
    ∃ i : ι, ∀ j : ι, ¬ (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z ∈ Set.range (c j)) := by
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image Finset.univ D.rank
    (Finset.univ_nonempty (α := ι))
  refine ⟨i, fun j hj => ?_⟩
  exact absurd (hmin j (Finset.mem_univ j)) (not_le.mpr (D.nested i j hj))

/-- **The nesting relation of a `SchoenfliesData` is transitive.** -/
theorem nestRel_trans_of_schoenfliesData {A : Set R3} {ι : Type} [Fintype ι]
    {c : ι → ℝ → R3} (D : SchoenfliesData A ι c)
    {i j k : ι} (hij : i ≠ j)
    (h1 : ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z ∈ Set.range (c j))
    (h2 : ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e j z ∈ Set.range (c k)) :
    ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z ∈ Set.range (c k) := by
  obtain ⟨z₂, hz₂, hz₂mem⟩ := h2
  have hsub := nested_discs_of_schoenfliesData D hij h1
  have hmem : (⟨D.e j z₂, D.mem j z₂⟩ : A) ∈
      {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e j z = (x : R3)} :=
    ⟨z₂, hz₂, rfl⟩
  obtain ⟨z, hz, hzeq⟩ := hsub hmem
  exact ⟨z, hz, hzeq ▸ hz₂mem⟩

end

end Work.Topology.Classical
