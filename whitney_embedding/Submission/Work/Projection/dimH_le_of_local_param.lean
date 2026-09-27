import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

open scoped Manifold ContDiff
open Topology MeasureTheory Set

namespace Work.Projection

/-- If every point of a finite-dimensional real normed space has an open neighbourhood `U` such
that `S ∩ U` is contained in the image of a `C¹` map on an open subset of a subspace of dimension
at most `d`, then `dimH S ≤ d`. -/
lemma dimH_le_of_local_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [LindelofSpace E] {S : Set E} {d : ENNReal}
    (h : ∀ x : E, ∃ (H : Submodule ℝ E) (g : H → E) (V : Set H) (U : Set E),
        (Module.finrank ℝ H : ENNReal) ≤ d ∧ IsOpen V ∧ ContDiffOn ℝ 1 g V ∧ IsOpen U ∧
        x ∈ U ∧ S ∩ U ⊆ g '' V) :
    dimH S ≤ d := by
  classical
  -- Choose the local parametrisation data at every point of `E`.
  choose H g V U hspec using h
  -- The open sets `U x` cover `E`; extract a countable subcover by Lindelöf.
  obtain ⟨f, hf⟩ := IsLindelof.indexed_countable_subcover (s := Set.univ) isLindelof_univ U
      (fun x => (hspec x).2.2.2.1)
      (fun x _ => mem_iUnion.2 ⟨x, (hspec x).2.2.2.2.1⟩)
  -- Hence `S` is a countable union of the pieces `S ∩ U (f n)`.
  have hcover : S ⊆ ⋃ n, S ∩ U (f n) := by
    intro y hy
    rcases mem_iUnion.1 (hf (mem_univ y)) with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, ⟨hy, hn⟩⟩
  calc dimH S ≤ dimH (⋃ n, S ∩ U (f n)) := dimH_mono hcover
    _ = ⨆ n, dimH (S ∩ U (f n)) := dimH_iUnion _
    _ ≤ d := iSup_le fun n =>
      calc dimH (S ∩ U (f n)) ≤ dimH (g (f n) '' V (f n)) :=
            dimH_mono (hspec (f n)).2.2.2.2.2
        _ ≤ (Module.finrank ℝ (H (f n)) : ENNReal) :=
            dimH_image_le_of_contDiffOn (hspec (f n)).2.1 (hspec (f n)).2.2.1 subset_rfl
        _ ≤ d := (hspec (f n)).1

end Work.Projection
