import Mathlib
import Submission.Work.WilG1.Cell.Junk.fibBad_thin_defs

namespace Work.WilG1.Cell.Junk

/-- `Fin.init` of the tuple `z ∘ insPermLift m i` (which reindexes the parameter coordinates by
`insPerm`) is `(Fin.init z) ∘ insPerm m i`: the lifted permutation fixes the value coordinate, so
dropping it commutes with the reindexing. -/
lemma init_comp_insPermLift (m : ℕ) (i : Fin (m + 1)) (z : Fin (m + 2) → ℝ) :
    Fin.init (z ∘ insPermLift m i) =
      (Fin.init z) ∘ (insPerm m i : Fin (m + 1) → Fin (m + 1)) := by
  funext j
  simp [Fin.init]

theorem graphOf_comp_insPerm (m : ℕ) (i : Fin (m + 1)) (h : (Fin (m + 1) → ℝ) → ℝ) :
    WilkiesDesign.graphOf
        (fun x : Fin (m + 1) → ℝ =>
          h (x ∘ (Work.WilG1.Cell.Junk.insPerm m i : Fin (m + 1) → Fin (m + 1))))
      = {z : Fin (m + 2) → ℝ |
          (z ∘ Work.WilG1.Cell.Junk.insPermLift m i) ∈ WilkiesDesign.graphOf h} := by
  ext z
  simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
  rw [init_comp_insPermLift]
  simp only [Function.comp_apply, insPermLift_last]

end Work.WilG1.Cell.Junk
