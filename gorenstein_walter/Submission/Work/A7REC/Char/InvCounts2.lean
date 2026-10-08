/-
Area `A7REC`: the pass-13 assembly for the involution counts.

`A7InvolutionCounts2Prop` (the restatement on `A7RecCtx` of the counts `i(π) = 4`, `i(z) = 8`,
`i(zσ) = 6`) follows from the two counting leaves `c13_C3` (nine involutions in `C_G(z)`, six of
them inverting `σ`) and `c13_C4` (pair counts as inverter counts) — the assembly of design pass 13
§3, with `c13_C4`'s second and third conjuncts fed by `c13_C3`.
-/
import Submission.Work.A7REC.Char.c13_C3
import Submission.Work.A7REC.Char.c13_C4

namespace Work.A7REC

open Subgroup

/-- **The pass-13 assembly**: `A7InvolutionCounts2Prop` from `c13_C3` and `c13_C4`. -/
theorem c13_counts : A7InvolutionCounts2Prop := by
  intro G _ _ ctx π σ hσ hσ1 hπS hπ4 hCπ
  obtain ⟨h1, h2, h3⟩ := Char.c13_C4 G ctx π σ hσ hσ1 hπS hπ4 hCπ
  obtain ⟨h9, h6⟩ := Char.c13_C3 G ctx π σ hσ hσ1 hπS hπ4 hCπ
  exact ⟨h1, by rw [h2, h9], by rw [h3, h6]⟩

end Work.A7REC
