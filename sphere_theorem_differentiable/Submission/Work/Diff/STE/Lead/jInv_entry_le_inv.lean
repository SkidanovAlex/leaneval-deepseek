import Mathlib
import Submission.Work.Diff.STE.fill.matInv_entry_bound
import Submission.Work.Diff.STE.Lead.matInv_entry_bound_explicit
import Submission.Work.Diff.EXT.ricJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-! Coercivity bound on the entries of the inverse Gram matrix, with the *sharp* constant `cl⁻¹`
(needed by `pPhi_entry_bound_v2`, where the constant of the bound must not depend on `cl`).

`Work.Diff.EXT.jInv A r s = (Matrix.of A)⁻¹ r s` is the inverse Gram matrix of the jet data
`A : Work.Diff.EXT.MatE (E := E) = Fin (finrank ℝ E) → Fin n → ℝ`.  The sibling
`Work.Diff.STE.fill.matInv_entry_bound` (imported via `depends_on`) proves the same bound with an
*abstract* constant `C ≥ 0` (chosen as `1/lam` inside its proof); here the explicit value `cl⁻¹` is
needed.  Either copy that proof with `C := 1 / cl`, or deduce it from `matInv_entry_bound` at
coercivity `1` applied to the rescaled matrix `cl⁻¹ • Matrix.of A` (whose quadratic form is
`≥ ‖ξ‖²`), using `Matrix.inv_smul` — the invertibility `IsUnit (Matrix.of A).det` follows from the
injectivity of `Matrix.mulVec (Matrix.of A)`, itself implied by the quadratic-form lower bound
(exactly as in `matInv_entry_bound`).

The statement uses `Finset.univ.sum` instead of `∑` so that it elaborates in a bare file.
Degenerate `finrank = 0` (empty index type) is vacuous, so no `1 ≤ n` hypothesis is needed; split it
off if the proof of the general case needs it.
-/

theorem jInv_entry_le_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {cl : ℝ} (hcl : 0 < cl)
    {A : Work.Diff.EXT.MatE (E := E)}
    (hquad : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      cl * (Finset.univ.sum (fun k => (ξ k) ^ 2))
        ≤ Finset.univ.sum (fun k => Finset.univ.sum (fun l => A k l * ξ k * ξ l))) :
    ∀ r s : Fin (Module.finrank ℝ E), |Work.Diff.EXT.jInv A r s| ≤ cl⁻¹ := by
  -- `n = Module.finrank ℝ E`.  For `n = 0` the index type `Fin 0` is empty and the statement is
  -- vacuous; for `n ≥ 1` we apply the explicit entrywise inverse bound.
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn | hn
  · intro r
    exact absurd r.isLt (by simp [hn])
  · intro r s
    have h := matInv_entry_bound_explicit hn hcl (Matrix.of A) hquad r s
    simpa [Work.Diff.EXT.jInv, one_div] using h

end Work.Diff.STE.Lead
