import Mathlib
import Submission.Work.PTCert.Chain

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions in `Submission/Work/PTCert/Chain.lean` (also Math.lean, Interfaces.lean).
Prove `RowFormula`.  For x ∈ rows: `avgMat Sg act U x z = Σ_{g∈Sg} U (act g x) (act g z)`; terms with
`act g x ∉ rows` vanish (support hypothesis); for the others `act g x = x` (distinct-orbit hypothesis), so the sum is
`Σ_{g ∈ Sg.filter (act g x = x)} U x (act g z)`, and each term equals `U x z` by stabiliser invariance
(`Finset.sum_filter`, `Finset.sum_congr`, `Finset.sum_const`, `nsmul_eq_mul`). ~40 lines.
-/

namespace Work.PTCert

open Submission.PTCert

theorem rowFormula : RowFormula := by
  intro G _ _ Sg hSg ι _ f act hconj rows U hsupp hstab hinv x hx z
  simp only [avgMat, Matrix.of_apply]
  -- Each term either vanishes (`act g x ∉ rows`) or is `U x z` (`act g x = x`, stabiliser invariance).
  have hstep : ∀ g ∈ Sg, U (act g x) (act g z) = if act g x = x then U x z else 0 := by
    intro g hg
    by_cases h : act g x = x
    · rw [h, if_pos rfl, hinv x hx g hg h z]
    · rw [if_neg h]
      exact hsupp _ _ (fun hmem => h (hstab x hx g hg hmem))
  calc ∑ g ∈ Sg, U (act g x) (act g z)
      = ∑ g ∈ Sg, (if act g x = x then U x z else 0) := Finset.sum_congr rfl hstep
    _ = ∑ g ∈ Sg.filter (fun g => act g x = x), U x z := by rw [Finset.sum_filter]
    _ = (Sg.filter (fun g => act g x = x)).card • U x z := Finset.sum_const _
    _ = ((Sg.filter (fun g => act g x = x)).card : ℝ) * U x z := by rw [nsmul_eq_mul]

end Work.PTCert
