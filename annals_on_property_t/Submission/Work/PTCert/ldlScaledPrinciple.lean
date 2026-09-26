import Mathlib
import Submission.Work.PTCert.Chain
import Submission.Work.PTCert.ldlPrinciple

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
Prove `LdlScaledPrinciple`.  `L Lᵀ` is PSD, and `R` is PSD by the diagonal-dominance argument already proved in
`Submission/Work/PTCert/ldlPrinciple.lean` (and helpers `psdDiagDominant.lean`, `offDiagBound.lean`) — reuse;
so `N := of (w i * M i j * w j)` is PSD; then `M = D⁻¹ N D⁻¹` with `D = diagonal w` (w > 0) is PSD
(`Matrix.PosSemidef.mul_mul_conjTranspose_same` with the diagonal matrix `diagonal (fun i => (w i)⁻¹)`). ~60 lines.
-/

namespace Work.PTCert

open Submission.PTCert

/-- Congruence by an invertible positive diagonal matrix preserves positive semidefiniteness:
if `N = D M D` with `D = diagonal w` and `w > 0`, then `N ⪰ 0` implies `M = D⁻¹ N D⁻¹ ⪰ 0`. -/
lemma posSemidef_of_scaled {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hN : (Matrix.of fun i j => w i * M i j * w j).PosSemidef) :
    M.PosSemidef := by
  have hD : (Matrix.diagonal fun i => (w i)⁻¹) * (Matrix.of fun i j => w i * M i j * w j)
      * (Matrix.diagonal fun i => (w i)⁻¹).conjTranspose = M := by
    ext i j
    rw [Matrix.diagonal_conjTranspose]
    simp only [star_trivial]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply]
    have hi : w i ≠ 0 := ne_of_gt (hw i)
    have hj : w j ≠ 0 := ne_of_gt (hw j)
    field_simp
  rw [← hD]
  exact hN.mul_mul_conjTranspose_same _

theorem ldlScaledPrinciple : LdlScaledPrinciple := by
  intro n M L R w hw hsym hdom hW
  have hN : (Matrix.of fun i j => w i * M i j * w j).PosSemidef := by
    rw [hW]
    refine Matrix.PosSemidef.add ?_ ?_
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
        (Matrix.PosSemidef.one (n := Fin n) (R := ℝ)).mul_mul_conjTranspose_same L
    · exact posSemidef_of_diag_dominant R hsym hdom
  exact posSemidef_of_scaled w hw hN

end Work.PTCert
