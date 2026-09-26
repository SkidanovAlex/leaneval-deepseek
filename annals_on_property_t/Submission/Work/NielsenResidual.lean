import Submission.Work.NielsenEndCancel

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# The residual configuration: no end cancellation anywhere

`double_coset_shortens` splits into the *end-cancellation* branch (closed in
`NielsenEndCancel.lean`: a single `rho`/`rhoNeg`/`lam`/`lamNeg` move reduces
`N`) and the remaining *residual* case: **no end cancellation anywhere** — no
pair of basis images admits a boundary cancellation shortening either word.

This file formalises that residual hypothesis (`NoEndCancel`) and proves its
clean characterisation: `NoEndCancel α` holds if and only if `α` is a *local
minimum of `N` under all four elementary right-composition families*
(`rho`, `rhoNeg`, `lam`, `lamNeg`).  So the residual configuration is exactly
the class of the machine-checked `peakAut` example (`LongArm.lean`): `N`
cannot be decreased by any *single* elementary move.  The remaining content of
`double_coset_shortens` is that in this residual configuration a *macro*
(two-sided multiplication by words in the other basis images) still shortens —
the open classical core, machine-validated.
-/

namespace Submission.Nielsen

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- No basis image can be shortened at either end by multiplication with
another basis image (any sign). -/
def NoEndCancel (n : ℕ) (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))⁻¹) ∧
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))) ∧
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i)) ∧
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm ((α (FreeGroup.of j)) * α (FreeGroup.of i))

private lemma term_le_N (α : MulAut (FreeGroup (Fin n))) (i : Fin n) :
    FreeGroup.norm (α (FreeGroup.of i)) ≤ N α := by
  rw [N_eq_sum]
  have hsp : (∑ k : Fin n, FreeGroup.norm (α (FreeGroup.of k)))
      = (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)), FreeGroup.norm (α (FreeGroup.of k)))
          + FreeGroup.norm (α (FreeGroup.of i)) := by
    exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun k => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ i)).symm
  omega

/-- `N` does not decrease under `rho i j` iff multiplying `w_i` on the right
by `w_j` does not shorten `w_i`. -/
lemma N_le_N_mul_rho_iff {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) :
    N α ≤ N (α * rho i j hij) ↔
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of i) * α (FreeGroup.of j)) := by
  have hN := N_mul_rho α i j hij
  have hle := term_le_N α i
  constructor <;> omega

/-- `N` does not decrease under `rhoNeg i j` iff right multiplication by
`w_j⁻¹` does not shorten `w_i`. -/
lemma N_le_N_mul_rhoNeg_iff {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) :
    N α ≤ N (α * rhoNeg i j hij) ↔
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))⁻¹) := by
  have hN := N_mul_rhoNeg α i j hij
  have hle := term_le_N α i
  constructor <;> omega

/-- `N` does not decrease under `lam i j` iff left multiplication by `w_j`
does not shorten `w_i`. -/
lemma N_le_N_mul_lam_iff {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) :
    N α ≤ N (α * lam i j hij) ↔
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of j) * α (FreeGroup.of i)) := by
  have hN := N_mul_lam α i j hij
  have hle := term_le_N α i
  constructor <;> omega

/-- `N` does not decrease under `lamNeg i j` iff left multiplication by
`w_j⁻¹` does not shorten `w_i`. -/
lemma N_le_N_mul_lamNeg_iff {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) :
    N α ≤ N (α * lamNeg i j hij) ↔
      FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i)) := by
  have hN := N_mul_lamNeg α i j hij
  have hle := term_le_N α i
  constructor <;> omega

/-- **Characterisation of the residual configuration.**  `NoEndCancel α`
holds iff `α` is a local minimum of `N` under every single elementary
right-composition (`rho`, `rhoNeg`, `lam`, `lamNeg`). -/
theorem noEndCancel_iff_local_min (n : ℕ) (α : MulAut (FreeGroup (Fin n))) :
    NoEndCancel n α ↔
      (∀ i j (hij : i ≠ j), N α ≤ N (α * rho i j hij)) ∧
      (∀ i j (hij : i ≠ j), N α ≤ N (α * rhoNeg i j hij)) ∧
      (∀ i j (hij : i ≠ j), N α ≤ N (α * lam i j hij)) ∧
      (∀ i j (hij : i ≠ j), N α ≤ N (α * lamNeg i j hij)) := by
  constructor
  · intro hnec
    constructor
    · intro i j hij
      exact (N_le_N_mul_rho_iff α i j hij).2 (hnec i j hij).2.1
    · constructor
      · intro i j hij
        exact (N_le_N_mul_rhoNeg_iff α i j hij).2 (hnec i j hij).1
      · constructor
        · intro i j hij
          exact (N_le_N_mul_lam_iff α i j hij).2 (hnec i j hij).2.2.2
        · intro i j hij
          exact (N_le_N_mul_lamNeg_iff α i j hij).2 (hnec i j hij).2.2.1
  · intro hmin i j hij
    exact ⟨(N_le_N_mul_rhoNeg_iff α i j hij).1 (hmin.2.1 i j hij),
      (N_le_N_mul_rho_iff α i j hij).1 (hmin.1 i j hij),
      (N_le_N_mul_lamNeg_iff α i j hij).1 (hmin.2.2.2 i j hij),
      (N_le_N_mul_lam_iff α i j hij).1 (hmin.2.2.1 i j hij)⟩

end

end Submission.Nielsen
