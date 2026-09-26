import Submission.Work.Nielsen
import Submission.Work.SignedClosure

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# End-cancellation branch of `double_coset_shortens`

The first (easiest) way a coordinate can shorten: some basis image `w_i`
shares a cancellable boundary with another image `w_j` — i.e. one of
`|w_i · w_j^{±1}| < |w_i|` or `|w_j^{±1} · w_i| < |w_i|`.  In that case a
*single* elementary move already realises the shortening: right composition by
`rho`/`rhoNeg` (for the right variants) or `lam`/`lamNeg` (for the left
variants), each of which lies in `closure(AutGen n)` (`N_mul_rho`,
`N_mul_rhoNeg`, `N_mul_lam`, `N_mul_lamNeg` in `Nielsen.lean` give the exact
`N`-change).  This file closes that branch of the reduction:

    end_cancel_shortens : an end-cancelling pair (any of the four variants)
    yields γ ∈ closure(AutGen n) with N (α * γ) < N α.

The complementary branch — *no* end cancellation anywhere — is the hard
conjugation/multiplication analysis of `double_coset_shortens`.
-/

namespace Submission.Nielsen

noncomputable section

open scoped BigOperators

variable {n : ℕ}

private lemma rhoNeg_mem_closure' (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    rhoNeg i j hij ∈ AutClosure n := by
  have h : rho i j hij ∈ AutClosure n :=
    Subgroup.subset_closure (rho_mem_AutGen n hij)
  have hinv : (rho i j hij)⁻¹ ∈ AutClosure n := (AutClosure n).inv_mem h
  simpa [rho_inv_eq] using hinv

private lemma lamNeg_mem_closure' (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    lamNeg i j hij ∈ AutClosure n := by
  have h : lam i j hij ∈ AutClosure n :=
    Subgroup.subset_closure (lam_mem_AutGen n hij)
  have hinv : (lam i j hij)⁻¹ ∈ AutClosure n := (AutClosure n).inv_mem h
  simpa [lam_inv_eq] using hinv

private lemma term_le_N (α : MulAut (FreeGroup (Fin n))) (i : Fin n) :
    FreeGroup.norm (α (FreeGroup.of i)) ≤ N α := by
  rw [N_eq_sum]
  have hsp : (∑ k : Fin n, FreeGroup.norm (α (FreeGroup.of k)))
      = (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)), FreeGroup.norm (α (FreeGroup.of k)))
          + FreeGroup.norm (α (FreeGroup.of i)) := by
    exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun k => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ i)).symm
  omega

/-- **End-cancellation branch.**  If some pair `(i, j)`, `i ≠ j`, admits a
boundary cancellation that strictly shortens `w_i` (in any of the four
orientations), then a single Nielsen move realises the shortening:
`∃ γ ∈ closure(AutGen n)` with `N (α * γ) < N α`. -/
theorem end_cancel_shortens (n : ℕ) (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j)
    (hshort : FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of i))
      ∨ FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j)))
          < FreeGroup.norm (α (FreeGroup.of i))
      ∨ FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i))
          < FreeGroup.norm (α (FreeGroup.of i))
      ∨ FreeGroup.norm ((α (FreeGroup.of j)) * α (FreeGroup.of i))
          < FreeGroup.norm (α (FreeGroup.of i))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  have hle := term_le_N α i
  rcases hshort with hs | hs | hs | hs
  · -- right multiply by w_j⁻¹: γ := rhoNeg i j
    refine ⟨rhoNeg i j hij, rhoNeg_mem_closure' n hij, ?_⟩
    have hN := N_mul_rhoNeg α i j hij
    rw [hN]
    omega
  · -- right multiply by w_j: γ := rho i j
    refine ⟨rho i j hij, Subgroup.subset_closure (rho_mem_AutGen n hij), ?_⟩
    have hN := N_mul_rho α i j hij
    rw [hN]
    omega
  · -- left multiply by w_j⁻¹: γ := lamNeg i j
    refine ⟨lamNeg i j hij, lamNeg_mem_closure' n hij, ?_⟩
    have hN := N_mul_lamNeg α i j hij
    rw [hN]
    omega
  · -- left multiply by w_j: γ := lam i j
    refine ⟨lam i j hij, Subgroup.subset_closure (lam_mem_AutGen n hij), ?_⟩
    have hN := N_mul_lam α i j hij
    rw [hN]
    omega

end

end Submission.Nielsen
