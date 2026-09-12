import Submission.PVer1
import Submission.QuantileExt

/-!
# The roots of the pruned approximating polynomial `P̃_N`

`PVer1.prunePoly N = ∏_{i ∈ [2..N+1]} (X − α_{N+2,i})` is the degree-`N`
pruned polynomial of `P_{N+2,μ}`.  This module records, indexed by `Fin N`
via `gammaRoot N k := alpha (N+2) (k.val + 2)`:

1. the reindexed factorization `prunePoly N = ∏_{k : Fin N} (X − C(gammaRoot N k))`;
2. every root is in the OPEN Serre interval;
3. the roots are strictly increasing;
4. pairwise distances of distinct roots are `≥ (C·(N+2))⁻²`;
5. every root has margin `≥ (C·(N+2))⁻²` from BOTH Serre endpoints.

Ingredients (all in `Quantile`/`QuantileExt`/`PVer1Base`):
`alpha_strict_mono`, `PVer1.exists_root_isolation` (which bundles
`Quantile.exists_spacing`, `QuantileExt.exists_left_margin_all` and
`QuantileExt.exists_right_margin_all` into one constant `C`, expressed with a
factor `N`); here we re-express the same bounds with the factor `N + 2`
(weaker, since `N ≤ N + 2` and `C ≥ 1` keeps the product positive).
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.PruneRoots

open Submission.SerreExample
open Submission.Quantile
open Submission.QuantileExt
open Submission.PVer1

/-- The `k`-th kept root of `P_{N+2,μ}` (`k : Fin N` ↦ level `k.val+2`). -/
def gammaRoot (N : ℕ) (k : Fin N) : ℝ := alpha (N + 2) (k.val + 2)

/-- Reindex the product over `Icc 2 (N+1)` by `Fin N` via `k ↦ k.val + 2`
(which is a bijection between `Fin N` and `{2, …, N+1}`). -/
private lemma prod_Icc_two_shift (N : ℕ) {M : Type*} [CommMonoid M] (g : ℕ → M) :
    (∏ i ∈ Finset.Icc 2 (N + 1), g i) = ∏ k : Fin N, g (k.val + 2) := by
  symm
  classical
  exact Finset.prod_bij
    (s := (Finset.univ : Finset (Fin N))) (t := Finset.Icc 2 (N + 1))
    (f := fun k : Fin N => g (k.val + 2)) (g := g)
    (fun a _ => a.val + 2)
    (by intro a _; rw [Finset.mem_Icc]; omega)
    (by intro a₁ _ a₂ _ h; apply Fin.ext; omega)
    (by
      intro b hb
      rw [Finset.mem_Icc] at hb
      have hbge2 : 2 ≤ b := hb.1
      refine ⟨⟨b - 2, by omega⟩, by simp, ?_⟩
      exact Nat.sub_add_cancel hbge2)
    (by intro a _; rfl)

/-- The pruned polynomial factorises over the reindexed roots: precisely the
statement of `prunePoly N` with the kept-level set `{2,…,N+1}` reindexed by
`k : Fin N ↦ k.val + 2`. -/
private lemma prunePoly_eq_fin (N : ℕ) :
    prunePoly N = ∏ k : Fin N, (Polynomial.X - Polynomial.C (gammaRoot N k)) := by
  unfold prunePoly kept gammaRoot
  exact prod_Icc_two_shift N (fun i : ℕ => Polynomial.X - Polynomial.C (alpha (N + 2) i))

/-- The shifted level `k.val + 2` of a `Fin N` index lies in the kept set
`Icc 2 (N+1)` (always: `0 ≤ k.val < N`). -/
private lemma kept_shift_mem {N : ℕ} (k : Fin N) : k.val + 2 ∈ kept N := by
  unfold kept
  rw [Finset.mem_Icc]
  omega

/-- Root-structure of the pruned polynomial: reindexed factorization, open
interval membership, strict increase, spacing and two-sided margins, all with
the SAME constant `C ≥ 1` for every `N ≥ 2`. -/
theorem prune_roots :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (prunePoly N = ∏ k : Fin N, (Polynomial.X - Polynomial.C (gammaRoot N k))) ∧
      (∀ k : Fin N, aSerre < gammaRoot N k ∧ gammaRoot N k < bSerre) ∧
      (∀ i j : Fin N, i.val < j.val → gammaRoot N i < gammaRoot N j) ∧
      (∀ i j : Fin N, i.val < j.val →
        ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ gammaRoot N j - gammaRoot N i) ∧
      (∀ k : Fin N,
        (((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ gammaRoot N k - aSerre) ∧
        (((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ bSerre - gammaRoot N k)) := by
  rcases exists_root_isolation with ⟨C, hC1, hIso⟩
  refine ⟨C, hC1, ?_⟩
  intro N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN2pos : 0 < ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + 2)
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hC1
  -- `PVer1.exists_root_isolation` gives all three estimates with factor `N`;
  -- since `N ≤ N+2` and `C·(·) > 0`, the same estimates with factor `N+2` follow.
  have hwk : ∀ d : ℝ, (C * (N : ℝ))⁻¹ ^ 2 ≤ d → ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ d := by
    intro d hd
    have hNle : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ N + 2)
    have hmul : C * (N : ℝ) ≤ C * ((N + 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hNle (le_of_lt hCpos)
    have hp1 : 0 < C * (N : ℝ) := mul_pos hCpos hNpos
    have hp2 : 0 < C * ((N + 2 : ℕ) : ℝ) := mul_pos hCpos hN2pos
    have hinv : (C * ((N + 2 : ℕ) : ℝ))⁻¹ ≤ (C * (N : ℝ))⁻¹ :=
      (inv_le_inv₀ hp2 hp1).2 hmul
    have hsq : ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ (C * (N : ℝ))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hp2.le) hinv 2
    exact le_trans hsq hd
  -- 1. factorization
  have hfac : prunePoly N = ∏ k : Fin N, (Polynomial.X - Polynomial.C (gammaRoot N k)) :=
    prunePoly_eq_fin N
  -- 3. strict increase (order of the `Fin N` indices)
  have hmono : ∀ i j : Fin N, i.val < j.val → gammaRoot N i < gammaRoot N j := by
    intro i j hij
    unfold gammaRoot
    exact alpha_strict_mono (n := N + 2) (i := i.val + 2) (j := j.val + 2)
      (by omega) (by omega) (by omega) (by omega)
  -- isolation bounds (factor `N`), reindexed to `Fin N`
  have hleft0 : ∀ k : Fin N, (C * (N : ℝ))⁻¹ ^ 2 ≤ gammaRoot N k - aSerre := by
    intro k
    have h := (hIso N hN (k.val + 2) (kept_shift_mem k)).1
    simpa [gammaRoot] using h
  have hright0 : ∀ k : Fin N, (C * (N : ℝ))⁻¹ ^ 2 ≤ bSerre - gammaRoot N k := by
    intro k
    have h := (hIso N hN (k.val + 2) (kept_shift_mem k)).2.1
    simpa [gammaRoot] using h
  have hspace0 : ∀ i j : Fin N, i.val < j.val →
      (C * (N : ℝ))⁻¹ ^ 2 ≤ gammaRoot N j - gammaRoot N i := by
    intro i j hij
    have hne : j.val + 2 ≠ i.val + 2 := by omega
    have h := (hIso N hN (i.val + 2) (kept_shift_mem i)).2.2
        (j.val + 2) (kept_shift_mem j) hne
    have habs : |alpha (N + 2) (i.val + 2) - alpha (N + 2) (j.val + 2)| =
        gammaRoot N j - gammaRoot N i := by
      rw [abs_sub_comm]
      exact abs_of_pos (sub_pos.mpr (hmono i j hij))
    rwa [habs] at h
  -- 5. margins (factor `N+2`)
  have hleft : ∀ k : Fin N, ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ gammaRoot N k - aSerre := by
    intro k
    exact hwk (gammaRoot N k - aSerre) (hleft0 k)
  have hright : ∀ k : Fin N, ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ bSerre - gammaRoot N k := by
    intro k
    exact hwk (bSerre - gammaRoot N k) (hright0 k)
  -- 4. pairwise spacing (factor `N+2`)
  have hspace : ∀ i j : Fin N, i.val < j.val →
      ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 ≤ gammaRoot N j - gammaRoot N i := by
    intro i j hij
    exact hwk (gammaRoot N j - gammaRoot N i) (hspace0 i j hij)
  -- 2. open Serre-interval membership (the margins are strictly positive)
  have hmem : ∀ k : Fin N, aSerre < gammaRoot N k ∧ gammaRoot N k < bSerre := by
    intro k
    have hpos : 0 < ((C * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2 := by
      have hp : 0 < C * ((N + 2 : ℕ) : ℝ) := mul_pos hCpos hN2pos
      positivity
    constructor
    · have hl : gammaRoot N k - aSerre > 0 := lt_of_lt_of_le hpos (hleft k)
      linarith
    · have hr : bSerre - gammaRoot N k > 0 := lt_of_lt_of_le hpos (hright k)
      linarith
  exact ⟨hfac, hmem, hmono, hspace, fun k => ⟨hleft k, hright k⟩⟩

end Submission.PruneRoots
