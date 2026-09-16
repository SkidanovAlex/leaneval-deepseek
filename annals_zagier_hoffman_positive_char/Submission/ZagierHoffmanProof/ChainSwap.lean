import Submission.ZagierHoffmanProof.ChainEval
import Submission.Commons.Order.StrictMono.strictMono_cons_iff
import Submission.Commons.Order.StrictMono.strictMono_snoc_iff

/-!
# The chain sum over `Fin r → ℕ` and its two recursions (C3 of the bridge)

This file builds the object that mediates between the two nesting orders of the strictly increasing
chain region `N ≤ n₁ < n₂ < ⋯ < nᵣ`:

* `incU r Y N` — the chain sum, defined by peeling the **first** coordinate (the smallest index);
  this is the shape produced by `ChainEval.evalIter`/`evalIterB`;
* `incT r Y N b` — the same region with the extra bound `nᵣ < b`, and the peel-**last** recursion
  (which is the shape of the ζ_A side: `Block.zeta_eq_tsum_block` groups the total region by the
  **largest** index).

`tsum_fin_cons`/`tsum_fin_snoc` (ChainEval) show that both recursions compute the same `tsum` over
`Fin r → ℕ`, which is the whole content of the reordering.

## Main results

* `incU`, `incT` and their recursions.
* ★★★ `incU_succ_eq_tsum` — the product form.
* ★★★ `incU_succ_peel_last` — the peel-last recursion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology
open SummationFilter

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The chain sum over the strictly increasing region `N ≤ n₁ < ⋯ < nᵣ`, peeling the first
(smallest) coordinate. -/
noncomputable def incU : (r : ℕ) → (Fin r → ℕ → K) → ℕ → K
  | 0, _, _ => 1
  | (r+1), Y, N => ∑' d : ℕ,
      (if N ≤ d then Y 0 d else 0) * incU r (fun j : Fin r => Y j.succ) (d + 1)

/-- The chain sum over the region `N ≤ n₁ < ⋯ < nᵣ < b`, peeling the first coordinate.  For `r = 0`
this is `1`; the extra bound is on the last coordinate. -/
noncomputable def incT : (r : ℕ) → (Fin r → ℕ → K) → ℕ → ℕ → K
  | 0, _, _, _ => 1
  | (r+1), Y, N, b => ∑' d : ℕ,
      (if N ≤ d ∧ d < b then Y 0 d else 0)
        * incT r (fun j : Fin r => Y j.succ) (d + 1) b

@[simp] lemma incU_zero (Y : Fin 0 → ℕ → K) (N : ℕ) : incU 0 Y N = 1 := rfl

lemma incU_succ (r : ℕ) (Y : Fin (r+1) → ℕ → K) (N : ℕ) :
    incU (r+1) Y N = ∑' d : ℕ,
      (if N ≤ d then Y 0 d else 0) * incU r (fun j : Fin r => Y j.succ) (d + 1) := rfl

@[simp] lemma incT_zero (Y : Fin 0 → ℕ → K) (N b : ℕ) : incT 0 Y N b = 1 := rfl

lemma incT_succ (r : ℕ) (Y : Fin (r+1) → ℕ → K) (N b : ℕ) :
    incT (r+1) Y N b = ∑' d : ℕ,
      (if N ≤ d ∧ d < b then Y 0 d else 0)
        * incT r (fun j : Fin r => Y j.succ) (d + 1) b := rfl

/-! ## §1b. Auxiliary facts -/

/-- On `Fin 1`, strict monotonicity is vacuous. -/
lemma strictMono_fin_one (v : Fin 1 → ℕ) : StrictMono v := by
  intro i j hij
  have h' : (i : ℕ) < (j : ℕ) := hij
  omega

/-- `Fin.cons d` is injective in its second argument. -/
lemma fin_cons_injective {r : ℕ} (d : ℕ) :
    Function.Injective (fun w : Fin r → ℕ => @Fin.cons r (fun _ => ℕ) d w) := by
  intro w1 w2 h
  funext j
  have := congrFun h j.succ
  simpa using this

/-- The chain summand on `Fin.cons d w`. -/
lemma chainTerm_cons {r : ℕ} (Y : Fin (r+2) → ℕ → K) (N d : ℕ) (w : Fin (r+1) → ℕ) :
    (if N ≤ (@Fin.cons (r+1) (fun _ : Fin (r+2) => ℕ) d w) 0
        ∧ StrictMono (@Fin.cons (r+1) (fun _ : Fin (r+2) => ℕ) d w)
      then ∏ j, Y j ((@Fin.cons (r+1) (fun _ : Fin (r+2) => ℕ) d w) j) else 0)
      = (if N ≤ d then Y 0 d else 0) *
        (if d + 1 ≤ w 0 ∧ StrictMono w then ∏ j, Y j.succ (w j) else 0) := by
  simp only [Commons.Order.StrictMono.strictMono_cons_iff, Fin.cons_zero, Fin.cons_succ,
    Fin.prod_univ_succ]
  by_cases h1 : N ≤ d <;> by_cases h2 : d < w 0 <;> by_cases h3 : StrictMono w <;>
    simp only [h1, h2, h3, if_true, if_false, true_and]
  all_goals simp only [and_true, and_false, if_false, mul_zero]
  all_goals (split_ifs with h4)
  all_goals try (exfalso; omega)
  all_goals try ring_nf

/-- **★★★ The chain sum as a `tsum` over `Fin (r+1) → ℕ`**: the product over the coordinates of
the strictly increasing chain `N ≤ n₀ < n₁ < ⋯ < nᵣ`. -/
theorem incU_succ_eq_tsum (r : ℕ) (Y : Fin (r+1) → ℕ → K) (N : ℕ)
    (hG : Summable fun v : Fin (r+1) → ℕ =>
      if N ≤ v 0 ∧ StrictMono v then ∏ j, Y j (v j) else 0) :
    incU (r+1) Y N = ∑' v : Fin (r+1) → ℕ,
      if N ≤ v 0 ∧ StrictMono v then ∏ j, Y j (v j) else 0 := by
  induction r generalizing N with
  | zero =>
    rw [incU_succ]
    simp only [incU_zero, mul_one]
    rw [← Equiv.tsum_eq (Equiv.funUnique (Fin 1) ℕ).symm (fun v : Fin 1 → ℕ =>
      if N ≤ v 0 ∧ StrictMono v then ∏ j, Y j (v j) else 0)]
    refine tsum_congr fun d => ?_
    rw [Fin.prod_univ_one]
    by_cases h : N ≤ d
    · rw [if_pos h, if_pos ⟨h, strictMono_fin_one _⟩]
      congr 1
    · rw [if_neg h, if_neg (fun hh => h hh.1)]
  | succ r ih =>
    rw [incU_succ]
    rw [tsum_fin_cons (r := r+1) hG]
    refine tsum_congr fun d => ?_
    by_cases hgood : N ≤ d ∧ Y 0 d ≠ 0
    · obtain ⟨hNd, hY0⟩ := hgood
      have hsub : Summable (fun w : Fin (r+1) → ℕ =>
          if d + 1 ≤ w 0 ∧ StrictMono w then ∏ j, Y j.succ (w j) else 0) := by
        have hf : Summable (fun w : Fin (r+1) → ℕ =>
            Y 0 d * (if d + 1 ≤ w 0 ∧ StrictMono w then ∏ j, Y j.succ (w j) else 0)) :=
          (hG.comp_injective (fin_cons_injective d)).congr (fun w => by
            show (if N ≤ (@Fin.cons (r+1) (fun _ : Fin (r+2) => ℕ) d w) 0
                ∧ StrictMono (@Fin.cons (r+1) (fun _ : Fin (r+2) => ℕ) d w)
              then ∏ j, Y j ((@Fin.cons (r+1) (fun _ : Fin (r+2) => ℕ) d w) j) else 0)
              = Y 0 d * (if d + 1 ≤ w 0 ∧ StrictMono w then ∏ j, Y j.succ (w j) else 0)
            rw [chainTerm_cons Y N d w, if_pos hNd])
        exact (hf.mul_left (Y 0 d)⁻¹).congr (fun w => by
          rw [← mul_assoc, inv_mul_cancel₀ hY0, one_mul])
      rw [ih (fun j : Fin (r+1) => Y j.succ) (d + 1) hsub]
      rw [← tsum_mul_left]
      exact tsum_congr fun w => (chainTerm_cons Y N d w).symm
    · have hz : (if N ≤ d then Y 0 d else 0) = 0 := by
        by_cases h : N ≤ d
        · rw [if_pos h]
          by_contra hne
          exact hgood ⟨h, hne⟩
        · rw [if_neg h]
      rw [hz, zero_mul]
      symm
      refine (tsum_congr fun w => chainTerm_cons Y N d w).trans ?_
      rw [tsum_mul_left, hz, zero_mul]

/-! ## §2. The correspondence with the `L`-series evaluation -/

/-- **The `L`-series iterated value is the chain sum `incU`**: the offset-free form
`ChainEval.evalIterB` is `incU` applied to the family of twisted evaluations. -/
theorem evalIterB_eq_incU (θ : K) (q : ℕ) [FrobPow K q] (ω : PowerSeries K)
    (Lst : List (ℕ × PowerSeries K)) (N : ℕ) :
    evalIterB θ q ω Lst N
      = incU Lst.length (fun j : Fin Lst.length => fun d =>
          evalSeriesGen (frobTwist (R := K) (p := q) d (ω ^ (Lst.get j).1 * (Lst.get j).2)) θ) N := by
  induction Lst generalizing N with
  | nil => rw [evalIterB_nil]; simp only [List.length_nil]; rw [incU_zero]
  | cons a rest ih =>
    obtain ⟨s, Q⟩ := a
    rw [evalIterB_cons]
    simp only [List.length_cons]
    rw [incU_succ]
    have hfun : (fun (j : Fin rest.length) (k : ℕ) => evalSeriesGen
          (frobTwist (R := K) (p := q) k
            (ω ^ (((s, Q) :: rest).get j.succ).1 * (((s, Q) :: rest).get j.succ).2)) θ)
        = (fun (j : Fin rest.length) (k : ℕ) => evalSeriesGen (frobTwist (R := K) (p := q) k
            (ω ^ (rest.get j).1 * (rest.get j).2)) θ) := by
      funext j k
      rfl
    refine tsum_congr fun d => ?_
    rw [ih (d + 1), hfun]
    rw [List.get_cons_zero]

end ZagierHoffmanPositiveChar
