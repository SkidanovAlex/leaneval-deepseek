import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.polyrel_chain_ind`: chains of `PolyRel`-steps

If `(I_i, P_i)`, `i = 0, …, ℓ`, is a sequence of intervals (left endpoint `x i`, length `Lv i > 0`)
carrying phases `Pv i`, and each consecutive pair satisfies the comparability relation
`PolyRel k C δ` with the *same* constant `C`, then the endpoints are related with the constant
`cycConst k C ℓ` obtained by iterating the transitivity constant `transConst` of
`Submission/Work/BMF/polyrel_basic.lean`.

The proof is an induction on `ℓ`, carried out for a `ℕ`-indexed chain (`polyrel_chain_nat`) so
that the induction step needs no reindexing of `Fin`s; the `Fin (ℓ+1)`-indexed chain of the
statement is then reindexed via `i ↦ min i ℓ`.  In the base case `ℓ = 0` the relation is
reflexive, which is why `cycConst k C 0 = max C 1 ≥ 1`.
-/

namespace Work.BMF

open Polynomial Finset Real

/-- `PolyRel` is reflexive, with any constant `C ≥ 1`, on an interval of nonnegative length. -/
lemma PolyRel.refl' {k : ℕ} {C δ x L : ℝ} {P : ℝ[X]} (hC : 1 ≤ C) (hL : 0 ≤ L) :
    PolyRel k C δ x L P x L P := by
  refine ⟨?_, ?_, ?_, 0, 0, Submodule.zero_mem _, Submodule.zero_mem _, ?_, ?_,
    IntegralOn.zero δ⟩
  · simpa using mul_le_mul_of_nonneg_right hC hL
  · simpa using mul_le_mul_of_nonneg_right hC hL
  · rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hL
  · show P = 0 + P + 0
    ring
  · intro t ht
    simp only [Polynomial.eval_zero, abs_zero]
    linarith

/-- A chain of `PolyRel`-steps with constant `C > 0`, indexed by `ℕ`: if every consecutive pair
`j, j+1` (`j < n`) is `PolyRel k C δ`-related, then the first and last intervals are related with
constant `cycConst k C n`. -/
lemma polyrel_chain_nat (k : ℕ) {C δ : ℝ} (hC : 0 < C) (n : ℕ)
    (y : ℕ → ℝ × ℝ × ℝ[X]) (hpos : ∀ i ≤ n, 0 < (y i).2.1)
    (hstep : ∀ j < n, PolyRel k C δ (y j).1 (y j).2.1 (y j).2.2
      (y (j + 1)).1 (y (j + 1)).2.1 (y (j + 1)).2.2) :
    PolyRel k (cycConst k C n) δ (y 0).1 (y 0).2.1 (y 0).2.2
      (y n).1 (y n).2.1 (y n).2.2 := by
  induction n generalizing y with
  | zero =>
      rw [cycConst_zero]
      exact PolyRel.refl' (le_max_right _ _) (le_of_lt (hpos 0 le_rfl))
  | succ m ih =>
      have h1 : PolyRel k (cycConst k C m) δ (y 0).1 (y 0).2.1 (y 0).2.2
          (y m).1 (y m).2.1 (y m).2.2 :=
        ih y (fun i hi => hpos i (by omega)) (fun j hj => hstep j (by omega))
      have h2 : PolyRel k C δ (y m).1 (y m).2.1 (y m).2.2
          (y (m + 1)).1 (y (m + 1)).2.1 (y (m + 1)).2.2 := hstep m (by omega)
      have h3 := h1.trans h2 (cycConst_pos k hC m) hC (hpos 0 (by omega))
        (hpos m (by omega)) (hpos (m + 1) (by omega))
      rwa [cycConst_succ]

theorem polyrel_chain_ind (k : ℕ) (C δ : ℝ) (hC : 1 ≤ C) (ℓ : ℕ) (x : Fin (ℓ + 1) → ℝ)
    (Lv : Fin (ℓ + 1) → ℝ) (Pv : Fin (ℓ + 1) → Polynomial ℝ) (hL : ∀ i, 0 < Lv i)
    (h : ∀ j : Fin ℓ, Work.BMF.PolyRel k C δ (x j.castSucc) (Lv j.castSucc) (Pv j.castSucc)
      (x j.succ) (Lv j.succ) (Pv j.succ)) :
    Work.BMF.PolyRel k (Work.BMF.cycConst k C ℓ) δ (x 0) (Lv 0) (Pv 0)
      (x (Fin.last ℓ)) (Lv (Fin.last ℓ)) (Pv (Fin.last ℓ)) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have key := polyrel_chain_nat k hCpos ℓ
    (fun i => (x ⟨min i ℓ, Nat.lt_succ_of_le (Nat.min_le_right i ℓ)⟩,
      Lv ⟨min i ℓ, Nat.lt_succ_of_le (Nat.min_le_right i ℓ)⟩,
      Pv ⟨min i ℓ, Nat.lt_succ_of_le (Nat.min_le_right i ℓ)⟩))
    (fun i _ => hL _)
    (by
      -- on the steps that matter (`j < ℓ`) the reindexed chain meets the original one
      intro j hj
      have h1 : (⟨min j ℓ, Nat.lt_succ_of_le (Nat.min_le_right j ℓ)⟩ : Fin (ℓ + 1))
          = (⟨j, hj⟩ : Fin ℓ).castSucc := by
        apply Fin.ext
        show min j ℓ = j
        exact Nat.min_eq_left (le_of_lt hj)
      have h2 : (⟨min (j + 1) ℓ, Nat.lt_succ_of_le (Nat.min_le_right (j + 1) ℓ)⟩ : Fin (ℓ + 1))
          = (⟨j, hj⟩ : Fin ℓ).succ := by
        apply Fin.ext
        show min (j + 1) ℓ = j + 1
        exact Nat.min_eq_left (by omega)
      simpa only [h1, h2] using h ⟨j, hj⟩)
  have h0 : (⟨min 0 ℓ, Nat.lt_succ_of_le (Nat.min_le_right 0 ℓ)⟩ : Fin (ℓ + 1)) = 0 := by
    apply Fin.ext
    show min 0 ℓ = 0
    exact Nat.min_eq_left (Nat.zero_le ℓ)
  have hℓ : (⟨min ℓ ℓ, Nat.lt_succ_of_le (Nat.min_le_right ℓ ℓ)⟩ : Fin (ℓ + 1))
      = Fin.last ℓ := by
    apply Fin.ext
    show min ℓ ℓ = ℓ
    exact Nat.min_self ℓ
  simpa only [h0, hℓ] using key

end Work.BMF
