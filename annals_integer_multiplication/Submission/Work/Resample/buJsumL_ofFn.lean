import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWstepKit

/-!
# `Work.Resample.buJsumL_ofFn`

The Neumann-sum stage of the `B̃` word: the list-level fold `buJsumL` of `buQWdefs` computes
the same thing as the `Fin`-level alternating sum `buJsum` of `buDefs`, provided the single
round agrees (`buRoundL (List.ofFn v) = List.ofFn (buRound v)`, the hypothesis `hR`).

The proof is pure list/vector arithmetic: the fold over the sign list `buSignsL n` keeps, at
its `k`-th step, the `k`-th iterate as first component and the alternating sum of the first
`k+1` iterates as second component.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Pointwise operations on `Fin s`-vectors -/

/-- Pointwise addition of two `Fin s`-vectors of fixed-point pairs. -/
def buPAdd {s : ℕ} (a b : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun i => ((a i).1 + (b i).1, (a i).2 + (b i).2)

/-- Pointwise scalar multiplication of a `Fin s`-vector. -/
def buPSMul {s : ℕ} (c : ℤ) (a : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun i => (c * (a i).1, c * (a i).2)

theorem buAddV_ofFn {s : ℕ} (a b : Fin s → ℤ × ℤ) :
    buAddV (List.ofFn a) (List.ofFn b) = List.ofFn (buPAdd a b) := by
  induction s with
  | zero => rw [List.ofFn_zero, List.ofFn_zero]; rfl
  | succ s ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      rw [show buAddV (a 0 :: List.ofFn fun i => a i.succ) (b 0 :: List.ofFn fun i => b i.succ)
          = ((a 0).1 + (b 0).1, (a 0).2 + (b 0).2) ::
            buAddV (List.ofFn fun i => a i.succ) (List.ofFn fun i => b i.succ) from rfl]
      rw [ih, List.ofFn_succ]
      rfl

theorem buSMulV_ofFn {s : ℕ} (c : ℤ) (a : Fin s → ℤ × ℤ) :
    buSMulV c (List.ofFn a) = List.ofFn (buPSMul c a) := by
  rw [buSMulV, List.map_ofFn]
  rfl

/-! ## The alternating sum accumulated by the fold -/

/-- The alternating sum `Σ_{j ≤ k} (-1)^j v^{(j)}` of the first `k+1` iterates of `buRound`. -/
noncomputable def buJacc (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s)
    (v : Fin s → ℤ × ℤ) (k : ℕ) : Fin s → ℤ × ℤ :=
  fun ℓ => ((∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j) * (buIter Wt p α s t hs v j ℓ).1),
            (∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j) * (buIter Wt p α s t hs v j ℓ).2))

theorem buIter_zero (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) :
    buIter Wt p α s t hs v 0 = v := rfl

theorem buIter_succ (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) (k : ℕ) :
    buIter Wt p α s t hs v (k + 1) = buRound Wt p α s t hs (buIter Wt p α s t hs v k) := rfl

/-- `buJacc` at `0` is the initial vector. -/
theorem buJacc_zero (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) :
    buJacc Wt p α s t hs v 0 = v := by
  funext ℓ
  simp only [buJacc, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_mul, zero_add]
  exact Prod.mk.eta.symm

/-- The recursion step of `buJacc`: adding the next iterate with the sign `(-1)^{k+1}`. -/
theorem buJacc_succ (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) (k : ℕ) :
    buPAdd (buJacc Wt p α s t hs v k)
        (buPSMul ((-1 : ℤ) ^ (k + 1)) (buRound Wt p α s t hs (buIter Wt p α s t hs v k)))
      = buJacc Wt p α s t hs v (k + 1) := by
  funext ℓ
  simp only [buPAdd, buPSMul, buJacc, Finset.sum_range_succ]
  rfl

/-- The fold over the first `k` signs of `buSignsL` produces the `k`-th iterate together with the
alternating sum of the first `k+1` iterates. -/
theorem buJfold_range (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s)
    (hR : ∀ v : Fin s → ℤ × ℤ,
      buRoundL Wt p s (egM p α) (List.ofFn v) = List.ofFn (buRound Wt p α s t hs v))
    (v : Fin s → ℤ × ℤ) (k : ℕ) :
    List.foldl (fun st (σ : ℤ) => (buRoundL Wt p s (egM p α) st.1,
        buAddV st.2 (buSMulV σ (buRoundL Wt p s (egM p α) st.1))))
      (List.ofFn v, List.ofFn v) ((List.range k).map (fun j => (-1 : ℤ) ^ (j + 1)))
    = (List.ofFn (buIter Wt p α s t hs v k), List.ofFn (buJacc Wt p α s t hs v k)) := by
  induction k with
  | zero =>
      simp only [List.range_zero, List.map_nil, List.foldl_nil]
      apply Prod.ext
      · rfl
      · rw [buJacc_zero]
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hR (buIter Wt p α s t hs v k), buIter_succ]
      rw [buSMulV_ofFn, buAddV_ofFn, buJacc_succ]

/-- `buSignsL` is the sign list of the fold, written as a map of `List.range`. -/
theorem buSignsL_eq (n : ℕ) :
    buSignsL n = (List.range (n - 1)).map (fun j => (-1 : ℤ) ^ (j + 1)) := rfl

theorem egN_pos (p α s t : ℕ) : 0 < egN p α s t := by
  simp only [egN]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_left 1 _)

/-! ## The main lemma -/

theorem buJsumL_ofFn (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (hR : ∀ v : Fin s → ℤ × ℤ, buRoundL Wt p s (egM p α) (List.ofFn v) = List.ofFn (buRound Wt p α s t hs v)) (v : Fin s → ℤ × ℤ) : buJsumL Wt p s (egM p α) (egN p α s t) (List.ofFn v) = List.ofFn (buJsum Wt p α s t hs v) := by
  have hfold : buJsumL Wt p s (egM p α) (egN p α s t) (List.ofFn v)
      = (List.foldl (fun st (σ : ℤ) => (buRoundL Wt p s (egM p α) st.1,
          buAddV st.2 (buSMulV σ (buRoundL Wt p s (egM p α) st.1))))
          (List.ofFn v, List.ofFn v)
          ((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1)))).2 := rfl
  rw [hfold, buJfold_range Wt p α s t hs hR v (egN p α s t - 1)]
  apply List.ofFn_inj.mpr
  funext ℓ
  have hpred : (egN p α s t - 1) + 1 = egN p α s t := Nat.succ_pred_eq_of_pos (egN_pos p α s t)
  simp only [buJacc, buJsum, hpred]

end Work.Resample
