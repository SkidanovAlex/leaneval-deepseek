import Submission.ZagierHoffmanProof.PrimeDominates
import Submission.ZagierHoffmanProof.PrimeJMin

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Thakur's dominance estimate for prime `q`

The dominance lemma `dominates_TT` is translated to the `jMin`-language for a finite field `F`
of prime cardinality: for every admissible shift `j ≠ jMin F k` and every `d`,

  `(k + jMin k) + s_d(k + jMin k) < (k + j) + s_d(k + j)`,  `s_d(y) = ∑_{i<d} T^{i+1}(y)`.

This is the input needed by Thakur's recursion `s_{d+1}(k) = s_d(s_1(k)) + s_1(k)`.
-/

namespace ZagierHoffmanPositiveChar

section JMinDominates

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The exponent `s_d(y) = ∑_{i<d} T^{i+1}(y)` of Thakur's recursion. -/
noncomputable def sExpG (d y : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d,
    ((Nat.iterate (TT (Nat.card F) (two_le_card F)) (i + 1) y : ℕ) : ℤ)

/-- `T y = y + jMin F y` for `y ≥ 1`. -/
lemma TT_eq_add_jMin (hp : (Nat.card F).Prime) {y : ℕ} (hy : 1 ≤ y) :
    TT (Nat.card F) (two_le_card F) y = y + jMin F ⟨y, hy⟩ := by
  have h : TT (Nat.card F) (two_le_card F) y
      = y + greedy (Nat.card F) (two_le_card F) (y - 1) := by
    show Tg (Nat.card F) (two_le_card F) (y - 1) = y + greedy (Nat.card F) (two_le_card F) (y - 1)
    unfold Tg
    omega
  rw [h]
  exact (congrArg (fun z => y + z) (jMin_eq_greedy F hp ⟨y, hy⟩)).symm

/-- **Thakur's dominance estimate.** -/
theorem jMin_dominates_prime (hp : (Nat.card F).Prime) (d : ℕ) (k : ℕ+) (j : ℕ) (hj : 1 ≤ j)
    (hadm : IsGoodJ F (k : ℕ) j) (hjne : j ≠ jMin F k) :
    ((k : ℕ) : ℤ) + (jMin F k : ℤ) + sExpG F d ((k : ℕ) + jMin F k)
      < ((k : ℕ) : ℤ) + (j : ℤ) + sExpG F d ((k : ℕ) + j) := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hk1 : 1 ≤ (k : ℕ) := k.pos
  have hAdm : Adm (Nat.card F) (k : ℕ) j := by
    have h := (isGoodJ_iff_noCarry F hp (k : ℕ) j hk1).mp hadm
    exact ⟨h.1, h.2.2, h.2.1⟩
  have hmin : jMin F k < j := by
    rcases lt_or_ge (jMin F k) j with h | h
    · exact h
    · exact absurd (le_antisymm (jMin_le F hadm) h) (fun hh => hjne hh.symm)
  have hdom : ∀ i, Nat.iterate (TT (Nat.card F) hq2) i (TT (Nat.card F) hq2 (k : ℕ))
      ≤ Nat.iterate (TT (Nat.card F) hq2) i ((k : ℕ) + j) :=
    fun i => dominates_TT hq2 hk1 hAdm i
  have hTk : TT (Nat.card F) hq2 (k : ℕ) = (k : ℕ) + jMin F k := TT_eq_add_jMin F hp hk1
  have hlt0 : ((Nat.iterate (TT (Nat.card F) hq2) 0 (TT (Nat.card F) hq2 (k : ℕ)) : ℕ) : ℤ)
      < ((Nat.iterate (TT (Nat.card F) hq2) 0 ((k : ℕ) + j) : ℕ) : ℤ) := by
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, hTk]
    omega
  have hsum : (∑ i ∈ Finset.range (d + 1),
        ((Nat.iterate (TT (Nat.card F) hq2) i (TT (Nat.card F) hq2 (k : ℕ)) : ℕ) : ℤ))
      < (∑ i ∈ Finset.range (d + 1),
        ((Nat.iterate (TT (Nat.card F) hq2) i ((k : ℕ) + j) : ℕ) : ℤ)) := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨0, Finset.mem_range.mpr (by omega), hlt0⟩
    exact_mod_cast hdom i
  have hL : ((k : ℕ) : ℤ) + (jMin F k : ℤ) + sExpG F d ((k : ℕ) + jMin F k)
      = ∑ i ∈ Finset.range (d + 1),
        ((Nat.iterate (TT (Nat.card F) hq2) i (TT (Nat.card F) hq2 (k : ℕ)) : ℕ) : ℤ) := by
    rw [hTk]
    unfold sExpG
    rw [Finset.sum_range_succ', Function.iterate_zero_apply]
    push_cast
    ring
  have hR : ((k : ℕ) : ℤ) + (j : ℤ) + sExpG F d ((k : ℕ) + j)
      = ∑ i ∈ Finset.range (d + 1),
        ((Nat.iterate (TT (Nat.card F) hq2) i ((k : ℕ) + j) : ℕ) : ℤ) := by
    unfold sExpG
    rw [Finset.sum_range_succ', Function.iterate_zero_apply]
    push_cast
    ring
  rw [hL, hR]
  exact hsum

end JMinDominates

end ZagierHoffmanPositiveChar
