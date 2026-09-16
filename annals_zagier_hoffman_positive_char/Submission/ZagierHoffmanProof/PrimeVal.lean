import Submission.ZagierHoffmanProof.PrimeJMinDom
import Submission.ZagierHoffmanProof.StepM7

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Thakur's recursion for prime `q`

`v (P_d k) = exp (−∑_{i≤d} T^i(k))`, `T k = k + j_min(k)`: the exact degree at infinity of the
depth-one power sums over a finite field of prime cardinality.  This is Thakur's Theorem 1 in
the form `s_{d+1}(k) = s_d(s_1(k)) + s_1(k)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section SExpBasic

lemma sExpG_zero (k : ℕ) : sExpG F 0 k = 0 := by
  unfold sExpG
  simp

lemma sExpG_nonneg (d k : ℕ) : 0 ≤ sExpG F d k := by
  unfold sExpG
  exact Finset.sum_nonneg fun i _ => Int.natCast_nonneg _

lemma sExpG_succ (d k : ℕ) :
    sExpG F (d + 1) k = ((Nat.iterate (TT (Nat.card F) (two_le_card F)) 1 k : ℕ) : ℤ)
      + sExpG F d (Nat.iterate (TT (Nat.card F) (two_le_card F)) 1 k) := by
  unfold sExpG
  rw [Finset.sum_range_succ', add_comm]
  congr 1


end SExpBasic

section Main

/-- The valuation of a summand of the truncated level recursion, for the general exponent. -/
lemma expTerm_valG (d : ℕ) (k : ℕ+) (j : ℕ)
    (hP : ∀ m : ℕ+, Valued.v (P F d m) = exp (-(sExpG F d (m : ℕ))))
    (hc : binF F k j * psumF F j ≠ 0) :
    Valued.v (expTerm F d k j)
      = exp (-(((k : ℤ) + j) + sExpG F d ((k : ℕ) + j))) :=
  v_P_expansion_term F d k j (sExpG F d ((k : ℕ) + j)) (hP _) hc

/-- **Thakur's Theorem 1** (exact valuation of the depth-one power sums) for `q` prime. -/
theorem val_P_iter_prime (hp : (Nat.card F).Prime) (d : ℕ) (k : ℕ+) :
    Valued.v (P F d k) = exp (-(sExpG F d (k : ℕ))) := by
  induction d generalizing k with
  | zero =>
      rw [P_zero_eq_one F k, sExpG_zero]
      simp
  | succ d ih =>
      set T := TT (Nat.card F) (two_le_card F) with hT
      have hTk : T (k : ℕ) = (k : ℕ) + jMin F k := TT_eq_add_jMin F hp k.pos
      have hTk' : T (k : ℕ) = (k : ℕ) + jMin F k := hTk
      set S : ℤ := sExpG F d ((k : ℕ) + jMin F k) with hS
      have hSnn : 0 ≤ S := sExpG_nonneg F d _
      set N : ℕ := (k : ℕ) + jMin F k + S.toNat with hN
      obtain ⟨E, hE, hvE⟩ := P_succ_expansion' F d N k
      have hjc : binF F k (jMin F k) * psumF F (jMin F k) ≠ 0 :=
        (mul_binF_psumF_ne_zero_iff F (k : ℕ) (jMin F k)).mpr (jMin_spec F k)
      have hvalj := expTerm_valG F d k (jMin F k) ih hjc
      have hdom : ∀ j ∈ Finset.range (N + 1), j ≠ jMin F k →
          Valued.v (expTerm F d k j) < Valued.v (expTerm F d k (jMin F k)) := by
        intro j _ hjne
        by_cases hc : binF F k j * psumF F j = 0
        · rw [expTerm_eq_zero F d k j hc, map_zero, hvalj]
          exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
        · rw [expTerm_valG F d k j ih hc, hvalj]
          refine WithZero.exp_lt_exp.mpr ?_
          have hgj : IsGoodJ F (k : ℕ) j := (mul_binF_psumF_ne_zero_iff F (k : ℕ) j).mp hc
          have := jMin_dominates_prime F hp d k j hgj.1 hgj hjne
          linarith
      have hjmin_mem : jMin F k ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range, hN]
        have := jMin_pos F k
        omega
      have hsum := Valuation.map_sum_eq_of_lt (v := Valued.v) hjmin_mem (by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
        exact hdom i hi.1 hi.2)
      have hElt : Valued.v E < Valued.v (expTerm F d k (jMin F k)) := by
        rw [hvalj]
        refine lt_of_le_of_lt hvE (WithZero.exp_lt_exp.mpr ?_)
        have hSc : ((S.toNat : ℕ) : ℤ) = S := Int.toNat_of_nonneg hSnn
        have hNc : ((N : ℕ) : ℤ) = (k : ℤ) + jMin F k + S := by
          rw [hN]; push_cast [hSc]; ring
        have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast k.pos
        have hj0 : (0 : ℤ) ≤ (jMin F k : ℤ) := by exact_mod_cast (Nat.zero_le _)
        have hd1 : (1 : ℤ) ≤ (d : ℤ) + 1 := by omega
        have hkn : (1 : ℤ) ≤ (k : ℤ) + (N : ℤ) + 1 := by
          have : (0 : ℤ) ≤ (N : ℤ) := Nat.cast_nonneg N; linarith
        rw [hNc]
        nlinarith [hd1, hk1, hj0, hkn]
      have hiter : Nat.iterate (TT (Nat.card F) (two_le_card F)) 1 (k : ℕ)
          = (k : ℕ) + jMin F k := by
        rw [Function.iterate_one]
        exact hTk
      rw [hE, Valuation.map_add_eq_of_lt_left (v := Valued.v) (by rw [hsum]; exact hElt),
        hsum, hvalj, sExpG_succ, hiter]
      congr 1

end Main

end ZagierHoffmanPositiveChar
