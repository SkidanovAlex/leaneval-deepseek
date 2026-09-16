import Submission.ZagierHoffmanProof.AExpansion
import Submission.ZagierHoffmanProof.D2
import Submission.ZagierHoffmanProof.ThakurDeg3

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# The degree of the level-one power-sum polynomials `A_n`

Carlitz's expansion (`AExpansion.lean`, `A_thakur_formula`)
`A_n = (-1)^n ∑_{m} (-1)^m C(n-1-m(q-1),m) [1]^{m(q-1)}` has *distinct* degrees
`m(q-1)q` for distinct `m`, so the degree of `A_n` is determined by the largest index `m*`
whose binomial coefficient does not vanish in `F`:

  `mStar n = max {m ≤ n : C(n-1-m(q-1), m) ≠ 0}`,   `natDegree (A_n) = (q-1)q·mStar n`.

This is the `d = 1` case of Thakur's Hypothesis H1 (the *uniqueness of the maximizing
decomposition* of Carlitz's formula) and it holds for every finite field, whereas the
`d ≥ 2` counterpart H2 fails for `q = 4` (Thakur 2009, Appendix A.11).

Combining the degree formula with the exact degree of the power sums
(`ThakurDeg3.val_P_one`: `v (P F 1 n) = exp (-(n + jMin F n))`) and the relation
`A_n = [1]^n · P_1(n)` (`D2.A_RatFunc_eq`) gives a **closed form for Thakur's `jMin`**:

  `jMin F n = (q-1) * (n - q * mStar n)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The largest index of Carrlitz's expansion whose coefficient does not vanish: Thakur's
maximizing index (`d = 1` case of H1). -/
noncomputable def mStar (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) ≠ 0) n

lemma mStar_le (n : ℕ) : mStar F n ≤ n := by
  classical
  have h := (Nat.findGreatest_eq_iff (P := fun m => ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) ≠ 0) (k := n)).mp rfl
  exact h.1

lemma mStar_spec (n : ℕ) :
    ((Nat.choose ((n - 1) - mStar F n * (Nat.card F - 1)) (mStar F n) : ℕ) : F) ≠ 0 := by
  classical
  rcases Nat.eq_zero_or_pos (mStar F n) with h | h
  · rw [h]
    have h1 : ((Nat.choose ((n - 1) - 0 * (Nat.card F - 1)) 0 : ℕ) : F) = 1 := by
      rw [Nat.zero_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
    rw [h1]
    exact one_ne_zero
  · have hh := (Nat.findGreatest_eq_iff (P := fun m => ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) ≠ 0) (k := n)).mp rfl
    exact hh.2.1 (Nat.pos_iff_ne_zero.mp h)

lemma mStar_max (n m : ℕ) (hm : mStar F n < m) (hmn : m ≤ n) :
    ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) = 0 := by
  classical
  have hh := (Nat.findGreatest_eq_iff (P := fun m => ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) ≠ 0) (k := n)).mp rfl
  by_contra hne
  exact hh.2.2 hm hmn hne

/-- `[1]^(q-1)`, the base of Carlitz's expansion. -/
noncomputable def carlitzBracketPow : F[X] := (carlitzOne F) ^ (Nat.card F - 1)

lemma carlitzBracketPow_monic : (carlitzBracketPow F).Monic := (carlitzOne_monic F).pow _

lemma carlitzBracketPow_ne_zero : (carlitzBracketPow F) ≠ 0 :=
  (carlitzBracketPow_monic F).ne_zero

lemma carlitzBracketPow_natDegree :
    (carlitzBracketPow F).natDegree = (Nat.card F - 1) * Nat.card F := by
  rw [carlitzBracketPow, (carlitzOne_monic F).natDegree_pow, carlitzOne_natDegree]

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `(-1)^m` as a constant polynomial. -/
lemma neg_one_pow_eq_C (m : ℕ) : (-1 : F[X]) ^ m = Polynomial.C ((-1 : F) ^ m) := by
  rw [show (-1 : F[X]) = Polynomial.C (-1 : F) by simp, ← Polynomial.C_pow]

/-- Degree bound for a finite sum of polynomials with a common degree bound. -/
private lemma natDegree_sum_le' {ι : Type*} (s : Finset ι) (f : ι → F[X]) (M : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ M) : (∑ i ∈ s, f i).natDegree ≤ M := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

/-- The summands of Carlitz's expansion, in `C`-normalised form. -/
private noncomputable def aThakurTerm (n m : ℕ) : F[X] :=
  Polynomial.C (((-1 : F) ^ m) * ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F)) *
    (carlitzBracketPow F) ^ m

private lemma thakurSum_eq_sum_terms (n : ℕ) :
    thakurSum F n = ∑ m ∈ Finset.range (n + 1), aThakurTerm F n m := by
  rw [thakurSum]
  apply Finset.sum_congr rfl
  intro m _
  rw [aThakurTerm, carlitzBracketPow, neg_one_pow_eq_C F m, ← Polynomial.C_mul]

private lemma term_natDegree_le (n m : ℕ) (hm : m ∈ Finset.range (n + 1)) :
    (aThakurTerm F n m).natDegree ≤ (Nat.card F - 1) * Nat.card F * mStar F n := by
  classical
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  by_cases hcase : m ≤ mStar F n
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_pow, carlitzBracketPow_natDegree]
    have h2 : m * ((Nat.card F - 1) * Nat.card F) ≤ mStar F n * ((Nat.card F - 1) * Nat.card F) :=
      Nat.mul_le_mul_right _ hcase
    calc 0 + m * ((Nat.card F - 1) * Nat.card F)
        = m * ((Nat.card F - 1) * Nat.card F) := by ring
      _ ≤ mStar F n * ((Nat.card F - 1) * Nat.card F) := h2
      _ = (Nat.card F - 1) * Nat.card F * mStar F n := by ring
  · have hc0 : ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) = 0 :=
      mStar_max F n m (lt_of_not_ge hcase) hmn
    have hz : aThakurTerm F n m = 0 := by
      rw [aThakurTerm, hc0, mul_zero, Polynomial.C_0, zero_mul]
    rw [hz, Polynomial.natDegree_zero]
    exact Nat.zero_le _

/-- ★ **The degree of `A_n`**: `natDegree (A_n) = (q-1)q·mStar n`. -/
theorem natDegree_A (n : ℕ) (hn : 1 ≤ n) :
    (A F n).natDegree = (Nat.card F - 1) * Nat.card F * mStar F n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  set N := (Nat.card F - 1) * Nat.card F * mStar F n with hN
  have hA : A F n = (-1 : F[X]) ^ n * ∑ m ∈ Finset.range (n + 1), aThakurTerm F n m := by
    rw [A_thakur_formula F n hn, thakurB_eq F n, thakurSum_eq_sum_terms F n]
  have hmain : (∑ m ∈ Finset.range (n + 1), aThakurTerm F n m).natDegree = N := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_sum_le' F (Finset.range (n + 1)) (fun m => aThakurTerm F n m) N
        (fun m hm => term_natDegree_le F n m hm)) ?_
    have hsplit : (∑ m ∈ Finset.range (n + 1), aThakurTerm F n m).coeff N
        = ∑ m ∈ Finset.range (n + 1), (aThakurTerm F n m).coeff N := by
      have := map_sum (Polynomial.lcoeff F N) (fun m => aThakurTerm F n m) (Finset.range (n + 1))
      simpa only [Polynomial.lcoeff_apply] using this
    rw [hsplit, Finset.sum_eq_single (mStar F n)]
    · -- the maximizing term
      have hmon : ((carlitzBracketPow F) ^ (mStar F n)).Monic := (carlitzBracketPow_monic F).pow _
      have hdegm : ((carlitzBracketPow F) ^ (mStar F n)).natDegree = N := by
        rw [Polynomial.natDegree_pow, carlitzBracketPow_natDegree, hN]; ring
      have h1 : ((carlitzBracketPow F) ^ (mStar F n)).coeff N = 1 := by
        rw [← hdegm]; exact hmon.coeff_natDegree
      rw [aThakurTerm, Polynomial.coeff_C_mul, h1, mul_one]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mStar_spec F n)
    · intro m hm hmne
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      rcases lt_or_gt_of_ne hmne with hlt | hgt
      · have hltN : ((carlitzBracketPow F) ^ m).natDegree < N := by
          rw [Polynomial.natDegree_pow, carlitzBracketPow_natDegree, hN]
          have hq2 : 0 < (Nat.card F - 1) * Nat.card F := by
            have hq := carlitz_card_ge_two F
            exact Nat.mul_pos (by omega) (by omega)
          have : m * ((Nat.card F - 1) * Nat.card F) < mStar F n * ((Nat.card F - 1) * Nat.card F) :=
            Nat.mul_lt_mul_of_pos_right hlt hq2
          calc m * ((Nat.card F - 1) * Nat.card F) < mStar F n * ((Nat.card F - 1) * Nat.card F) := this
            _ = (Nat.card F - 1) * Nat.card F * mStar F n := by ring
        rw [aThakurTerm, Polynomial.coeff_C_mul,
          Polynomial.coeff_eq_zero_of_natDegree_lt hltN, mul_zero]
      · have hc0 : ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) = 0 :=
          mStar_max F n m hgt hmn
        rw [aThakurTerm, hc0, mul_zero, Polynomial.C_0, zero_mul, Polynomial.coeff_zero]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by have := mStar_le F n; omega)) hmem
  rw [hA, neg_one_pow_eq_C F n,
    Polynomial.natDegree_C_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]
  exact hmain

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

private lemma intDegree_pow (x : RatFunc F) (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp [RatFunc.intDegree_one]
  | succ k ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero k hx) hx, ih]
      push_cast; ring

/-- `q * mStar n ≤ n` (the maximizing index of Carlitz's expansion is admissible). -/
lemma card_mul_mStar_le (n : ℕ) : Nat.card F * mStar F n ≤ n := by
  have hc : Nat.choose ((n - 1) - mStar F n * (Nat.card F - 1)) (mStar F n) ≠ 0 := by
    intro h
    exact mStar_spec F n (by rw [h, Nat.cast_zero])
  have h2 : ¬(((n - 1) - mStar F n * (Nat.card F - 1)) < mStar F n) := by
    intro hlt
    exact hc (Nat.choose_eq_zero_of_lt hlt)
  have h3 : mStar F n ≤ (n - 1) - mStar F n * (Nat.card F - 1) := le_of_not_gt h2
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  by_cases hcase : mStar F n * (Nat.card F - 1) ≤ n - 1
  · have h4 : mStar F n + mStar F n * (Nat.card F - 1) ≤ n - 1 :=
      Nat.add_le_of_le_sub (a := mStar F n) (b := mStar F n * (Nat.card F - 1))
        (c := n - 1) hcase h3
    have h4' : mStar F n * (Nat.card F - 1) + mStar F n ≤ n - 1 := by omega
    have h5 : Nat.card F * mStar F n
        = mStar F n * (Nat.card F - 1) + mStar F n := by
      have hq1' : Nat.card F = (Nat.card F - 1) + 1 := by omega
      calc Nat.card F * mStar F n = ((Nat.card F - 1) + 1) * mStar F n := by
            conv_lhs => rw [hq1']
        _ = (Nat.card F - 1) * mStar F n + mStar F n := by rw [Nat.add_mul, one_mul]
        _ = mStar F n * (Nat.card F - 1) + mStar F n := by rw [Nat.mul_comm]
    omega
  · have hN0 : (n - 1) - mStar F n * (Nat.card F - 1) = 0 :=
      Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hcase))
    rw [hN0] at h3
    have : mStar F n = 0 := by omega
    rw [this]
    omega

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **Closed form for Thakur's `jMin`**: `jMin F k = (q-1)·(k - q·mStar k)`. -/
theorem jMin_eq_mStar (k : ℕ+) :
    jMin F k = (Nat.card F - 1) * ((k : ℕ) - Nat.card F * mStar F (k : ℕ)) := by
  classical
  have hval := val_P_one F k
  have hcoe := P_one_eq_coe_P1rat F k
  have hP0 : P F 1 k ≠ 0 := by
    intro h
    have h1 : Valued.v (P F 1 k) = 0 := by rw [h, map_zero]
    rw [hval] at h1
    exact WithZero.exp_ne_zero h1
  have hpr0 : P1rat F (k : ℕ) ≠ 0 := by
    intro h
    have h2 : P F 1 k = 0 := by
      rw [hcoe]
      change toK F (P1rat F (k : ℕ)) = 0
      rw [h, map_zero]
    exact hP0 h2
  have hP1 : (P1rat F (k : ℕ)).intDegree = -(((k : ℕ) : ℤ) + (jMin F k : ℤ)) := by
    have h1 := v_toK F (P1rat F (k : ℕ)) hpr0
    change Valued.v (((P1rat F (k : ℕ) : RatFunc F)) : RatFunc.CompletionAtInfty F)
      = WithZero.exp ((P1rat F (k : ℕ)).intDegree) at h1
    rw [← hcoe, hval] at h1
    exact WithZero.exp_inj.mp h1.symm
  have hy0 : (algebraMap F[X] (RatFunc F) (carlitzOne F)) ≠ 0 := by
    intro h
    exact (carlitzOne_monic F).ne_zero (RatFunc.algebraMap_injective F (by simpa using h))
  have hA : (algebraMap F[X] (RatFunc F) (A F (k : ℕ))).intDegree
      = ((k : ℕ) : ℤ) * Nat.card F + (P1rat F (k : ℕ)).intDegree := by
    rw [A_RatFunc_eq F (k : ℕ)]
    rw [RatFunc.intDegree_mul (pow_ne_zero (k : ℕ) hy0) hpr0, intDegree_pow F _ hy0 (k : ℕ),
      RatFunc.intDegree_polynomial, carlitzOne_natDegree]
  have hdeg : ((A F (k : ℕ)).natDegree : ℤ)
      = ((k : ℕ) : ℤ) * Nat.card F + (P1rat F (k : ℕ)).intDegree := by
    rw [← RatFunc.intDegree_polynomial (p := A F (k : ℕ))]
    exact hA
  have hj : (jMin F k : ℤ)
      = ((k : ℕ) : ℤ) * Nat.card F - (k : ℕ) - (A F (k : ℕ)).natDegree := by
    rw [hdeg, hP1]; ring
  have hcast : ((jMin F k : ℕ) : ℤ)
      = (((Nat.card F - 1) * ((k : ℕ) - Nat.card F * mStar F (k : ℕ)) : ℕ) : ℤ) := by
    have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
    have hle := card_mul_mStar_le F (k : ℕ)
    rw [hj, natDegree_A F (k : ℕ) k.pos]
    push_cast [Nat.cast_sub hle, Nat.cast_sub hq1]
    ring
  exact_mod_cast hcast

end ZagierHoffmanPositiveChar
