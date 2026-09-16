import Submission.ZagierHoffmanProof.StepK27

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K28: the degree of the two-variable tower polynomial

`hh 0 2 k` (complete homogeneous of degree `k` in `(X, X^q)`) has the closed form
`hh 0 2 k = Σ_{i=0}^{k} X^{(q−1)·i + k}` and degree `q·k` with top coefficient `1`:

  hh_two_form (k) : hh 0 2 k = Σ_{i<k+1} X^{(Nat.card F − 1)·i + k}
      [def-unfold (first calc line is `rfl` with the exponent written `(Nat.card F)^1`
       — `X^(q^1)` is NOT defeq `X^q`, so keep the `^1` and `rw [pow_one]` per-term);
       per-term: hh 0 1 (k−i) = X^{k−i} (hh_one), (X^q)^i = X^{q·i} (pow_mul .symm),
       pow_add, exponent congruence (q−1)·i + (i + (k−i)) via hqi ((q−1)·i + i = q·i
       by ring after the (q−1)+1 = q rewrite — NOT `rw [← hpred]`+ring, which fails)]
  hh_two_deg (k) (1 ≤ k) : (hh 0 2 k).natDegree = (Nat.card F)·k
      [le_antisymm: ≤ via natDegree_le_iff_coeff_eq_zero with per-term degree bound
       (nlinarith with hq1 : 1 ≤ q−1 in scope); ≥ via by_contra + top coefficient 1
       (sum_eq_single k; lt_of_not_ge not omega — q·k is a nonlinear atom)]
  hh_two_topcoeff (k) (1 ≤ k) : (hh 0 2 k).coeff ((Nat.card F)·k) = 1

These unblock the inner-collapse gate `Z.natDegree ≠ 0` for `Z := D1 (m+1)(cons 0 u)`
(its top term `hh 0 2 (m+1)` with coefficient 1 dominates the `m' ≤ m` terms).  All
lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- the two-variable complete homogeneous polynomial: `hh 0 2 k = Σ_{i=0}^{k} X^{(q−1)·i + k}`. -/
lemma hh_two_form (k : ℕ) :
    hh F 0 2 k = ∑ i ∈ Finset.range (k + 1), X ^ ((Nat.card F - 1) * i + k) := by
  classical
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hh1 (j : ℕ) : hh F 0 1 j = X ^ j := by
    rw [hh_one F 0 j]
    simp
  calc
    hh F 0 2 k = ∑ i ∈ Finset.range (k + 1), (X ^ ((Nat.card F) ^ 1)) ^ i * hh F 0 1 (k - i) := by
          rfl
    _ = ∑ i ∈ Finset.range (k + 1), X ^ ((Nat.card F - 1) * i + k) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < k + 1 := Finset.mem_range.mp hi
          have hik : i ≤ k := by omega
          have hp : ((X : F[X]) ^ (Nat.card F)) ^ i = (X : F[X]) ^ (Nat.card F * i) := by
            exact (pow_mul (X : F[X]) (Nat.card F) i).symm
          have hk' : i + (k - i) = k := by omega
          have hqi : (Nat.card F - 1) * i + i = Nat.card F * i := by
            have hpred : Nat.card F - 1 + 1 = Nat.card F := by omega
            calc
              (Nat.card F - 1) * i + i = ((Nat.card F - 1) + 1) * i := by ring
              _ = Nat.card F * i := by rw [hpred]
          calc
            (X ^ ((Nat.card F) ^ 1)) ^ i * hh F 0 1 (k - i)
                = (X ^ (Nat.card F)) ^ i * hh F 0 1 (k - i) := by
                  congr 1
                  rw [pow_one]
            _ = (X ^ (Nat.card F)) ^ i * X ^ (k - i) := by rw [hh1 (k - i)]
            _ = X ^ (Nat.card F * i) * X ^ (k - i) := by rw [hp]
            _ = X ^ ((Nat.card F) * i + (k - i)) := by rw [pow_add]
            _ = X ^ ((Nat.card F - 1) * i + k) := by
                  congr 1
                  calc
                    (Nat.card F) * i + (k - i) = ((Nat.card F - 1) * i + i) + (k - i) := by rw [← hqi]
                    _ = (Nat.card F - 1) * i + (i + (k - i)) := by rw [add_assoc]
                    _ = (Nat.card F - 1) * i + k := by rw [hk']


/-- the two-variable tower polynomial has degree `q·k`: `hh 0 2 k` is a sum of
monomials `X^{k+(q−1)·i}` (i = 0..k) with unique top monomial `X^{qk}` at `i = k`. -/
lemma hh_two_deg (k : ℕ) (hk : 1 ≤ k) : (hh F 0 2 k).natDegree = (Nat.card F) * k := by
  classical
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hq1 : 1 ≤ Nat.card F - 1 := by omega
  rw [hh_two_form F k]
  let e : ℕ → ℕ := fun i => (Nat.card F - 1) * i + k
  apply le_antisymm
  · -- natDegree ≤ q·k: coefficients above q·k vanish
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    -- coeff N of the sum
    have hcoeff : (∑ i ∈ Finset.range (k + 1), X ^ e i : F[X]).coeff N =
        ∑ i ∈ Finset.range (k + 1), (X ^ e i : F[X]).coeff N := by simp
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < k + 1 := Finset.mem_range.mp hi
    have hb : e i < N := by
      dsimp [e]
      have hle : (Nat.card F - 1) * i + k ≤ (Nat.card F - 1) * k + k := by
        have hik : i ≤ k := by omega
        nlinarith
      have htop : (Nat.card F - 1) * k + k = Nat.card F * k := by
        have hpred : Nat.card F - 1 + 1 = Nat.card F := by omega
        calc
          (Nat.card F - 1) * k + k = ((Nat.card F - 1) + 1) * k := by ring
          _ = Nat.card F * k := by rw [hpred]
      omega
    rw [Polynomial.coeff_X_pow (e i) N, if_neg (by omega : N ≠ e i)]
  · -- natDegree ≥ q·k: the coefficient of X^{qk} is 1
    by_contra hlt
    have hlt' : (∑ i ∈ Finset.range (k + 1), X ^ e i : F[X]).natDegree < Nat.card F * k := lt_of_not_ge hlt
    have hz : (∑ i ∈ Finset.range (k + 1), X ^ e i : F[X]).coeff (Nat.card F * k) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
    have hc : (∑ i ∈ Finset.range (k + 1), X ^ e i : F[X]).coeff (Nat.card F * k) = 1 := by
      have hcoeff : (∑ i ∈ Finset.range (k + 1), X ^ e i : F[X]).coeff (Nat.card F * k) =
          ∑ i ∈ Finset.range (k + 1), (X ^ e i : F[X]).coeff (Nat.card F * k) := by simp
      rw [hcoeff]
      -- only i = k contributes 1
      have htop : (Nat.card F - 1) * k + k = Nat.card F * k := by
        have hpred : Nat.card F - 1 + 1 = Nat.card F := by omega
        calc
          (Nat.card F - 1) * k + k = ((Nat.card F - 1) + 1) * k := by ring
          _ = Nat.card F * k := by rw [hpred]
      rw [Finset.sum_eq_single k]
      · -- the k-term: X^{e k}.coeff (qk) = 1 since e k = qk
        dsimp [e]
        rw [htop]
        rw [Polynomial.coeff_X_pow (Nat.card F * k) (Nat.card F * k), if_pos rfl]
      · intro b hb hbk
        -- b ≠ k: e b ≠ qk, term zero
        have hb' : b < k + 1 := Finset.mem_range.mp hb
        have hneq : e b ≠ Nat.card F * k := by
          intro hc0
          have hb_le : b < k := by omega
          dsimp [e] at hc0
          have hlt0 : (Nat.card F - 1) * b + k < (Nat.card F - 1) * k + k := by
            nlinarith
          have htop0 : (Nat.card F - 1) * k + k = Nat.card F * k := by
            have hpred : Nat.card F - 1 + 1 = Nat.card F := by omega
            calc
              (Nat.card F - 1) * k + k = ((Nat.card F - 1) + 1) * k := by ring
              _ = Nat.card F * k := by rw [hpred]
          omega
        rw [Polynomial.coeff_X_pow (e b) (Nat.card F * k), if_neg (by intro h; exact hneq h.symm)]
      · intro hknotin
        exact False.elim (hknotin (by simp))
    rw [hc] at hz
    exact one_ne_zero hz



/-- the top coefficient of the two-variable tower is `1`: `(hh 0 2 k).coeff (q·k) = 1`. -/
lemma hh_two_topcoeff (k : ℕ) (hk : 1 ≤ k) :
    (hh F 0 2 k).coeff ((Nat.card F) * k) = 1 := by
  classical
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hq1 : 1 ≤ Nat.card F - 1 := by omega
  rw [hh_two_form F k]
  let e : ℕ → ℕ := fun i => (Nat.card F - 1) * i + k
  have hcoeff : (∑ i ∈ Finset.range (k + 1), X ^ e i : F[X]).coeff (Nat.card F * k) =
      ∑ i ∈ Finset.range (k + 1), (X ^ e i : F[X]).coeff (Nat.card F * k) := by simp
  rw [hcoeff]
  have htop : (Nat.card F - 1) * k + k = Nat.card F * k := by
    have hpred : Nat.card F - 1 + 1 = Nat.card F := by omega
    calc
      (Nat.card F - 1) * k + k = ((Nat.card F - 1) + 1) * k := by ring
      _ = Nat.card F * k := by rw [hpred]
  rw [Finset.sum_eq_single k]
  · dsimp [e]
    rw [htop]
    rw [Polynomial.coeff_X_pow (Nat.card F * k) (Nat.card F * k), if_pos rfl]
  · intro b hb hbk
    have hb' : b < k + 1 := Finset.mem_range.mp hb
    have hneq : e b ≠ Nat.card F * k := by
      intro hc0
      have hb_le : b < k := by omega
      dsimp [e] at hc0
      have hlt0 : (Nat.card F - 1) * b + k < (Nat.card F - 1) * k + k := by
        nlinarith
      have htop0 : (Nat.card F - 1) * k + k = Nat.card F * k := by
        have hpred : Nat.card F - 1 + 1 = Nat.card F := by omega
        calc
          (Nat.card F - 1) * k + k = ((Nat.card F - 1) + 1) * k := by ring
          _ = Nat.card F * k := by rw [hpred]
      omega
    rw [Polynomial.coeff_X_pow (e b) (Nat.card F * k), if_neg (by intro h; exact hneq h.symm)]
  · intro hknotin
    exact False.elim (hknotin (by simp))


end ZagierHoffmanPositiveChar
