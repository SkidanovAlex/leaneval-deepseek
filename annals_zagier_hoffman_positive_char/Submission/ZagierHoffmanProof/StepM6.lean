import Submission.ZagierHoffmanProof.StepM5
import Submission.ZagierHoffmanProof.ThakurDeg3

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M6: the `q = 2` exponent recursion for the power sums

Thakur's recursion `s_{d+1}(k) = s_d(s_1(k)) + s_1(k)` (`s_1(k) = k + jMin(k)`) is
formalised here for the case `q = 2`, where `s_1(k) = T k = k + 2^{v_2 k}` and the
admissible shifts are exactly the `j ≥ 1` with `j &&& (k−1) = 0`.

This module sets up the map `T`, the exponent `sExp d k = ∑_{i=1}^{d} T^i(k)`, and computes
the valuation of a single summand of the truncated level recursion of Step M5.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Tmap

/-- The "round up" map `T k = k + 2 ^ v_2(k)` of the `q = 2` recursion
(`T k = s_1(k) = k + jMin(k)` when `Nat.card F = 2`). -/
def Tmap (k : ℕ) : ℕ := k + 2 ^ k.factorization 2

lemma Tmap_def (k : ℕ) : Tmap k = k + 2 ^ k.factorization 2 := rfl

lemma Tmap_pos (k : ℕ) : 0 < Tmap k := by
  rw [Tmap_def]
  have := pow_pos (by norm_num : (0 : ℕ) < 2) (k.factorization 2)
  omega

lemma Tmap_gt {k : ℕ} (hk : k ≠ 0) : k < Tmap k := by
  rw [Tmap_def]
  have : 0 < 2 ^ k.factorization 2 := pow_pos (by norm_num) _
  omega

lemma Tmap_mul_two_pow (a x : ℕ) (hx : x ≠ 0) :
    Tmap (2 ^ a * x) = 2 ^ a * Tmap x := by
  have h1 : (2 ^ a * x).factorization 2 = a + x.factorization 2 := by
    rw [Nat.factorization_mul (pow_ne_zero a (by norm_num)) hx, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  rw [Tmap_def, Tmap_def, h1, pow_add]
  ring

end Tmap

section SExp

/-- The exponent of `P_d(k)` at `q = 2`: `sExp d k = ∑_{i=1}^{d} T^i(k)`. -/
noncomputable def sExp (d k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, ((Nat.iterate Tmap (i + 1) k : ℕ) : ℤ)

lemma sExp_zero (k : ℕ) : sExp 0 k = 0 := by
  simp [sExp]

lemma sExp_succ (d k : ℕ) : sExp (d + 1) k = (Tmap k : ℤ) + sExp d (Tmap k) := by
  unfold sExp
  rw [Finset.sum_range_succ']
  have h2 : ∀ i : ℕ, Tmap (Tmap^[i] k) = Tmap^[i] (Tmap k) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have h : ∀ i : ℕ, Tmap^[i + 1 + 1] k = Tmap^[i + 1] (Tmap k) := by
    intro i
    rw [show i + 1 + 1 = (i + 1) + 1 from rfl, Function.iterate_succ_apply']
    exact h2 (i + 1)
  have hsum : (∑ i ∈ Finset.range d, ((Tmap^[i + 1 + 1]) k : ℤ))
      = ∑ i ∈ Finset.range d, ((Tmap^[i + 1]) (Tmap k) : ℤ) :=
    Finset.sum_congr rfl fun i _ => by rw [h i]
  rw [hsum, Function.iterate_one]
  ring

lemma sExp_nonneg (d k : ℕ) : 0 ≤ sExp d k := by
  unfold sExp
  refine Finset.sum_nonneg fun i _ => ?_
  exact_mod_cast Nat.zero_le _

end SExp

section TermVal

/-- The valuation of a single summand of the truncated level recursion (Step M5). -/
lemma v_P_expansion_term (d : ℕ) (k : ℕ+) (j : ℕ) (S : ℤ)
    (hP : Valued.v (P F d ⟨(k : ℕ) + j, Nat.add_pos_left k.pos j⟩) = exp (-S))
    (ha : binF F k j * psumF F j ≠ 0) :
    Valued.v (cst F (binF F k j * psumF F j) *
        (((((Polynomial.X : F[X]) : RatFunc F)) : RatFunc.CompletionAtInfty F) ^
          ((k : ℕ) + j))⁻¹ *
        P F d ⟨(k : ℕ) + j, Nat.add_pos_left k.pos j⟩)
      = exp (-(((k : ℤ) + j) + S)) := by
  rw [Valuation.map_mul, Valuation.map_mul, v_cst_eq_one F _ ha, one_mul,
    ← coe_poly_pow F Polynomial.X ((k : ℕ) + j), v_coe_X_pow_inv F ((k : ℕ) + j), hP,
    ← WithZero.exp_add]
  congr 1
  push_cast
  ring

end TermVal

end ZagierHoffmanPositiveChar
