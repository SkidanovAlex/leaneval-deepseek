/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ATBridge
import Submission.ZagierHoffmanProof.D1
import Submission.Commons.Algebra.Polynomial.comp_injective_of_natDegree_pos
import Submission.Commons.Algebra.BigOperators.sum_Icc_filter_dvd

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# Thakur's polynomial form of the level-one shuffle relation

Carlitz's expansion `A_n = (-1)^n ∑_m (-1)^m C(n-1-m(q-1),m) [1]^{m(q-1)}`
(`AExpansion.A_thakur_formula`) exhibits `A_n` as the value at `T = [1]^(q-1)` of the *Thakur
polynomial*
```
b_n(T) = (-1)^n ∑_m (-1)^m C(n-1-m(q-1),m) T^m .
```
Since `T ↦ [1]^(q-1)` is an injective ring hom `F[T] → F[X]` (the image is nonconstant), the
level-one shuffle identity `D1.thakurP1` transfers to `F[T]`:

  `b_a · b_b = b_(a+b) + Σ_{k=1}^{⌊(a+b-1)/(q-1)⌋} Δ^{(q-1)k} · T^k · b_(a+b-(q-1)k)`

with Chen's coefficients `Δ^i = ChenDeltaZ` — Thakur's form of the relation (Thakur, IMRN 2010,
Theorem 5.1 (2) at depth one).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Thakur's polynomial `b_n(T) = (-1)^n ∑_m (-1)^m C(n-1-m(q-1),m) T^m`. -/
noncomputable def thakurPoly (n : ℕ) : Polynomial F :=
  (-1 : Polynomial F) ^ n *
    ∑ m ∈ Finset.range (n + 1),
      (-1 : Polynomial F) ^ m *
        Polynomial.C ((((n - 1) - m * (Nat.card F - 1)).choose m : ℕ) : F) *
        Polynomial.X ^ m

/-- The specialisation `T ↦ [1]^(q-1)`: an injective ring hom `F[T] → F[X]`. -/
noncomputable def Phi : F[X] →+* F[X] :=
  Polynomial.eval₂RingHom Polynomial.C ((carlitzOne F) ^ (Nat.card F - 1))

lemma Phi_apply (p : F[X]) :
    Phi F p = Polynomial.eval₂ Polynomial.C ((carlitzOne F) ^ (Nat.card F - 1)) p := by
  simp only [Phi, Polynomial.coe_eval₂RingHom]

lemma Phi_comp (p : F[X]) : Phi F p = p.comp ((carlitzOne F) ^ (Nat.card F - 1)) := by
  rw [Phi_apply]
  rfl

@[simp] lemma Phi_X : Phi F Polynomial.X = (carlitzOne F) ^ (Nat.card F - 1) := by
  rw [Phi_apply, Polynomial.eval₂_X]

@[simp] lemma Phi_C (c : F) : Phi F (Polynomial.C c) = Polynomial.C c := by
  rw [Phi_apply, Polynomial.eval₂_C]

lemma carlitzOne_pow_ne_zero : (carlitzOne F) ^ (Nat.card F - 1) ≠ 0 :=
  pow_ne_zero _ (carlitzOne_ne_zero F)

lemma natDegree_carlitzOne_pow : ((carlitzOne F) ^ (Nat.card F - 1)).natDegree =
    Nat.card F * (Nat.card F - 1) := by
  rw [Polynomial.natDegree_pow, carlitzOne_natDegree, Nat.mul_comm]

lemma Phi_injective : Function.Injective (Phi F) := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hpos : 0 < ((carlitzOne F) ^ (Nat.card F - 1)).natDegree := by
    rw [natDegree_carlitzOne_pow]
    exact Nat.mul_pos (by omega) (by omega)
  rw [show Phi F = (fun p : F[X] => p.comp ((carlitzOne F) ^ (Nat.card F - 1))) from
    funext (Phi_comp F)]
  exact Commons.Algebra.Polynomial.comp_injective_of_natDegree_pos hpos

/-- The Thakur polynomial specialises to Carlitz's power-sum polynomial: `b_n([1]^(q-1)) = A_n`. -/
lemma Phi_thakurPoly (n : ℕ) (hn : 1 ≤ n) : Phi F (thakurPoly F n) = A F n := by
  rw [A_thakur_formula F n hn, thakurB, thakurPoly]
  simp only [map_mul, map_pow, map_sum, Phi_C, Phi_X, map_neg, map_one]

/-- Reindexing the level-one Chen sum over the multiples of `q - 1`. -/
lemma delta_sum_reindex (a b : ℕ) :
    (∑ i ∈ Finset.Icc 1 (a + b - 1),
        Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))
      = ∑ k ∈ Finset.Icc 1 ((a + b - 1) / (Nat.card F - 1)),
          Polynomial.C (ChenDeltaZ F a b ((Nat.card F - 1) * k) : F) *
            (carlitzOne F) ^ ((Nat.card F - 1) * k) *
            A F (a + b - (Nat.card F - 1) * k) := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hd : 1 ≤ Nat.card F - 1 := by omega
  have hdpos : 0 < Nat.card F - 1 := by omega
  have h1 : (∑ i ∈ (Finset.Icc 1 (a + b - 1)).filter (fun i => Nat.card F - 1 ∣ i),
        Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))
      = ∑ i ∈ Finset.Icc 1 (a + b - 1),
        Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i) :=
    Finset.sum_filter_of_ne (fun x _ hne => by
      by_contra hndvd
      exact hne (by rw [ChenDeltaZ, if_neg hndvd]; simp))
  rw [← h1, Commons.Algebra.BigOperators.sum_Icc_filter_dvd (Nat.card F - 1) (a + b - 1)
    (fun i => Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))]


/-- ★★★ Thakur's polynomial form of the depth-one shuffle relation: for `a, b ≥ 1`,
`b_a · b_b = b_(a+b) + Σ_{k ≥ 1} Δ^{(q-1)k} T^k b_(a+b-(q-1)k)` in `F[T]`. -/
theorem thakurPoly_mul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    thakurPoly F a * thakurPoly F b = thakurPoly F (a + b) +
      ∑ k ∈ Finset.Icc 1 ((a + b - 1) / (Nat.card F - 1)),
        Polynomial.C (ChenDeltaZ F a b ((Nat.card F - 1) * k) : F) *
          Polynomial.X ^ k * thakurPoly F (a + b - (Nat.card F - 1) * k) := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hdpos : 0 < Nat.card F - 1 := by omega
  refine Phi_injective F ?_
  rw [map_mul, map_add, map_sum, Phi_thakurPoly F a ha, Phi_thakurPoly F b hb,
    Phi_thakurPoly F (a + b) (by omega)]
  have hsummand : (∑ k ∈ Finset.Icc 1 ((a + b - 1) / (Nat.card F - 1)),
        Phi F (Polynomial.C (ChenDeltaZ F a b ((Nat.card F - 1) * k) : F) *
          Polynomial.X ^ k * thakurPoly F (a + b - (Nat.card F - 1) * k)))
      = ∑ k ∈ Finset.Icc 1 ((a + b - 1) / (Nat.card F - 1)),
          Polynomial.C (ChenDeltaZ F a b ((Nat.card F - 1) * k) : F) *
            (carlitzOne F) ^ ((Nat.card F - 1) * k) *
            A F (a + b - (Nat.card F - 1) * k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : (Nat.card F - 1) * k ≤ a + b - 1 := by
      have h := hk.2
      rw [Nat.le_div_iff_mul_le hdpos] at h
      rwa [Nat.mul_comm] at h
    rw [map_mul, map_mul, Phi_C, map_pow, Phi_X, ← pow_mul,
      Phi_thakurPoly F (a + b - (Nat.card F - 1) * k) (by omega)]
  rw [hsummand, ← delta_sum_reindex F a b, ← thakurP1 F a b ha hb]

@[simp] lemma thakurPoly_zero : thakurPoly F 0 = 1 := by
  rw [thakurPoly, Finset.range_one, Finset.sum_singleton]
  norm_num

/-- The easy range: `b_n = (-1)^n` for `1 ≤ n ≤ q`. -/
lemma thakurPoly_eq_neg_one_pow (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ≤ Nat.card F) :
    thakurPoly F n = (-1 : Polynomial F) ^ n := by
  refine Phi_injective F ?_
  rw [Phi_thakurPoly F n hn1, A_eq_neg_one_pow F n hn1 hnq, map_pow, map_neg, map_one]

lemma thakurPoly_one : thakurPoly F 1 = -1 := by
  simpa using thakurPoly_eq_neg_one_pow F 1 le_rfl (by have := card_ge_two F; omega)

/-- The Thakur–Pascal recursion in `F[T]`: `b_n + b_(n-1) = T·b_(n-q)` for `n ≥ q+1`. -/
lemma thakurPoly_rec (n : ℕ) (hn : Nat.card F + 1 ≤ n) :
    thakurPoly F n + thakurPoly F (n - 1) =
      Polynomial.X * thakurPoly F (n - Nat.card F) := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hn1 : 1 ≤ n := by omega
  have hn2 : 1 ≤ n - 1 := by omega
  have hn3 : 1 ≤ n - Nat.card F := by omega
  refine Phi_injective F ?_
  rw [map_add, map_mul, Phi_X, Phi_thakurPoly F n hn1,
    Phi_thakurPoly F (n - 1) hn2, Phi_thakurPoly F (n - Nat.card F) hn3]
  exact A_recursion F n (by omega)

end ZagierHoffmanPositiveChar
