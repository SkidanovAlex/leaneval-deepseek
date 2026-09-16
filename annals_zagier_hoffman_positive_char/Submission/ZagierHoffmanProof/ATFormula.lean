import Submission.ZagierHoffmanProof.ATPsi
import Submission.ZagierHoffmanProof.ATDrinfeld
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Lagrange
import Submission.Commons.Algebra.Polynomial.sum_inv_prod_sub_decEq
import Submission.Commons.Algebra.Polynomial.aeval_pow_card

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The explicit Anderson--Thakur formula for `Ψ_k`

`ATPsi.lean` defines the Anderson--Thakur polynomial `Ψ_k(a)` as the coefficient of `x ^ (q ^ k)` in
the Carlitz module action `C_a(x)`.  This file proves the **explicit formula** of the literature
(Anderson--Thakur; see also Dac §4.2)

```
Ψ_k(a) = ∑_{j ≤ k} a(θ ^ (q^j)) / (D_j * L_{k - j} ^ (q^j)),
```

where `D_j` are the Carlitz factorials, `L_i = ∏_{ℓ=1}^{i} (θ - θ ^ (q ^ ℓ))` the denominators of
the Carlitz logarithm, and `a(θ ^ (q^j))` is the evaluation of `a ∈ F[X]` at `θ ^ (q^j)`.

Two ingredients are used:

* the **partial-fraction identity** `∑_{j ≤ k} 1 / (D_j * L_{k-j} ^ (q^j)) = δ_{k,0}`
  (the `z ^ (#s - 1)`-coefficient of the Lagrange interpolation identity
  `∑_i ∏_{j ≠ i} (z - θ ^ (q^i)) / ∏_{j ≠ i}(θ^(q^i) - θ^(q^j)) = 1`);
* the polynomial identity `∏_{j ≠ i, j ≤ k} (θ ^ (q^i) - θ ^ (q^j)) = D_i * L_{k-i} ^ (q^i)`.

The closed form is then characterised by the same recursion as `Ψ_k`
(`Ψ_k(θa) = θ Ψ_k(a) + Ψ_{k-1}(a) ^ q`) plus the value on constants (given by the partial-fraction
identity), and the two agree by induction on `a`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]


/-! ### The product identity and the partial-fraction identity -/

lemma sub_pow_card_pow {S : Type*} [CommRing S] [CharP S (ringChar F)] (x y : S) (i : ℕ) :
    (x - y) ^ (Nat.card F ^ i) = x ^ (Nat.card F ^ i) - y ^ (Nat.card F ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ, pow_mul, ih, sub_pow_card F]
      simp only [← pow_mul]

lemma erase_range_eq (k i : ℕ) (hi : i ≤ k) :
    (Finset.range (k + 1)).erase i = Finset.range i ∪ Finset.Icc (i + 1) k := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
  omega

lemma disjoint_range_Icc (i k : ℕ) : Disjoint (Finset.range i) (Finset.Icc (i + 1) k) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  rw [Finset.mem_range] at hj
  rw [Finset.mem_Icc] at hj'
  omega

lemma prod_erase_range_X (k i : ℕ) (hi : i ≤ k) :
    ∏ j ∈ (Finset.range (k + 1)).erase i,
        (X ^ (Nat.card F ^ i) - X ^ (Nat.card F ^ j) : F[X])
      = carlitzFact F i * (carlitzL F (k - i)) ^ (Nat.card F ^ i) := by
  rw [erase_range_eq k i hi, Finset.prod_union (disjoint_range_Icc i k)]
  have h1 : ∏ j ∈ Finset.range i, (X ^ (Nat.card F ^ i) - X ^ (Nat.card F ^ j) : F[X])
      = carlitzFact F i := rfl
  have h2 : ∏ j ∈ Finset.Icc (i + 1) k,
        (X ^ (Nat.card F ^ i) - X ^ (Nat.card F ^ j) : F[X])
      = (carlitzL F (k - i)) ^ (Nat.card F ^ i) := by
    rw [show Finset.Icc (i + 1) k = Finset.Ico (i + 1) (k + 1) from by
      ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    rw [Finset.prod_Ico_eq_prod_range]
    rw [show k + 1 - (i + 1) = k - i from by omega]
    have hsub : ∀ t : ℕ, (X ^ (Nat.card F ^ i) - X ^ (Nat.card F ^ (i + 1 + t)) : F[X])
        = (X - X ^ (Nat.card F ^ (t + 1))) ^ (Nat.card F ^ i) := by
      intro t
      rw [sub_pow_card_pow F X (X ^ (Nat.card F ^ (t + 1))) i]
      congr 1
      rw [← pow_mul, ← pow_add]
      congr 1
      congr 1
      omega
    rw [Finset.prod_congr rfl (fun t _ => hsub t), Finset.prod_pow]
    congr 1
  rw [h1, h2]

lemma prod_erase_range_rat (k i : ℕ) (hi : i ≤ k) :
    ∏ j ∈ (Finset.range (k + 1)).erase i,
        ((RatFunc.X : RatFunc F) ^ (Nat.card F ^ i) - (RatFunc.X : RatFunc F) ^ (Nat.card F ^ j))
      = ((carlitzFact F i : F[X]) : RatFunc F)
          * (((carlitzL F (k - i) : F[X]) : RatFunc F)) ^ (Nat.card F ^ i) := by
  have h := congrArg (algebraMap F[X] (RatFunc F)) (prod_erase_range_X F k i hi)
  simp only [map_prod, map_sub, map_pow, map_mul, RatFunc.algebraMap_X] at h
  exact h

/-- The denominator `D_j * L_{k-j} ^ (q ^ j)` of the `j`-th summand of the closed form. -/
noncomputable def atDen (k j : ℕ) : RatFunc F :=
  ((carlitzFact F j : F[X]) : RatFunc F)
    * (((carlitzL F (k - j) : F[X]) : RatFunc F)) ^ (Nat.card F ^ j)

lemma partialFraction (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (atDen F k i)⁻¹ = if k = 0 then 1 else 0 := by
  have hvs : Set.InjOn (fun i => (RatFunc.X : RatFunc F) ^ (Nat.card F ^ i))
      (Finset.range (k + 1)) := by
    intro i _ j _ hij
    simp only [] at hij
    have key : ∀ i : ℕ, (RatFunc.X : RatFunc F) ^ (Nat.card F ^ i)
        = algebraMap F[X] (RatFunc F) (Polynomial.X ^ (Nat.card F ^ i)) := by
      intro i
      rw [map_pow, RatFunc.algebraMap_X]
    rw [key i, key j] at hij
    have hpoly : (Polynomial.X ^ (Nat.card F ^ i) : F[X]) = Polynomial.X ^ (Nat.card F ^ j) :=
      RatFunc.algebraMap_injective F hij
    have hdeg := congrArg Polynomial.natDegree hpoly
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hdeg
    exact Nat.pow_right_injective (by have := carlitz_card_ge_two F; omega) hdeg
  have h := Commons.Algebra.Polynomial.sum_inv_prod_sub_decEq (Finset.range (k + 1))
      (fun i => (RatFunc.X : RatFunc F) ^ (Nat.card F ^ i)) (by simp) hvs
  rw [Finset.card_range] at h
  have h' : (if k + 1 = 1 then (1 : RatFunc F) else 0) = (if k = 0 then 1 else 0) := by
    by_cases hk : k = 0
    · subst hk; norm_num
    · rw [if_neg (by omega : ¬ (k + 1 = 1)), if_neg hk]
  refine Eq.trans ?_ h'
  refine Eq.trans (Finset.sum_congr rfl (fun i hi => ?_)) h
  rw [Finset.mem_range] at hi
  refine congrArg Inv.inv ?_
  rw [atDen, prod_erase_range_rat F k i (by omega)]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The **closed form** of the Anderson–Thakur polynomials:
`Ψ_k(a) = ∑_{j ≤ k} a(θ ^ (q^j)) / (D_j * L_{k-j} ^ (q^j))`. -/
noncomputable def atPsiClosed (k : ℕ) (a : F[X]) : RatFunc F :=
  ∑ j ∈ Finset.range (k + 1),
    (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ j)) a) * (atDen F k j)⁻¹

lemma atPsiClosed_add (k : ℕ) (a b : F[X]) :
    atPsiClosed F k (a + b) = atPsiClosed F k a + atPsiClosed F k b := by
  rw [atPsiClosed, atPsiClosed, atPsiClosed, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_add, add_mul]

lemma atPsiClosed_C_mul (k : ℕ) (c : F) (a : F[X]) :
    atPsiClosed F k (Polynomial.C c * a)
      = algebraMap F (RatFunc F) c * atPsiClosed F k a := by
  rw [atPsiClosed, atPsiClosed, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, Polynomial.aeval_C, mul_assoc]

lemma atPsiClosed_sum (k : ℕ) {ι : Type*} (s : Finset ι) (f : ι → F[X]) :
    atPsiClosed F k (∑ i ∈ s, f i) = ∑ i ∈ s, atPsiClosed F k (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [atPsiClosed]
  | cons i s hi ih => rw [Finset.sum_cons, atPsiClosed_add, Finset.sum_cons, ih]

lemma atPsiClosed_one (k : ℕ) : atPsiClosed F k (1 : F[X]) = if k = 0 then 1 else 0 := by
  rw [atPsiClosed]
  simp only [map_one, one_mul]
  exact partialFraction F k

lemma atPsi_one (k : ℕ) : atPsi F k (1 : F[X]) = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    rw [atPsi_zero_eq]
    simp
  · rw [if_neg (by omega)]
    exact atPsi_eq_zero_of_lt_degree F k 1 (by simpa using h)

lemma aeval_X_mul (x : RatFunc F) (a : F[X]) :
    Polynomial.aeval x (Polynomial.X * a) = x * Polynomial.aeval x a := by
  rw [map_mul, Polynomial.aeval_X]

lemma carlitzTheta_pow_sub_ne_zero (m : ℕ) (hm : m ≠ 1) :
    (carlitzTheta F) ^ m - carlitzTheta F ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hm ((carlitzTheta_pow_eq_iff F).mp h)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `D_i ^ q * L_{k-(i+1)} ^ (q ^ (i+1))`: the denominator produced when the `q`-th power of the
`(k-1)`-st closed form is expanded. -/
noncomputable def atDenStep (k i : ℕ) : RatFunc F :=
  (((carlitzFact F i : F[X]) : RatFunc F)) ^ (Nat.card F)
    * (((carlitzL F (k - (i + 1)) : F[X]) : RatFunc F)) ^ (Nat.card F ^ (i + 1))

lemma atDen_succ_factor (k i : ℕ) :
    atDen F k (i + 1)
      = atDenStep F k i * ((carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F) := by
  simp only [atDen, atDenStep, carlitzFact_succ, carlitzBracket, carlitz_coe_mul,
    carlitz_coe_pow, carlitz_coe_sub, carlitz_coe_X]
  ring

lemma atDen_hstep (k i : ℕ) :
    ((carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F) * (atDen F k (i + 1))⁻¹
      = (atDenStep F k i)⁻¹ := by
  have hθ : (carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F ≠ 0 := by
    have h2 := carlitz_card_ge_two F
    refine carlitzTheta_pow_sub_ne_zero F _ (fun h => ?_)
    have h1 : Nat.card F ^ 1 ≤ Nat.card F ^ (i + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h1
    omega
  rw [atDen_succ_factor, mul_inv]
  rw [show ((carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F)
        * (((atDenStep F k i)⁻¹)
            * (((carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F)⁻¹))
      = (atDenStep F k i)⁻¹
        * (((carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F)
            * (((carlitzTheta F) ^ (Nat.card F ^ (i + 1)) - carlitzTheta F)⁻¹)) from by ring]
  rw [mul_inv_cancel₀ hθ, mul_one]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

lemma atPsiClosed_X_mul_zero (a : F[X]) :
    atPsiClosed F 0 (Polynomial.X * a) = carlitzTheta F * atPsiClosed F 0 a := by
  simp only [atPsiClosed, Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one,
    Nat.sub_zero, atDen, carlitzFact_zero, carlitzL_zero, inv_one, mul_one,
    aeval_X_mul, mul_assoc]

lemma atPsiClosed_X_mul (k : ℕ) (a : F[X]) :
    atPsiClosed F k (Polynomial.X * a)
      = carlitzTheta F * atPsiClosed F k a
        + (if k = 0 then 0 else (atPsiClosed F (k - 1) a) ^ (Nat.card F)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [if_pos rfl, add_zero]
    exact atPsiClosed_X_mul_zero F a
  · rw [if_neg (by omega)]
    have hA : atPsiClosed F k (Polynomial.X * a) - carlitzTheta F * atPsiClosed F k a
        = ∑ i ∈ Finset.range k,
            (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ (i + 1))) a)
              * (atDenStep F k i)⁻¹ := by
      rw [atPsiClosed, atPsiClosed, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ']
      have h0 : (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ 0)) (Polynomial.X * a)
            * (atDen F k 0)⁻¹
          - carlitzTheta F
            * (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ 0)) a * (atDen F k 0)⁻¹))
          = 0 := by
        rw [pow_zero, pow_one, aeval_X_mul]
        ring
      rw [h0, add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [aeval_X_mul]
      calc (carlitzTheta F ^ Nat.card F ^ (i + 1) * Polynomial.aeval (carlitzTheta F ^ Nat.card F ^ (i + 1)) a
              * (atDen F k (i + 1))⁻¹
            - carlitzTheta F
              * (Polynomial.aeval (carlitzTheta F ^ Nat.card F ^ (i + 1)) a
                  * (atDen F k (i + 1))⁻¹))
          = Polynomial.aeval (carlitzTheta F ^ Nat.card F ^ (i + 1)) a
              * ((carlitzTheta F ^ Nat.card F ^ (i + 1) - carlitzTheta F)
                  * (atDen F k (i + 1))⁻¹) := by ring
        _ = Polynomial.aeval (carlitzTheta F ^ Nat.card F ^ (i + 1)) a
              * (atDenStep F k i)⁻¹ := by rw [atDen_hstep]
    have hB : (atPsiClosed F (k - 1) a) ^ (Nat.card F)
        = ∑ i ∈ Finset.range k,
            (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ (i + 1))) a)
              * (atDenStep F k i)⁻¹ := by
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
      rw [atPsiClosed, hk1, carlitz_sum_pow_card]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow, inv_pow]
      congr 1
      · rw [Commons.Algebra.Polynomial.aeval_pow_card,
          show ((carlitzTheta F) ^ (Nat.card F ^ j)) ^ (Nat.card F)
            = (carlitzTheta F) ^ (Nat.card F ^ (j + 1)) from by rw [← pow_mul, ← pow_succ]]
      · congr 1
        rw [atDen, atDenStep, mul_pow, ← pow_mul, ← pow_succ,
          show (k - 1) - j = k - (j + 1) from by omega]
    rw [hB]
    exact (sub_eq_iff_eq_add.mp hA).trans (add_comm _ _)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

lemma atPsi_X_pow_eq_closed (i : ℕ) :
    ∀ k : ℕ, atPsi F k (Polynomial.X ^ i) = atPsiClosed F k (Polynomial.X ^ i) := by
  induction i with
  | zero => intro k; rw [pow_zero, atPsi_one, atPsiClosed_one]
  | succ i ih =>
      intro k
      rw [pow_succ', atPsi_X_mul, atPsiClosed_X_mul, ih k]
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk, ih (k - 1)]

/-- ★★★ **The explicit (Anderson–Thakur) formula for `Ψ_k`**:
`Ψ_k(a) = ∑_{j ≤ k} a(θ ^ (q^j)) / (D_j * L_{k-j} ^ (q^j))`. -/
theorem atPsi_eq_atPsiClosed (k : ℕ) (a : F[X]) : atPsi F k a = atPsiClosed F k a := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow a]
  conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow a]
  rw [atPsi_sum, atPsiClosed_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [atPsi_C_mul, atPsiClosed_C_mul, atPsi_X_pow_eq_closed]

end ZagierHoffmanPositiveChar

