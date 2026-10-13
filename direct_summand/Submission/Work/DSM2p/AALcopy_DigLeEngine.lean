-- Redirected copy of `Submission.Work.DSM2p.DigLeEngine` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_DigLeDefs
import Submission.Work.DSM2p.AALcopy_untilt_add_le

/-!
# The Gauss-norm engine: `DigLe` is subadditive and submultiplicative

`DigLe v z B` (every tilt digit of `z` has `v`-value at most `B`) satisfies

* `DigLe.add` : `DigLe v w B → DigLe v u C → B ≤ 1 → C ≤ 1 → DigLe v (w + u) (max B C)`,
* `DigLe.mul` : `DigLe v w B → DigLe v u C → B ≤ 1 → C ≤ 1 → DigLe v (w * u) (B * C)`.

Both are consequences of the *integrality* of the Witt addition and multiplication polynomials,
proved in `WittPolyWt.lean`: `(w + u).coeff n` and `(w * u).coeff n` are integer polynomials in the
coordinates of `w` and `u`, and every monomial of the `n`-th such polynomial has "weight" at
least `p ^ n` (the weight of the coordinate `j` being `p ^ j`), respectively row-weight at least
`p ^ n`.  Evaluating and using subadditivity/multiplicativity of `nv` gives the bound.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.DSM2p

universe u v w

open WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]

section Basic

variable {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}

theorem nv_prod {ι : Type*} (s : Finset ι) (f : ι → PreTilt R p) :
    nv v (∏ i ∈ s, f i) = ∏ i ∈ s, nv v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, nv_mul, ih]

theorem nv_sum_le {ι : Type*}
    (hadd : ∀ a b : PreTilt R p, nv v (a + b) ≤ max (nv v a) (nv v b))
    (s : Finset ι) (f : ι → PreTilt R p) {M : Γ₀}
    (h : ∀ i ∈ s, nv v (f i) ≤ M) : nv v (∑ i ∈ s, f i) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_le : (0 : Γ₀) ≤ M)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (hadd _ _) (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

end Basic

section ProdBounds

variable {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

/-- The product `∏ y, β_{y.1}^{m y · p^{y.2}}` is bounded by `γ^{weight}` when `β ≤ γ ≤ 1`. -/
theorem prod_beta_le_pow {k : ℕ} {β : Fin k → Γ₀} {γ : Γ₀} (hβ : ∀ i, β i ≤ γ) (hγ : γ ≤ 1)
    (m : Fin k × ℕ →₀ ℕ) {N : ℕ}
    (hN : N ≤ monWt (fun y : Fin k × ℕ => p ^ y.2) m) :
    ∏ y ∈ m.support, β y.1 ^ (m y * p ^ y.2) ≤ γ ^ N := by
  classical
  have h1 : ∏ y ∈ m.support, β y.1 ^ (m y * p ^ y.2)
      ≤ ∏ y ∈ m.support, γ ^ (m y * p ^ y.2) :=
    Finset.prod_le_prod fun y _ => pow_le_pow_left' (hβ y.1) _
  have h2 : ∏ y ∈ m.support, γ ^ (m y * p ^ y.2)
      = γ ^ monWt (fun y : Fin k × ℕ => p ^ y.2) m := by
    rw [Finset.prod_pow_eq_pow_sum, monWt_eq_sum]
  have h3 : γ ^ monWt (fun y : Fin k × ℕ => p ^ y.2) m ≤ γ ^ N :=
    pow_le_pow_right_of_le_one' hγ hN
  rw [h2] at h1
  exact le_trans h1 h3

/-- The two-row refinement: the product is the product of the row-wise powers. -/
theorem prod_two_row_eq (B C : Γ₀) (m : Fin 2 × ℕ →₀ ℕ) :
    (∏ y ∈ m.support, (if y.1 = 0 then B else C) ^ (m y * p ^ y.2))
      = B ^ monWt (rhoRow (p := p) 0) m * C ^ monWt (rhoRow (p := p) 1) m := by
  classical
  have h0 : ∑ y ∈ m.support.filter (fun y => y.1 = 0), m y * p ^ y.2
      = monWt (rhoRow (p := p) 0) m := by
    rw [monWt_eq_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rhoRow]
    by_cases h : y.1 = 0 <;> simp [h]
  have h1 : ∑ y ∈ m.support.filter (fun y => ¬ y.1 = 0), m y * p ^ y.2
      = monWt (rhoRow (p := p) 1) m := by
    rw [monWt_eq_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rhoRow]
    by_cases h : y.1 = 0
    · simp [h]
    · rw [Fin.eq_one_of_ne_zero y.1 h]
      simp [h]
  rw [← h0, ← h1, ← Finset.prod_filter_mul_prod_filter_not m.support (fun y => y.1 = 0)]
  congr 1
  · refine (Finset.prod_congr rfl fun y hy => ?_).trans (Finset.prod_pow_eq_pow_sum _ _ _)
    rw [if_pos (Finset.mem_filter.mp hy).2]
  · refine (Finset.prod_congr rfl fun y hy => ?_).trans (Finset.prod_pow_eq_pow_sum _ _ _)
    rw [if_neg (Finset.mem_filter.mp hy).2]

theorem prod_beta_le_mul {B C : Γ₀} (hB : B ≤ 1) (hC : C ≤ 1) (m : Fin 2 × ℕ →₀ ℕ) {N : ℕ}
    (h0 : N ≤ monWt (rhoRow (p := p) 0) m) (h1 : N ≤ monWt (rhoRow (p := p) 1) m) :
    ∏ y ∈ m.support, (if y.1 = 0 then B else C) ^ (m y * p ^ y.2) ≤ (B * C) ^ N := by
  rw [prod_two_row_eq]
  calc B ^ monWt (rhoRow (p := p) 0) m * C ^ monWt (rhoRow (p := p) 1) m
      ≤ B ^ N * C ^ N :=
        mul_le_mul' (pow_le_pow_right_of_le_one' hB h0) (pow_le_pow_right_of_le_one' hC h1)
    _ = (B * C) ^ N := (mul_pow B C N).symm

end ProdBounds

section EvalBound

variable {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}

/-- **The evaluation bound.**  If `v` is the unit ball and `nv v` is subadditive, and the
coordinates of the family `x` are bounded by the powers of `β`, then `aeval x P` is bounded by any
`τ` dominating all the monomial products `∏ y, β_{y.1}^{m y · p^{y.2}}`. -/
theorem eval_bound {k : ℕ} {x : Fin k → ℕ → PreTilt R p} {β : Fin k → Γ₀}
    (hball : IsUnitBall v Set.univ)
    (hadd : ∀ a b : PreTilt R p, nv v (a + b) ≤ max (nv v a) (nv v b))
    (hx : ∀ i j, nv v (x i j) ≤ β i ^ p ^ j)
    {P : MvPolynomial (Fin k × ℕ) ℤ} {τ : Γ₀}
    (hP : ∀ m, P.coeff m ≠ 0 →
      ∏ y ∈ m.support, β y.1 ^ (m y * p ^ y.2) ≤ τ) :
    nv v (MvPolynomial.aeval (Function.uncurry x) P) ≤ τ := by
  classical
  have hsum : (MvPolynomial.aeval (Function.uncurry x)) P
      = ∑ m ∈ P.support, (MvPolynomial.aeval (Function.uncurry x))
          (MvPolynomial.monomial m (P.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
  rw [hsum]
  refine nv_sum_le hadd _ _ fun m hm => ?_
  rw [MvPolynomial.mem_support_iff] at hm
  rw [MvPolynomial.aeval_monomial, nv_mul]
  have hprod : nv v (Finsupp.prod m fun y e => Function.uncurry x y ^ e)
      ≤ ∏ y ∈ m.support, β y.1 ^ (m y * p ^ y.2) := by
    rw [show (Finsupp.prod m fun y e => Function.uncurry x y ^ e)
        = ∏ y ∈ m.support, Function.uncurry x y ^ (m y) from rfl]
    rw [nv_prod]
    refine Finset.prod_le_prod fun y _ => ?_
    rw [nv_pow]
    calc nv v (x y.1 y.2) ^ (m y) ≤ (β y.1 ^ p ^ y.2) ^ (m y) :=
          pow_le_pow_left' (hx y.1 y.2) (m y)
      _ = β y.1 ^ (m y * p ^ y.2) := by rw [← pow_mul, mul_comm]
  refine le_trans (mul_le_mul' (nv_le_one hball _) hprod) ?_
  rw [one_mul]
  exact hP m hm

end EvalBound

section Engine

variable {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}

/-- **Subadditivity of `DigLe`.** -/
theorem DigLe.add (hball : IsUnitBall v Set.univ)
    (hv : ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, v (p : R) ^ n < γ)
    {z u : WittVector p (PreTilt R p)} {B C : Γ₀} (hB : B ≤ 1) (hC : C ≤ 1)
    (hz : DigLe v z B) (hu : DigLe v u C) : DigLe v (z + u) (max B C) := by
  intro n
  have hcoeff : nv v ((z + u).coeff n) ≤ (max B C) ^ p ^ n := by
    rw [WittVector.add_coeff]
    refine eval_bound (v := v) (β := ![B, C]) (x := ![z.coeff, u.coeff]) hball
      (untilt_add_le hball hv) ?_ ?_
    · intro i j
      fin_cases i
      · simpa [Matrix.cons_val_zero] using hz.to_coeff j
      · simpa [Matrix.cons_val_one] using hu.to_coeff j
    · intro m hm
      have hβ : ∀ i, (![B, C] : Fin 2 → Γ₀) i ≤ max B C := by
        intro i; fin_cases i <;> simp [le_max_left, le_max_right]
      exact prod_beta_le_pow hβ (max_le hB hC) m
        (show p ^ n ≤ monWt (fun y : Fin 2 × ℕ => p ^ y.2) m
          from wtLe_wittAdd (p := p) n m hm)
  change nv v (tiltDigit (z + u) n) ≤ max B C
  apply le_of_pow_le_pow_left₀ (pow_ne_zero n (Fact.out : p.Prime).ne_zero) (zero_le)
  rw [nv_tiltDigit_pow]
  exact hcoeff

/-- **Submultiplicativity of `DigLe`.** -/
theorem DigLe.mul (hball : IsUnitBall v Set.univ)
    (hv : ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, v (p : R) ^ n < γ)
    {z u : WittVector p (PreTilt R p)} {B C : Γ₀} (hB : B ≤ 1) (hC : C ≤ 1)
    (hz : DigLe v z B) (hu : DigLe v u C) : DigLe v (z * u) (B * C) := by
  intro n
  have hcoeff : nv v ((z * u).coeff n) ≤ (B * C) ^ p ^ n := by
    rw [WittVector.mul_coeff]
    refine eval_bound (v := v) (β := ![B, C]) (x := ![z.coeff, u.coeff]) hball
      (untilt_add_le hball hv) ?_ ?_
    · intro i j
      fin_cases i
      · simpa [Matrix.cons_val_zero] using hz.to_coeff j
      · simpa [Matrix.cons_val_one] using hu.to_coeff j
    · intro m hm
      rw [show (∏ y ∈ m.support, (![B, C] : Fin 2 → Γ₀) y.1 ^ (m y * p ^ y.2))
          = ∏ y ∈ m.support, (if y.1 = 0 then B else C) ^ (m y * p ^ y.2) from
        Finset.prod_congr rfl (fun y _ => by
          obtain ⟨i, j⟩ := y
          fin_cases i <;> simp)]
      exact prod_beta_le_mul hB hC m (wtLe_wittMul_row (p := p) 0 n m hm)
        (wtLe_wittMul_row (p := p) 1 n m hm)
  change nv v (tiltDigit (z * u) n) ≤ B * C
  apply le_of_pow_le_pow_left₀ (pow_ne_zero n (Fact.out : p.Prime).ne_zero) (zero_le)
  rw [nv_tiltDigit_pow]
  exact hcoeff

end Engine

end Work.DSM2p
