import Mathlib
import Submission.CDT.Residue
import Submission.Commons.Data.Rat.exists_nat_mul_eq_int

/-!
# The function-field Lindemann–Weierstrass theorem: multiplicative dependence

The classical function-field Lindemann–Weierstrass theorem says that a `ℂ`-linear relation among
logarithms `Σᵢ cᵢ log fᵢ ∈ ℂ(y)` (i.e. `Σᵢ cᵢ fᵢ'/fᵢ` is a derivative) forces the `fᵢ` to be
**multiplicatively dependent**.

Here the *derivative* form of the hypothesis is proved in the sharpest elementary case: if
`Σᵢ cᵢ (dRat fᵢ)/fᵢ = dRat h` with **integer** coefficients `cᵢ` (and all `fᵢ ≠ 0`), then

  `∏ᵢ fᵢ ^ cᵢ` **is a constant**   (`prod_zpow_const_of_sum_dRat_div`).

The proof is the classical residue argument, entirely inside `K(X)`:

* the logarithmic derivative `(dRat fᵢ)/fᵢ` has residue `ordAt α fᵢ` at `α`
  (`residueAt_dRat_div_self`), which is an *integer*;
* hence the combination `Σᵢ cᵢ (dRat fᵢ)/fᵢ` has residue `Σᵢ cᵢ · ordAt α fᵢ` at `α`;
* but it equals `dRat h`, and `dRat h` never has a simple pole (`ordAt_dRat_ne_neg_one`), so
  `Σᵢ cᵢ · ordAt α fᵢ = 0` for every `α`;
* consequently `ordAt α (∏ᵢ fᵢ ^ cᵢ) = 0` for every `α`, i.e. the product has no zeros and no
  poles — it is a constant.

Corollaries: two rational functions with the same logarithmic derivative differ by a nonzero
constant (`exists_const_mul_of_dRat_div_eq`); a rational function whose logarithmic derivative is
a derivative is constant; `dRat f / f` is not a multiple of a derivative for nonconstant `f`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- `ordAt` of an integer power: `ordAt α (x ^ n) = n * ordAt α x` for `x ≠ 0`, `n : ℤ`. -/
lemma ordAt_zpow (α : K) {x : RatFunc K} (hx : x ≠ 0) (n : ℤ) :
    ordAt α (x ^ n) = n * ordAt α x := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · subst hk
    rw [zpow_natCast, ordAt_pow]
  · subst hk
    rw [zpow_neg, zpow_natCast, ordAt_inv α (pow_ne_zero k hx), ordAt_pow]
    ring

/-- `ordAt` is additive over finite products of nonzero factors. -/
lemma ordAt_prod {ι : Type*} (α : K) (s : Finset ι) (g : ι → RatFunc K)
    (hg : ∀ i ∈ s, g i ≠ 0) :
    ordAt α (∏ i ∈ s, g i) = ∑ i ∈ s, ordAt α (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ordAt_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      ordAt_mul α (hg i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hg j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))]

/-- Residues are additive over finite sums. -/
lemma ResidueAt.sum {ι : Type*} {α : K} {s : Finset ι} {g : ι → RatFunc K} {d : ι → K}
    (h : ∀ i ∈ s, ResidueAt α (g i) (d i)) :
    ResidueAt α (∑ i ∈ s, g i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ResidueAt.of_ordAt_nonneg (by rw [ordAt_zero])
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ResidueAt.add (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- **Function-field Lindemann–Weierstrass (multiplicative-dependence form).**  Let `K` be an
algebraically closed field of characteristic `0`, `f : ι → K(X)` a finite family of nonzero
rational functions and `c : ι → ℤ` integer coefficients.  If the combination
`Σᵢ cᵢ · (dRat fᵢ)/fᵢ` of logarithmic derivatives is a derivative in `K(X)`, then
`∏ᵢ fᵢ ^ cᵢ` is a nonzero constant. -/
theorem prod_zpow_const_of_sum_dRat_div [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → ℤ)
    (h : ∃ h₀ : RatFunc K,
      ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (f i) / f i) = dRat h₀) :
    ∃ C : K, C ≠ 0 ∧ ∏ i, f i ^ (c i) = algebraMap K (RatFunc K) C := by
  obtain ⟨h₀, hh₀⟩ := h
  -- the residue of the combination at `α` is `Σᵢ cᵢ · ordAt α (fᵢ)`
  have hres : ∀ α : K,
      ResidueAt α (∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (f i) / f i))
        (∑ i, ((c i : ℤ) : K) * ((ordAt α (f i) : ℤ) : K)) := by
    intro α
    refine ResidueAt.sum (s := Finset.univ) (fun i _ => ?_)
    exact ResidueAt.const_mul (residueAt_dRat_div_self (f i) (hf i) α) ((c i : ℤ) : K)
  -- the no-simple-pole theorem forces the residue to vanish
  have hzero : ∀ α : K, ∑ i, ((c i : ℤ) : K) * ((ordAt α (f i) : ℤ) : K) = 0 := by
    intro α
    by_contra hne
    have h1 : ordAt α (dRat h₀) = -1 := by
      have h2 := (hres α).ordAt_eq_neg_one hne
      rwa [hh₀] at h2
    exact ordAt_dRat_ne_neg_one α h₀ h1
  -- integer form of the relation
  have hint : ∀ α : K, ∑ i, c i * ordAt α (f i) = 0 := by
    intro α
    have h1 : (((∑ i, c i * ordAt α (f i)) : ℤ) : K) = 0 := by
      have heq : (((∑ i, c i * ordAt α (f i)) : ℤ) : K)
          = ∑ i, ((c i : ℤ) : K) * ((ordAt α (f i) : ℤ) : K) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Int.cast_mul])
      rw [heq, hzero α]
    exact_mod_cast h1
  -- the product has order `0` everywhere
  have hord : ∀ α : K, ordAt α (∏ i, f i ^ (c i)) = 0 := by
    intro α
    have h1 : ordAt α (∏ i, f i ^ (c i)) = ∑ i, ordAt α (f i ^ (c i)) :=
      ordAt_prod α Finset.univ (fun i => f i ^ (c i)) (fun i _ => zpow_ne_zero (c i) (hf i))
    rw [h1]
    rw [Finset.sum_congr rfl (fun i _ => ordAt_zpow α (hf i) (c i))]
    rw [hint α]
  -- a rational function with no zeros and no poles is constant
  have hdR : dRat (∏ i, f i ^ (c i)) = 0 := by
    by_contra hne
    obtain ⟨α, hα⟩ := exists_ordAt_ne_zero_of_dRat_ne_zero (∏ i, f i ^ (c i)) hne
    exact hα (hord α)
  obtain ⟨C, hC⟩ := exists_const_of_dRat_eq_zero hdR
  refine ⟨C, ?_, hC⟩
  intro hC0
  have h0 : (∏ i, f i ^ (c i)) = 0 := by rw [hC, hC0, map_zero]
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero (c i) (hf i))) h0

/-- **Two rational functions with the same logarithmic derivative differ by a nonzero
constant.** -/
theorem exists_const_mul_of_dRat_div_eq [IsAlgClosed K] {f g : RatFunc K} (hf : f ≠ 0)
    (hg : g ≠ 0) (h : dRat f / f = dRat g / g) :
    ∃ C : K, C ≠ 0 ∧ f = algebraMap K (RatFunc K) C * g := by
  set F : Fin 2 → RatFunc K := ![f, g] with hF
  set c : Fin 2 → ℤ := ![1, -1] with hc
  have hF0 : ∀ i, F i ≠ 0 := by
    intro i; fin_cases i
    · simpa [hF] using hf
    · simpa [hF] using hg
  have hsum : ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (F i) / F i) = dRat 0 := by
    rw [Fin.sum_univ_two]
    simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h, dRat_zero]
    push_cast
    ring
  obtain ⟨C, hC0, hC⟩ := prod_zpow_const_of_sum_dRat_div F hF0 c ⟨0, hsum⟩
  refine ⟨C, hC0, ?_⟩
  rw [Fin.prod_univ_two] at hC
  simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one] at hC
  rw [zpow_one, zpow_neg_one] at hC
  rw [← hC]
  field_simp

/-- A rational function whose logarithmic derivative is a derivative is constant: this is the
case `ι = Fin 1` of `prod_zpow_const_of_sum_dRat_div`. -/
theorem exists_const_of_dRat_div_eq_dRat [IsAlgClosed K] {f : RatFunc K} (hf : f ≠ 0)
    (h : ∃ h₀ : RatFunc K, dRat f / f = dRat h₀) : ∃ C : K, f = algebraMap K (RatFunc K) C := by
  set F : Fin 1 → RatFunc K := fun _ => f with hF
  set c : Fin 1 → ℤ := fun _ => 1 with hc
  have hF0 : ∀ i, F i ≠ 0 := fun i => by simpa [hF] using hf
  obtain ⟨h₀, hh⟩ := h
  have hsum : ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (F i) / F i)
      = dRat h₀ := by
    rw [Fin.sum_univ_one]
    simp only [hc, hF]
    rw [hh]
    push_cast
    ring
  obtain ⟨C, _, hC⟩ := prod_zpow_const_of_sum_dRat_div F hF0 c ⟨h₀, hsum⟩
  refine ⟨C, ?_⟩
  rw [Fin.prod_univ_one] at hC
  simp only [hF, hc] at hC
  rw [zpow_one] at hC
  exact hC

/-- The derivative of a constant is zero. -/
lemma dRat_const (t : K) : dRat (algebraMap K (RatFunc K) t) = 0 := by
  rw [← am_C', dRat_algebraMap, Polynomial.derivative_C, map_zero]

/-- The derivative of a constant multiple. -/
lemma dRat_const_mul (t : K) (h : RatFunc K) :
    dRat (algebraMap K (RatFunc K) t * h) = algebraMap K (RatFunc K) t * dRat h := by
  rw [dRat_mul, dRat_const, zero_mul, zero_add]

/-- **Lindemann–Weierstrass (multiplicative dependence) with rational coefficients.**  If a
`ℚ`-linear combination of logarithmic derivatives `Σᵢ cᵢ·(dRat fᵢ)/fᵢ` (`cᵢ ∈ ℚ`) is a derivative in
`K(X)`, then clearing denominators produces a nontrivial *integer* multiplicative relation
`∏ᵢ fᵢ ^ mᵢ ∈ K`. -/
theorem exists_int_prod_zpow_const_of_sum_dRat_div_rat [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → ℚ) (hc : c ≠ 0)
    (h : ∃ h₀ : RatFunc K,
      ∑ i, algebraMap K (RatFunc K) ((c i : ℚ) : K) * (dRat (f i) / f i) = dRat h₀) :
    ∃ m : ι → ℤ, m ≠ 0 ∧ ∃ C : K, C ≠ 0 ∧ ∏ i, f i ^ (m i) = algebraMap K (RatFunc K) C := by
  classical
  obtain ⟨h₀, hh₀⟩ := h
  obtain ⟨N, hNpos, hm⟩ := Commons.Data.Rat.exists_nat_mul_eq_int c
  choose m hm' using hm
  have hNne : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNneK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  -- `(m i : K) = (N : K) * (c i : K)`
  have hcast : ∀ i, ((m i : ℤ) : K) = (N : K) * ((c i : ℚ) : K) := by
    intro i
    have h2 : (N : K) * ((c i : ℚ) : K) = ((m i : ℤ) : K) := by
      have h3 : (((N : ℚ) * c i : ℚ) : K) = ((m i : ℚ) : K) := by rw [hm' i]
      rw [Rat.cast_mul, Rat.cast_natCast] at h3
      rw [h3]
      exact Rat.cast_intCast (m i)
    exact h2.symm
  have hsum : ∑ i, algebraMap K (RatFunc K) ((m i : ℤ) : K) * (dRat (f i) / f i)
      = dRat (algebraMap K (RatFunc K) (N : K) * h₀) := by
    have h1 : ∑ i, algebraMap K (RatFunc K) ((m i : ℤ) : K) * (dRat (f i) / f i)
        = algebraMap K (RatFunc K) (N : K)
          * ∑ i, algebraMap K (RatFunc K) ((c i : ℚ) : K) * (dRat (f i) / f i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcast i, map_mul]
      ring
    rw [h1, hh₀, dRat_const_mul]
  obtain ⟨C, hC0, hC⟩ :=
    prod_zpow_const_of_sum_dRat_div f hf m ⟨algebraMap K (RatFunc K) (N : K) * h₀, hsum⟩
  refine ⟨m, ?_, C, hC0, hC⟩
  intro hm0
  exact hc (funext fun i => by
    have h1 := hm' i
    rw [hm0] at h1
    exact (mul_eq_zero.mp h1).resolve_left hNne)

/-- The logarithmic derivative of an integer power, `n : ℤ`. -/
lemma logDeriv_zpow (f : RatFunc K) (hf : f ≠ 0) (n : ℤ) :
    dRat (f ^ n) / f ^ n = algebraMap K (RatFunc K) ((n : ℤ) : K) * (dRat f / f) := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) :=
      ⟨(-n).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    subst hk
    have hneg : (((-(k : ℤ)) : ℤ) : K) = -(k : K) := by
      rw [Int.cast_neg, Int.cast_natCast]
    rw [zpow_neg, zpow_natCast, dRat_inv_div (f ^ k) (pow_ne_zero k hf),
      dRat_pow_div f hf k, hneg, map_neg]
    ring
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by rw [Int.toNat_of_nonneg hn]⟩
    subst hk
    have hpos : (((k : ℤ)) : K) = (k : K) := Int.cast_natCast k
    rw [zpow_natCast, dRat_pow_div f hf k, hpos]

/-- **The logarithmic derivative of a finite product is the sum of the logarithmic derivatives.** -/
lemma logDeriv_prod {ι : Type*} (s : Finset ι) (g : ι → RatFunc K) (hg : ∀ i ∈ s, g i ≠ 0) :
    dRat (∏ i ∈ s, g i) / (∏ i ∈ s, g i) = ∑ i ∈ s, dRat (g i) / g i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, dRat_one, div_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      dRat_mul_div _ _ (hg i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hg j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))]

/-- **The converse direction**: if `∏ᵢ fᵢ ^ cᵢ` is a constant then the combination
`Σᵢ cᵢ·(dRat fᵢ)/fᵢ` of logarithmic derivatives is the derivative of `0` (i.e. vanishes).  This
shows that the conclusion of `prod_zpow_const_of_sum_dRat_div` is exactly the right one: the
integer multiplicative relations span all the known log-relations. -/
theorem sum_dRat_div_eq_zero_of_prod_zpow_const {ι : Type*} [Fintype ι]
    (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → ℤ)
    (h : ∃ C : K, ∏ i, f i ^ (c i) = algebraMap K (RatFunc K) C) :
    ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (f i) / f i) = 0 := by
  obtain ⟨C, hC⟩ := h
  have hlog : ∑ i, algebraMap K (RatFunc K) ((c i : ℤ) : K) * (dRat (f i) / f i)
      = dRat (∏ i, f i ^ (c i)) / (∏ i, f i ^ (c i)) := by
    rw [logDeriv_prod Finset.univ (fun i => f i ^ (c i))
      (fun i _ => zpow_ne_zero (c i) (hf i))]
    exact Finset.sum_congr rfl (fun i _ => (logDeriv_zpow (f i) (hf i) (c i)).symm)
  rw [hlog, hC, dRat_const, zero_div]

end Submission.CDT
