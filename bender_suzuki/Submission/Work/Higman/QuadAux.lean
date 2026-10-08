/-
Copyright (c) 2024. All rights reserved.

# Finite-field linear algebra for Higman's Lemma 11

This file develops the elementary finite-field linear algebra used in
`Submission.Work.Higman.monomial_form` (Higman, *Suzuki 2-groups*, Lemma 11, type `A`).

The main results are

* `Work.Higman.monomial_indep` / `monomial_indep_finset`: the functions `x ↦ x ^ m`
  (`m < |F|`) are linearly independent over `F`;
* `Work.Higman.additive_coeff_choose_eq_zero`: if `A : F → F` is additive and
  `P := polyRep A` is its interpolating polynomial of degree `< |F|`, then
  `P.coeff m * (m.choose a : F) = 0` for `0 < a < m < |F|`;
* `Work.Higman.exists_odd_choose_of_not_pow_two`: for `m ≥ 1` which is not a power of `2`
  there is `0 < a < m` with `m.choose a` odd;
* `Work.Higman.additive_frob`: an additive map `A : F → F` (with `|F| = 2 ^ n` and `F` of
  characteristic two) is a "Frobenius combination"
  `A x = ∑_{k < n} (polyRep A).coeff (2 ^ k) * x ^ (2 ^ k)`.
-/

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

open Polynomial

namespace Work.Higman

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Lagrange interpolating polynomial of `f`, the unique polynomial of degree `< |F|`
taking the value `f x` at every `x : F`. -/
noncomputable def polyRep (f : F → F) : Polynomial F :=
  (Lagrange.interpolate Finset.univ id f)

lemma polyRep_eval (f : F → F) (x : F) : (polyRep f).eval x = f x := by
  rw [polyRep]
  exact Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (Finset.mem_univ x)

lemma polyRep_natDegree_lt (f : F → F) : (polyRep f).natDegree < Fintype.card F := by
  rcases eq_or_ne (polyRep f) 0 with h | h
  · rw [h]; simp only [natDegree_zero]
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  · rw [Polynomial.natDegree_lt_iff_degree_lt h]
    have hh := Lagrange.degree_interpolate_lt (v := id) (s := Finset.univ) f (Set.injOn_id _)
    simpa [polyRep, Finset.card_univ] using hh

/-- **Linear independence of monomials.**  If distinct exponents `e i < |F|` satisfy
`∑ i, c i * x ^ (e i) = 0` for every `x : F`, then all `c i` vanish. -/
theorem monomial_indep {ι : Type*} [Fintype ι] (e : ι → ℕ) (he : Function.Injective e)
    (hlt : ∀ i, e i < Fintype.card F) (c : ι → F)
    (h : ∀ x : F, ∑ i, c i * x ^ (e i) = 0) : ∀ i, c i = 0 := by
  classical
  set p : Polynomial F := ∑ i, C (c i) * X ^ (e i) with hp
  have heval : ∀ x : F, p.eval x = 0 := by
    intro x
    rw [hp, Polynomial.eval_finsetSum (s := Finset.univ)
      (g := fun i => C (c i) * X ^ (e i))]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact h x
  have hcard : p.natDegree < Fintype.card F := by
    have hdeg : p.natDegree ≤ Fintype.card F - 1 := by
      rw [hp]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_X_pow_le (c i) (e i)).trans
        (Nat.le_sub_one_of_lt (hlt i))
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hp0 : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Function.injective_id
      (fun x => by simpa using heval x) hcard
  intro i
  have hcoeff : p.coeff (e i) = c i := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    have h1 : (∑ x : ι, (if e i = e x then c x else 0)) = (if e i = e i then c i else 0) :=
      Finset.sum_eq_single (M := F) i (fun j _ hji => by
        have : ¬ (e i = e j) := fun hh => hji (he hh).symm
        simp [this]) (fun hi => absurd (Finset.mem_univ i) hi)
    simpa using h1
  rw [← hcoeff, hp0]
  simp

/-- `Finset` version of `monomial_indep`. -/
theorem monomial_indep_finset (s : Finset ℕ) (e : ℕ → ℕ) (he : Set.InjOn e ↑s)
    (hlt : ∀ m ∈ s, e m < Fintype.card F) (c : ℕ → F)
    (h : ∀ x : F, ∑ m ∈ s, c m * x ^ (e m) = 0) : ∀ m ∈ s, c m = 0 := by
  classical
  set p : Polynomial F := ∑ m ∈ s, C (c m) * X ^ (e m) with hp
  have heval : ∀ x, p.eval x = 0 := by
    intro x
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact h x
  have hcard : p.natDegree < Fintype.card F := by
    have hdeg : p.natDegree ≤ Fintype.card F - 1 := by
      rw [hp]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro m hm
      exact (Polynomial.natDegree_C_mul_X_pow_le (c m) (e m)).trans
        (Nat.le_sub_one_of_lt (hlt m hm))
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hp0 : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Function.injective_id
      (fun x => by simpa using heval x) hcard
  intro m hm
  have hcoeff : p.coeff (e m) = c m := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    have h1 : (∑ k ∈ s, (if e m = e k then c k else 0)) = (if e m = e m then c m else 0) :=
      Finset.sum_eq_single (M := F) m (fun j hj hjm => by
        have : ¬ (e m = e j) := fun hh => hjm (he hm hj hh).symm
        simp [this]) (fun hnot => absurd hm hnot)
    simpa using h1
  rw [← hcoeff, hp0]
  simp

/-- **Coefficient relation for an additive map.**  If `A : F → F` is additive and
`P = polyRep A`, then for `0 < a < m < |F|` we have `P.coeff m * (m.choose a : F) = 0`. -/
lemma additive_coeff_choose_eq_zero (A : F → F) (hA : ∀ x y, A (x + y) = A x + A y)
    {a : ℕ} (ha : 0 < a) {m : ℕ} (hm : m < Fintype.card F) (ham : a < m) :
    (polyRep A).coeff m * ((m.choose a : ℕ) : F) = 0 := by
  classical
  have hPN : (polyRep A).natDegree < Fintype.card F := polyRep_natDegree_lt A
  have hcomp : ∀ y : F, (polyRep A).comp (X + C y) = polyRep A + C ((polyRep A).eval y) := by
    intro y
    have hQ : (polyRep A).comp (X + C y) - (polyRep A + C ((polyRep A).eval y)) = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
      · intro x
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_comp,
          Polynomial.eval_X, Polynomial.eval_C, polyRep_eval]
        rw [hA]; ring
      · have h1 : ((polyRep A).comp (X + C y)).natDegree ≤ Fintype.card F - 1 := by
          have hle := Polynomial.natDegree_comp_le (p := polyRep A) (q := X + C y)
          rw [Polynomial.natDegree_X_add_C, mul_one] at hle
          omega
        have h2 : (polyRep A + C ((polyRep A).eval y)).natDegree ≤ Fintype.card F - 1 := by
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · omega
          · rw [Polynomial.natDegree_C]; omega
        have h3 := (Polynomial.natDegree_sub_le ((polyRep A).comp (X + C y))
          (polyRep A + C ((polyRep A).eval y))).trans (max_le h1 h2)
        have : 1 < Fintype.card F := Fintype.one_lt_card
        omega
    exact sub_eq_zero.mp hQ
  have hmain : ∀ y : F, ∑ k ∈ Finset.range (Fintype.card F),
      (polyRep A).coeff k * (y ^ (k - a) * ((k.choose a : ℕ) : F)) = (polyRep A).coeff a := by
    intro y
    have h := congrArg (fun p : Polynomial F => p.coeff a) (hcomp y)
    have hrep : (polyRep A) = ∑ i ∈ Finset.range (Fintype.card F),
        C ((polyRep A).coeff i) * X ^ i :=
      Polynomial.as_sum_range_C_mul_X_pow' _ hPN
    have hcomp_sum : (polyRep A).comp (X + C y) = ∑ i ∈ Finset.range (Fintype.card F),
        (C ((polyRep A).coeff i) * X ^ i).comp (X + C y) := by
      conv_lhs => rw [hrep]
      rw [Polynomial.sum_comp]
    have hL : ((polyRep A).comp (X + C y)).coeff a = ∑ k ∈ Finset.range (Fintype.card F),
        (polyRep A).coeff k * (y ^ (k - a) * ((k.choose a : ℕ) : F)) := by
      rw [hcomp_sum, Polynomial.finsetSum_coeff]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [Polynomial.C_mul_comp, Polynomial.X_pow_comp, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_add_C_pow])
    have hR : (polyRep A + C ((polyRep A).eval y)).coeff a = (polyRep A).coeff a := by
      rw [Polynomial.coeff_add, Polynomial.coeff_C_of_ne_zero (Nat.pos_iff_ne_zero.mp ha),
        add_zero]
    rw [hL, hR] at h
    exact h
  let D : ℕ → F := fun k => (polyRep A).coeff k * ((k.choose a : ℕ) : F)
  have hmainD : ∀ y : F, ∑ k ∈ Finset.range (Fintype.card F), D k * y ^ (k - a)
      = (polyRep A).coeff a := by
    intro y
    rw [← hmain y]
    exact Finset.sum_congr rfl (fun k _ => by
      show (polyRep A).coeff k * ((k.choose a : ℕ) : F) * y ^ (k - a) = _
      ring)
  have hzero_y : ∀ y : F,
      ∑ k ∈ (Finset.range (Fintype.card F)).filter (fun k => a < k), D k * y ^ (k - a) = 0 := by
    intro y
    have haN : a < Fintype.card F := by omega
    have hB : ∑ k ∈ (Finset.range (Fintype.card F)).filter (fun k => ¬ a < k),
        D k * y ^ (k - a) = (polyRep A).coeff a := by
      have hsingle : ∀ k ∈ (Finset.range (Fintype.card F)).filter (fun k => ¬ a < k),
          k ≠ a → D k * y ^ (k - a) = 0 := by
        intro k hk hka
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        have hklt : k < a := by omega
        have hc : k.choose a = 0 := Nat.choose_eq_zero_of_lt hklt
        show (polyRep A).coeff k * ((k.choose a : ℕ) : F) * y ^ (k - a) = 0
        rw [hc, Nat.cast_zero, mul_zero, zero_mul]
      have ha_mem : a ∈ (Finset.range (Fintype.card F)).filter (fun k => ¬ a < k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haN, by omega⟩
      have hsum0 : ∑ k ∈ ((Finset.range (Fintype.card F)).filter (fun k => ¬ a < k)).erase a,
          D k * y ^ (k - a) = 0 :=
        Finset.sum_eq_zero (fun k hk =>
          hsingle k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
      rw [← Finset.insert_erase ha_mem, Finset.sum_insert (Finset.notMem_erase a _), hsum0,
        add_zero]
      show (polyRep A).coeff a * ((a.choose a : ℕ) : F) * y ^ (a - a) = (polyRep A).coeff a
      rw [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, mul_one]
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (Fintype.card F))
      (fun k => a < k) (fun k => D k * y ^ (k - a))
    have h3 : (∑ k ∈ (Finset.range (Fintype.card F)).filter (fun k => a < k),
          D k * y ^ (k - a))
        = (∑ k ∈ Finset.range (Fintype.card F), D k * y ^ (k - a))
          - (∑ k ∈ (Finset.range (Fintype.card F)).filter (fun k => ¬ a < k),
              D k * y ^ (k - a)) :=
      (eq_sub_iff_add_eq).mpr hsplit
    rw [hmainD y, hB, sub_self] at h3
    exact h3
  have hs : ∀ k ∈ (Finset.range (Fintype.card F)).filter (fun k => a < k), D k = 0 := by
    refine monomial_indep_finset ((Finset.range (Fintype.card F)).filter (fun k => a < k))
      (fun k => k - a) ?_ ?_ D ?_
    · intro k hk k' hk' heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk hk'
      have heq' : k - a = k' - a := heq
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · exact hzero_y
  have hmem : m ∈ (Finset.range (Fintype.card F)).filter (fun k => a < k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, ham⟩
  have hlast := hs m hmem
  show (polyRep A).coeff m * ((m.choose a : ℕ) : F) = 0
  exact hlast

end FiniteField

/-- For `m ≥ 1` which is not a power of two there is `0 < a < m` with `m.choose a` odd.
Contrapositive of `Nat.Prime` Kummer/Lucas: `m.choose i` is even for all `1 ≤ i < m`
only when `m` is a power of `2`. -/
theorem exists_odd_choose_of_not_pow_two {m : ℕ} (hm : 0 < m)
    (h : ¬ ∃ k, m = 2 ^ k) : ∃ a, 0 < a ∧ a < m ∧ Odd (m.choose a) := by
  by_contra hcon
  push Not at hcon
  have hmul : m = 2 ^ multiplicity 2 m := by
    apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (p := 2) hm
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨h1, h2⟩ := hi
    have hodd : ¬ Odd (m.choose i) := hcon i (by omega) (by omega)
    rw [Nat.not_odd_iff_even, Nat.ModEq, Nat.even_iff] at *
    omega
  exact h ⟨multiplicity 2 m, hmul⟩

section FiniteFieldChar2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Frobenius form of an additive map.**  If `|F| = 2 ^ n`, `F` has characteristic two and
`A : F → F` is additive, then `A` is a "Frobenius combination": with `c m = (polyRep A).coeff m`,
`A x = ∑_{k < n} c (2 ^ k) * x ^ (2 ^ k)` for all `x`. -/
theorem additive_frob {n : ℕ} [CharP F 2] (hcard : Fintype.card F = 2 ^ n)
    (A : F → F) (hA : ∀ x y, A (x + y) = A x + A y) (x : F) :
    A x = ∑ k ∈ Finset.range n, (polyRep A).coeff (2 ^ k) * x ^ (2 ^ k) := by
  have hA0 : A 0 = 0 := by
    have h := hA 0 0
    rw [add_zero] at h
    have h1 : A 0 - A 0 = A 0 + A 0 - A 0 := congrArg (fun t => t - A 0) h
    rw [sub_self, add_sub_cancel_right] at h1
    exact h1.symm
  have hc0 : ∀ m, m < Fintype.card F → (¬ ∃ k, m = 2 ^ k) → (polyRep A).coeff m = 0 := by
    intro m hm hpow
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      rw [Polynomial.coeff_zero_eq_eval_zero, polyRep_eval, hA0]
    · obtain ⟨a, ha, ham, hodd⟩ := exists_odd_choose_of_not_pow_two hpos hpow
      have h := additive_coeff_choose_eq_zero A hA ha hm ham
      have hcast : ((m.choose a : ℕ) : F) ≠ 0 := by
        intro hzero
        rw [CharP.cast_eq_zero_iff] at hzero
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hzero)
      rcases mul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 hcast
  have hrep : (polyRep A) = ∑ m ∈ Finset.range (Fintype.card F),
      C ((polyRep A).coeff m) * X ^ m :=
    Polynomial.as_sum_range_C_mul_X_pow' _ (polyRep_natDegree_lt A)
  have heval : (polyRep A).eval x = ∑ m ∈ Finset.range (Fintype.card F),
      (polyRep A).coeff m * x ^ m := by
    conv_lhs => rw [hrep]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← polyRep_eval A x, heval]
  set im := (Finset.range n).image (fun k => 2 ^ k) with him
  have hsub : im ⊆ Finset.range (Fintype.card F) := by
    intro m hm
    rw [him, Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    rw [Finset.mem_range] at hk ⊢
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) hk
  have hzero : ∀ m ∈ Finset.range (Fintype.card F), m ∉ im →
      (polyRep A).coeff m * x ^ m = 0 := by
    intro m hm hmi
    have hmlt : m < Fintype.card F := Finset.mem_range.mp hm
    have hpow : ¬ ∃ k, m = 2 ^ k := by
      rintro ⟨k, hk⟩
      apply hmi
      rw [him, Finset.mem_image]
      refine ⟨k, ?_, hk.symm⟩
      rw [Finset.mem_range]
      by_contra hle
      push Not at hle
      rw [hk, hcard] at hmlt
      exact absurd hmlt (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hle))
    rw [hc0 m hmlt hpow, zero_mul]
  rw [← Finset.sum_subset hsub hzero, him, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.pow_right_injective (by norm_num) hab

end FiniteFieldChar2

end Work.Higman
