import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.Analysis.MvPolynomial

open scoped BigOperators

/-!
# Evaluating a homogeneous polynomial at a point with two free coordinates

If `P` is homogeneous of degree `k`, then evaluating `P` at a point whose only
possibly nonzero coordinates are the two coordinates `a` and `b` (with values
`s` and `t`) gives a sum over the monomials of `P` with `d a + d b = k` of
`coeff d * s^(d a) * t^(d b)`.

Everything else vanishes: a monomial `X^d` of total degree `k` has a nonzero
exponent in some coordinate outside `{a, b}` unless `d a + d b = k`, and at
such coordinates the evaluation variable is `0`.
-/

/-- Total weight with the constant weight `1` equals the sum of the exponents. -/
lemma weight_one_eq_sum {n : ℕ} (d : Fin n →₀ ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) d = ∑ i : Fin n, d i := by
  rw [Finsupp.weight_eq_sum]
  simp

/-- A sum over all of `Fin n` splits off the two terms at `a` and `b`. -/
lemma sum_univ_pair_add_rest {n : ℕ} (a b : Fin n) (hab : a ≠ b) (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = f a + f b +
      ∑ x ∈ ((Finset.univ.erase a).erase b : Finset (Fin n)), f x := by
  calc
    (∑ i : Fin n, f i) = (∑ x ∈ (Finset.univ : Finset (Fin n)).erase a, f x) + f a := by
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (f := f) (a := a)]
      simp
    _ = (∑ x ∈ ((Finset.univ : Finset (Fin n)).erase a).erase b, f x) + f b + f a := by
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)).erase a) (f := f) (a := b)]
      exact Finset.mem_erase.mpr ⟨fun hba : b = a => hab hba.symm, Finset.mem_univ b⟩
    _ = f a + f b + ∑ x ∈ ((Finset.univ : Finset (Fin n)).erase a).erase b, f x := by
      omega

/-- If `Finsupp.weight 1 d = k` and `d a + d b = k`, then `d` is supported only
on `{a, b}` (here `a ≠ b`). -/
lemma eq_zero_outside_of_weight_eq_sum {n : ℕ} (a b : Fin n) (hab : a ≠ b) {d : Fin n →₀ ℕ}
    {k : ℕ} (hdw : Finsupp.weight (1 : Fin n → ℕ) d = k) (hdab : d a + d b = k) :
    ∀ i : Fin n, i ≠ a → i ≠ b → d i = 0 := by
  intro i hia hib
  have hwsum : Finsupp.weight (1 : Fin n → ℕ) d = ∑ x : Fin n, d x := weight_one_eq_sum d
  have hsplit : (∑ x : Fin n, d x) = d a + d b +
      ∑ y ∈ ((Finset.univ.erase a).erase b : Finset (Fin n)), d y :=
    sum_univ_pair_add_rest a b hab (fun x => d x)
  have hrest : (∑ x ∈ ((Finset.univ : Finset (Fin n)).erase a).erase b, d x) = 0 := by
    omega
  have hi : i ∈ ((Finset.univ : Finset (Fin n)).erase a).erase b := by
    simp [hia, hib]
  have hmain := (Finset.sum_eq_zero_iff.mp hrest) i hi
  simpa using hmain

/-- If `Finsupp.weight 1 d = k` but `d a + d b ≠ k`, then some coordinate outside
`{a, b}` carries a nonzero exponent (here `a ≠ b`). -/
lemma exists_ne_zero_outside_of_weight_ne_sum {n : ℕ} (a b : Fin n) (hab : a ≠ b) {d : Fin n →₀ ℕ}
    {k : ℕ} (hdw : Finsupp.weight (1 : Fin n → ℕ) d = k) (hne : d a + d b ≠ k) :
    ∃ i : Fin n, i ≠ a ∧ i ≠ b ∧ d i ≠ 0 := by
  by_contra h
  have hall : ∀ i : Fin n, i ≠ a → i ≠ b → d i = 0 := by
    intro i hia hib
    by_contra hd
    exact h ⟨i, hia, hib, hd⟩
  have hwsum : Finsupp.weight (1 : Fin n → ℕ) d = ∑ x : Fin n, d x := weight_one_eq_sum d
  have hsplit : (∑ x : Fin n, d x) = d a + d b +
      ∑ y ∈ ((Finset.univ.erase a).erase b : Finset (Fin n)), d y :=
    sum_univ_pair_add_rest a b hab (fun x => d x)
  have hrest_zero : (∑ x ∈ ((Finset.univ : Finset (Fin n)).erase a).erase b, d x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxne : x ≠ b := (Finset.mem_erase.mp hx).1
    have hxmem : x ∈ (Finset.univ : Finset (Fin n)).erase a := (Finset.mem_erase.mp hx).2
    have hxne' : x ≠ a := (Finset.mem_erase.mp hxmem).1
    exact hall x hxne' hxne
  have hsum : d a + d b = k := by omega
  exact hne hsum

/-- A product over `Fin n` of factors that are all `1` except possibly at the two
distinct elements `a` and `b` equals the product of those two factors. -/
lemma prod_pair_eq_mul {n : ℕ} (a b : Fin n) (hab : a ≠ b) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, i ≠ a → i ≠ b → g i = 1) :
    (∏ i : Fin n, g i) = g a * g b := by
  let U : Finset (Fin n) := Finset.univ
  calc
    (∏ i : Fin n, g i) = U.prod g := by simp [U]
    _ = (U.erase b).prod g * g b := by
      rw [← Finset.prod_erase_mul U g (by simp [U])]
    _ = ((U.erase b).erase a).prod g * g a * g b := by
      rw [← Finset.prod_erase_mul (s := U.erase b) (f := g) (a := a)
        (by exact Finset.mem_erase.mpr ⟨hab, by simp [U]⟩)]
    _ = g a * g b := by
      have hrest : ((U.erase b).erase a).prod g = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        have hib : i ≠ b := (Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).1
        exact hg i hia hib
      rw [hrest]
      ring

/-- Evaluation monomial value of `∏ i, v i ^ d i` when all exponents outside `{a, b}`
vanish, with `v a = s`, `v b = t`, and `v i = 0` elsewhere. -/
lemma prod_eval_two_coordinates {n : ℕ} (a b : Fin n) (hab : a ≠ b) (s t : ℝ)
    {d : Fin n →₀ ℕ} (hd : ∀ i : Fin n, i ≠ a → i ≠ b → d i = 0) :
    (∏ i : Fin n, (if i = a then s else if i = b then t else 0) ^ d i) =
      s ^ d a * t ^ d b := by
  classical
  let v : Fin n → ℝ := fun i => if i = a then s else if i = b then t else 0
  have hv_a : v a = s := by simp [v]
  have hv_b : v b = t := by
    dsimp [v]
    rw [if_neg (show b ≠ a from fun hba : b = a => hab hba.symm), if_pos rfl]
  have hv_out : ∀ i : Fin n, i ≠ a → i ≠ b → v i = 0 := by
    intro i hia hib
    simp [v, hia, hib]
  calc
    (∏ i : Fin n, (if i = a then s else if i = b then t else 0) ^ d i)
        = ∏ i : Fin n, (v i) ^ d i := by simp [v]
    _ = (v a) ^ d a * (v b) ^ d b := by
      apply prod_pair_eq_mul a b hab (fun i => (v i) ^ d i)
      intro i hia hib
      rw [hv_out i hia hib, hd i hia hib]
      simp
    _ = s ^ d a * t ^ d b := by rw [hv_a, hv_b]

theorem eval_support_subset_two {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (P : MvPolynomial (Fin n) ℝ) {k : ℕ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (s t : ℝ) :
    MvPolynomial.eval (fun i : Fin n => if i = a then s else if i = b then t else 0) P
      = ∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k),
          P.coeff d * s ^ (d a) * t ^ (d b) := by
  classical
  let v : Fin n → ℝ := fun i => if i = a then s else if i = b then t else 0
  change MvPolynomial.eval v P =
    ∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k),
      P.coeff d * s ^ (d a) * t ^ (d b)
  have hIso : ∀ d : Fin n →₀ ℕ, P.coeff d ≠ 0 → Finsupp.weight (1 : Fin n → ℕ) d = k := by
    intro d hd
    exact (MvPolynomial.mem_homogeneousSubmodule (n := k) P).mp hP (d := d) hd
  let F : (Fin n →₀ ℕ) → ℝ := fun d => P.coeff d * (∏ i : Fin n, (v i) ^ (d i))
  have hF_zero_of_not : ∀ d : Fin n →₀ ℕ, d ∈ P.support → d a + d b ≠ k → F d = 0 := by
    intro d hdmem hne
    have hcoeff : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hdmem
    have hdw : Finsupp.weight (1 : Fin n → ℕ) d = k := hIso d hcoeff
    rcases exists_ne_zero_outside_of_weight_ne_sum a b hab hdw hne with ⟨j, hja, hjb, hdj⟩
    have hprod0 : (∏ i : Fin n, (v i) ^ (d i)) = 0 := by
      apply Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => (v i) ^ (d i)) (i := j) (by simp)
      have hvj : v j = 0 := by
        simp [v, hja, hjb]
      rw [hvj, zero_pow hdj]
    dsimp [F]
    rw [hprod0]
    ring
  have hfilter_sum : (∑ d ∈ P.support, F d) =
      ∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k), F d := by
    symm
    apply Finset.sum_filter_of_ne
    intro d hdmem hFne
    by_contra hne
    exact hFne (hF_zero_of_not d hdmem hne)
  have hF_on : ∀ d : Fin n →₀ ℕ,
      d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k) →
        F d = P.coeff d * s ^ (d a) * t ^ (d b) := by
    intro d hdf
    have hdmem : d ∈ P.support := (Finset.mem_filter.mp hdf).1
    have hdab : d a + d b = k := (Finset.mem_filter.mp hdf).2
    have hcoeff : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hdmem
    have hdw : Finsupp.weight (1 : Fin n → ℕ) d = k := hIso d hcoeff
    have hout : ∀ i : Fin n, i ≠ a → i ≠ b → d i = 0 :=
      eq_zero_outside_of_weight_eq_sum a b hab hdw hdab
    have hprod : (∏ i : Fin n, (v i) ^ (d i)) = (v a) ^ (d a) * (v b) ^ (d b) := by
      apply prod_pair_eq_mul a b hab (fun i => (v i) ^ (d i))
      intro i hia hib
      have hvi : v i = 0 := by simp [v, hia, hib]
      rw [hvi, hout i hia hib]
      simp
    dsimp [F]
    rw [hprod]
    have hv_a : v a = s := by simp [v]
    have hv_b : v b = t := by
      dsimp [v]
      rw [if_neg (show b ≠ a from fun hba : b = a => hab hba.symm), if_pos rfl]
    rw [hv_a, hv_b]
    ring
  calc
    MvPolynomial.eval v P = ∑ d ∈ P.support, F d := by
      dsimp [F]
      exact MvPolynomial.eval_eq' v P
    _ = ∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k), F d := hfilter_sum
    _ = ∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k),
          P.coeff d * s ^ (d a) * t ^ (d b) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hF_on d hd

end Commons.Analysis.MvPolynomial