/-
# Basic material for `Work.FIArea7.twoChar_pv_dilated`

The product of two Jacobi-symbol characters `(A n + c₁ | m₁)·(A n + c₂ | m₂)` is reduced, in
`Submission/Work/FIArea7/TwoCharPV/twoChar_reduce.lean`, to a *single* Jacobi symbol
`(n + d | Q)` of a modulus `Q` built from the parts of `m₁, m₂` coprime to `A`.  This file
contains

* the definition of the part `aCore A m` of `m` supported on the primes dividing `A` and of its
  complement `aFree A m` (the part coprime to `A`), together with the elementary divisibility
  facts, and
* the general Jacobi-symbol identities used in the reduction:
  multiplicativity of `jacobiSym` over a finite product of moduli,
  the formula `J(a|b) = ∏_{p ‖ b} J(a|p)^{v_p(b)}`,
  the "constancy" of `J(·|u)` when every prime of `u` divides `A`,
  the dilation identity `J(A n + c|w) = J(A|w)·J(n + d|w)` for `w ∣ A d − c`,
  the CRT combination `J(n + d₁|u)·J(n + d₂|v) = J(n + d|uv)`,
  and the two existence lemmas producing `d`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7

open scoped BigOperators

/-! ## The part of `m` supported on the primes dividing `A` -/

/-- `aCore A m` is the part of `m` supported on the primes dividing `A` (the `gcd` of `m` with a
sufficiently large power of `A`). -/
def aCore (A m : ℕ) : ℕ := m.gcd (A ^ m)

/-- `aFree A m` is the part of `m` supported on the primes **not** dividing `A` (all primes
dividing `A` removed from `m`). -/
def aFree (A m : ℕ) : ℕ := m / m.gcd (A ^ m)

lemma aCore_dvd (A m : ℕ) : aCore A m ∣ m := Nat.gcd_dvd_left m (A ^ m)

lemma aCore_mul_aFree (A m : ℕ) : aCore A m * aFree A m = m :=
  Nat.mul_div_cancel' (aCore_dvd A m)

lemma aFree_dvd (A m : ℕ) : aFree A m ∣ m := Nat.div_dvd_of_dvd (aCore_dvd A m)

lemma aCore_pos {A m : ℕ} (hm : 0 < m) : 0 < aCore A m := Nat.gcd_pos_of_pos_left _ hm

lemma aFree_pos {A m : ℕ} (hm : 0 < m) : 0 < aFree A m :=
  Nat.div_pos (Nat.gcd_le_left (A ^ m) hm) (Nat.gcd_pos_of_pos_left _ hm)

/-- Every prime dividing `aCore A m` divides `A`. -/
lemma aCore_prime_dvd {A m p : ℕ} (hp : p.Prime) (h : p ∣ aCore A m) : p ∣ A :=
  hp.dvd_of_dvd_pow (h.trans (Nat.gcd_dvd_right m (A ^ m)))

/-! ## Jacobi-symbol identities -/

/-- Multiplicativity of the Jacobi symbol over a finite product of non-zero moduli. -/
lemma jacobiSym_prod_right {ι : Type*} (s : Finset ι) (f : ι → ℕ) (a : ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      rw [jacobiSym.mul_right' a (hf i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
      rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- The Jacobi symbol as a product over the prime factors: `J(a|b) = ∏_{p ‖ b} J(a|p)^{v_p(b)}`. -/
lemma jacobiSym_eq_prod_primeFactors (a : ℤ) {b : ℕ} (hb : b ≠ 0) :
    jacobiSym a b = ∏ p ∈ b.primeFactors, (jacobiSym a p) ^ (b.factorization p) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hb]
  rw [jacobiSym_prod_right _ _ _
    (fun p hp => pow_ne_zero _ ((Nat.mem_primeFactors.mp hp).1.ne_zero))]
  exact Finset.prod_congr rfl (fun p _ => by rw [jacobiSym.pow_right])

/-- **Constancy of `J(·|u)` on the primes of `u` dividing `A`**: if every prime factor of `u`
divides `A`, then `J(A n + c|u) = J(c|u)` for all `n`. -/
lemma jacobiSym_const_of_prime_dvd {u : ℕ} {A : ℤ}
    (h : ∀ p : ℕ, p.Prime → p ∣ u → (p : ℤ) ∣ A) (c n : ℤ) :
    jacobiSym (A * n + c) u = jacobiSym c u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [jacobiSym_eq_prod_primeFactors (A * n + c) hu, jacobiSym_eq_prod_primeFactors c hu]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hAp : (p : ℤ) ∣ A := h p hp' (Nat.mem_primeFactors.mp hp).2.1
    have hdvd : (p : ℤ) ∣ A * n + c - c := by
      rw [show A * n + c - c = A * n by ring]
      exact dvd_mul_of_dvd_left hAp n
    have hmod : (A * n + c) % (p : ℤ) = c % (p : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_eq_zero_of_dvd hdvd]
    rw [jacobiSym.mod_left' hmod]

/-- **Dilation identity**: if `w ∣ A d − c` then `J(A n + c|w) = J(A|w)·J(n + d|w)`. -/
lemma jacobiSym_dilate {w : ℕ} {A c d : ℤ} (hd : (w : ℤ) ∣ A * d - c) (n : ℤ) :
    jacobiSym (A * n + c) w = jacobiSym A w * jacobiSym (n + d) w := by
  have hdvd : (w : ℤ) ∣ A * (n + d) - (A * n + c) := by
    rw [show A * (n + d) - (A * n + c) = A * d - c by ring]; exact hd
  have hmod : A * (n + d) % (w : ℤ) = (A * n + c) % (w : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_eq_zero_of_dvd hdvd]
  rw [← jacobiSym.mod_left' hmod, jacobiSym.mul_left]

/-- **CRT combination of two Jacobi symbols**: for non-zero `u, v` and `d` congruent to `d₁`
modulo `u` and to `d₂` modulo `v`, the product of the two Jacobi symbols is the single Jacobi
symbol of modulus `u * v`. -/
lemma jacobiSym_crt_mul (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) {d d₁ d₂ : ℤ}
    (h₁ : (u : ℤ) ∣ d - d₁) (h₂ : (v : ℤ) ∣ d - d₂) (n : ℤ) :
    jacobiSym (n + d₁) u * jacobiSym (n + d₂) v = jacobiSym (n + d) (u * v) := by
  rw [jacobiSym.mul_right' _ hu hv]
  have e₁ : (n + d) % (u : ℤ) = (n + d₁) % (u : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,
      show n + d - (n + d₁) = d - d₁ by ring, Int.emod_eq_zero_of_dvd h₁]
  have e₂ : (n + d) % (v : ℤ) = (n + d₂) % (v : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,
      show n + d - (n + d₂) = d - d₂ by ring, Int.emod_eq_zero_of_dvd h₂]
  rw [jacobiSym.mod_left' e₁, jacobiSym.mod_left' e₂]

/-- **Existence of the dilation parameter**: if `A` and `w` are coprime (over `ℤ`), then for any
`c` there is `d` with `w ∣ A d − c`. -/
lemma exists_dvd_mul_sub {w : ℕ} {A c : ℤ} (h : IsCoprime A (w : ℤ)) :
    ∃ d : ℤ, (w : ℤ) ∣ A * d - c := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * c, ⟨-(b * c), ?_⟩⟩
  linear_combination (c : ℤ) * hab

/-- **Existence of the CRT parameter**: for coprime `u, v` and any `d₁, d₂` there is `d` with
`u ∣ d − d₁` and `v ∣ d − d₂`. -/
lemma exists_crt_int {u v : ℕ} (h : Nat.Coprime u v) (d₁ d₂ : ℤ) :
    ∃ d : ℤ, (u : ℤ) ∣ d - d₁ ∧ (v : ℤ) ∣ d - d₂ := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr h.symm : IsCoprime (v : ℤ) (u : ℤ))
  refine ⟨d₁ * (a * v) + d₂ * (b * u), ⟨b * (d₂ - d₁), ?_⟩, ⟨a * (d₁ - d₂), ?_⟩⟩
  · linear_combination d₁ * hab
  · linear_combination d₂ * hab

end Work.FIArea7
