import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

attribute [local instance] Classical.propDecidable

/-! ## Dilation reduction for the Jacobi symbol

This file provides the proof of `Work.FIArea7.jacobiSym_dilation`, together with the
elementary facts about Jacobi symbols and about the `A`-coprime part of a modulus that
the proof needs.
-/

/-- `coprimePart A m` is the product of the prime powers of `m` at the primes `p` with `p ∤ A`:
the largest divisor of `m` all of whose prime factors are coprime to `A`. -/
noncomputable def coprimePart (A : ℤ) (m : ℕ) : ℕ :=
  (m.factorization.filter fun p : ℕ => ¬ (p : ℤ) ∣ A).prod (· ^ ·)

/-- `fullPart A m` is the complementary part of `m`: the product of the prime powers of `m`
at the primes `p` with `p ∣ A`. -/
noncomputable def fullPart (A : ℤ) (m : ℕ) : ℕ :=
  (m.factorization.filter fun p : ℕ => (p : ℤ) ∣ A).prod (· ^ ·)

/-! ### Multiplicativity of the Jacobi symbol over a product -/

/-- The Jacobi symbol is multiplicative over a product of non-zero moduli. -/
lemma jacobiSym_finset_prod {α : Type*} (a : ℤ) {f : α → ℕ} :
    ∀ {s : Finset α}, (∀ x ∈ s, f x ≠ 0) →
      jacobiSym a (∏ x ∈ s, f x) = ∏ x ∈ s, jacobiSym a (f x) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert x s hx ih =>
      intro hf
      rw [Finset.prod_insert hx, Finset.prod_insert hx,
        jacobiSym.mul_right' a (hf x (Finset.mem_insert_self x s))
          (Finset.prod_ne_zero_iff.mpr fun y hy => hf y (Finset.mem_insert_of_mem hy)),
        ih fun y hy => hf y (Finset.mem_insert_of_mem hy)]

/-- The Jacobi symbol decomposes over the prime powers of its modulus. -/
lemma jacobiSym_primeFactors_prod (a : ℤ) {n : ℕ} (hn : n ≠ 0) :
    jacobiSym a n = ∏ p ∈ n.primeFactors, jacobiSym a (p ^ n.factorization p) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  exact jacobiSym_finset_prod a fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-! ### The `A`-coprime part -/

lemma coprimePart_factorization (A : ℤ) (m : ℕ) :
    (coprimePart A m).factorization
      = m.factorization.filter (fun p : ℕ => ¬ (p : ℤ) ∣ A) := by
  unfold coprimePart
  exact Nat.prod_pow_factorization_eq_self fun p hp => by
    rw [Finsupp.support_filter] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma coprimePart_factorization_apply (A : ℤ) (m p : ℕ) :
    (coprimePart A m).factorization p = if ¬ (p : ℤ) ∣ A then m.factorization p else 0 := by
  rw [coprimePart_factorization, Finsupp.filter_apply]

lemma coprimePart_factorization_of_not_dvd {A : ℤ} {m p : ℕ} (h : ¬ (p : ℤ) ∣ A) :
    (coprimePart A m).factorization p = m.factorization p := by
  rw [coprimePart_factorization_apply, if_pos h]

lemma coprimePart_factorization_of_dvd {A : ℤ} {m p : ℕ} (h : (p : ℤ) ∣ A) :
    (coprimePart A m).factorization p = 0 := by
  rw [coprimePart_factorization_apply, if_neg (fun h' => h' h)]

lemma fullPart_factorization (A : ℤ) (m : ℕ) :
    (fullPart A m).factorization = m.factorization.filter (fun p : ℕ => (p : ℤ) ∣ A) := by
  unfold fullPart
  exact Nat.prod_pow_factorization_eq_self fun p hp => by
    rw [Finsupp.support_filter] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma fullPart_factorization_apply (A : ℤ) (m p : ℕ) :
    (fullPart A m).factorization p = if (p : ℤ) ∣ A then m.factorization p else 0 := by
  rw [fullPart_factorization, Finsupp.filter_apply]

lemma fullPart_factorization_of_dvd {A : ℤ} {m p : ℕ} (h : (p : ℤ) ∣ A) :
    (fullPart A m).factorization p = m.factorization p := by
  rw [fullPart_factorization_apply, if_pos h]

lemma coprimePart_dvd (A : ℤ) (m : ℕ) : coprimePart A m ∣ m := by
  unfold coprimePart
  refine Nat.prod_pow_dvd_of_le_factorization ?_
  rw [Finsupp.le_def]
  intro p
  rw [Finsupp.filter_apply]
  split <;> simp

lemma fullPart_dvd (A : ℤ) (m : ℕ) : fullPart A m ∣ m := by
  unfold fullPart
  refine Nat.prod_pow_dvd_of_le_factorization ?_
  rw [Finsupp.le_def]
  intro p
  rw [Finsupp.filter_apply]
  split <;> simp

lemma coprimePart_ne_zero (A : ℤ) {m : ℕ} (hm : m ≠ 0) : coprimePart A m ≠ 0 := by
  intro h
  have hd := coprimePart_dvd A m
  rw [h] at hd
  exact hm (zero_dvd_iff.mp hd)

lemma fullPart_ne_zero (A : ℤ) {m : ℕ} (hm : m ≠ 0) : fullPart A m ≠ 0 := by
  intro h
  have hd := fullPart_dvd A m
  rw [h] at hd
  exact hm (zero_dvd_iff.mp hd)

/-- The `A`-coprime part and its complement multiply back to `m`. -/
lemma coprimePart_mul_fullPart {A : ℤ} {m : ℕ} (hm : m ≠ 0) :
    coprimePart A m * fullPart A m = m := by
  have hsplit : m.factorization.filter (fun p : ℕ => ¬ (p : ℤ) ∣ A)
      + m.factorization.filter (fun p : ℕ => (p : ℤ) ∣ A) = m.factorization := by
    ext p
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases h : (p : ℤ) ∣ A
    · rw [if_neg (not_not_intro h), if_pos h, zero_add]
    · rw [if_pos h, if_neg h, add_zero]
  calc coprimePart A m * fullPart A m
      = (m.factorization.filter (fun p : ℕ => ¬ (p : ℤ) ∣ A)).prod (· ^ ·)
          * (m.factorization.filter (fun p : ℕ => (p : ℤ) ∣ A)).prod (· ^ ·) := rfl
    _ = (m.factorization.filter (fun p : ℕ => ¬ (p : ℤ) ∣ A)
          + m.factorization.filter (fun p : ℕ => (p : ℤ) ∣ A)).prod (· ^ ·) :=
          (Finsupp.prod_add_index' (fun a => by simp) (fun a b₁ b₂ => by rw [pow_add])).symm
    _ = m.factorization.prod (· ^ ·) := by rw [hsplit]
    _ = m := Nat.prod_factorization_pow_eq_self hm

/-- `A` is coprime to the `A`-coprime part of `m`. -/
lemma coprime_natAbs_coprimePart (A : ℤ) {m : ℕ} (hm : m ≠ 0) :
    Nat.Coprime A.natAbs (coprimePart A m) := by
  have hm' : coprimePart A m ≠ 0 := coprimePart_ne_zero A hm
  rw [Nat.prod_primeFactors_pow_factorization hm']
  refine Nat.Coprime.prod_right fun p hp => ?_
  refine Nat.Coprime.pow_right _ ?_
  have hnotdvd : ¬ (p : ℤ) ∣ A := by
    intro hc
    have hfac : (coprimePart A m).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    rw [coprimePart_factorization_apply, if_neg (not_not_intro hc)] at hfac
    exact hfac rfl
  rw [Nat.coprime_comm]
  refine (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mpr ?_
  intro hd
  exact hnotdvd (by rw [← Int.natAbs_dvd_natAbs]; simpa using hd)

/-! ### The per-prime-power dilation step -/

lemma jacobiSym_pow_of_dvd (A c u : ℤ) {p : ℕ} (hd : (p : ℤ) ∣ A) (e : ℕ) :
    jacobiSym (A * u + c) (p ^ e) = jacobiSym c (p ^ e) := by
  rw [jacobiSym.pow_right, jacobiSym.pow_right]
  congr 1
  apply jacobiSym.mod_left'
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,
    show A * u + c - c = A * u by ring,
    Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd u)]

lemma jacobiSym_pow_of_not_dvd (A c c' u : ℤ) {p : ℕ} (hd : (p : ℤ) ∣ A * c' - c) (e : ℕ) :
    jacobiSym (A * u + c) (p ^ e) = jacobiSym A (p ^ e) * jacobiSym (u + c') (p ^ e) := by
  rw [jacobiSym.pow_right, jacobiSym.pow_right, jacobiSym.pow_right, ← mul_pow]
  congr 1
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,
    show A * u + c - A * (u + c') = -(A * c' - c) by ring,
    Int.emod_eq_zero_of_dvd (dvd_neg.mpr hd)]

/-! ### Solving `A c' ≡ c` modulo `m'` -/

lemma exists_mul_sub_dvd (A c : ℤ) {m' : ℕ} (hcop : Nat.Coprime A.natAbs m') :
    ∃ c' : ℤ, (m' : ℤ) ∣ A * c' - c := by
  have hu : IsUnit (A : ZMod m') := by
    rcases Int.natAbs_eq A with h | h
    · rw [h]; simpa using (ZMod.unitOfCoprime A.natAbs hcop).isUnit
    · rw [h]; simpa using (ZMod.unitOfCoprime A.natAbs hcop).isUnit.neg
  refine ⟨ZMod.valMinAbs ((A : ZMod m')⁻¹ * (c : ZMod m')), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul, sub_self]

/-- **Dilation reduction for the Jacobi symbol.**  For odd `m`, a dilation step `A` and a shift `c`,
the function `u ↦ (A*u + c | m)` is (up to a constant of modulus `≤ 1`) a *shifted* Jacobi symbol
with the `A`-coprime part `m'` of `m` as its modulus.  More precisely, there are `K, c' : ℤ` and
`m' : ℕ` with `|K| ≤ 1`, `m' ∣ m`,

  `(A*u + c | m) = K · (u + c' | m')`  for all `u : ℤ`,

`m'` contains exactly the prime powers of `m` at the primes `p ∤ A` (and none at the primes `p ∣ A`).

Concretely `m' = ∏_{p ∣ m, p ∤ A} p ^ m.factorization p`, `K = (c | m/m')·(A | m')` and
`c' ≡ c·A⁻¹ (mod m')`; the proof writes `(A*u+c | p)^{e} = (c|p)^e` for `p ∣ A` (as `A*u+c ≡ c`)
and `= (A|p)^e·(u + c A⁻¹|p)^e` for `p ∤ A`, and multiplies over the prime powers of `m`
(`jacobiSym.mul_right` splits the prime-factor list, so `(a | p^e) = (a|p)^e` is definitional).
The prime-power properties pin `m'` down uniquely, so that in applications one can read off
`p ∣ m' ⟺ (p ∣ m ∧ p ∤ A)` and the exponent of `p` in `m'`.

Used in *FI* §22 to pass from the progression `s = b + 4dg·u` (where the `4d`-split freezes the
`4d`-periodic character `χ`) to genuine shifted Jacobi characters of *coprime* moduli, so that
`Work.FIArea7.twoChar_pv_dilated` applies. -/
theorem jacobiSym_dilation (A c : ℤ) (m : ℕ) (hm : Odd m) :
    ∃ (K c' : ℤ) (m' : ℕ),
      |K| ≤ 1 ∧ m' ∣ m ∧
      (∀ u : ℤ, jacobiSym (A * u + c) m = K * jacobiSym (u + c') m') ∧
      (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ A → m'.factorization p = m.factorization p) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ A → m'.factorization p = 0) := by
  classical
  have hm0 : m ≠ 0 := hm.pos.ne'
  obtain ⟨c', hc'⟩ := exists_mul_sub_dvd A c (coprime_natAbs_coprimePart A hm0)
  refine ⟨jacobiSym A (coprimePart A m) * jacobiSym c (fullPart A m), c', coprimePart A m,
    ?_, coprimePart_dvd A m, ?_, ?_, ?_⟩
  · have h1 := jacobiSym.trichotomy A (coprimePart A m)
    have h2 := jacobiSym.trichotomy c (fullPart A m)
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  · intro u
    have hm'0 : coprimePart A m ≠ 0 := coprimePart_ne_zero A hm0
    have hm''0 : fullPart A m ≠ 0 := fullPart_ne_zero A hm0
    have hα : jacobiSym (A * u + c) (coprimePart A m)
        = jacobiSym A (coprimePart A m) * jacobiSym (u + c') (coprimePart A m) := by
      rw [jacobiSym_primeFactors_prod (A * u + c) hm'0, jacobiSym_primeFactors_prod A hm'0,
        jacobiSym_primeFactors_prod (u + c') hm'0, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      refine jacobiSym_pow_of_not_dvd A c c' u ?_ _
      have hpd : (p : ℤ) ∣ ((coprimePart A m : ℕ) : ℤ) := by
        exact_mod_cast Nat.dvd_of_mem_primeFactors hp
      exact hpd.trans hc'
    have hβ : jacobiSym (A * u + c) (fullPart A m) = jacobiSym c (fullPart A m) := by
      rw [jacobiSym_primeFactors_prod (A * u + c) hm''0, jacobiSym_primeFactors_prod c hm''0]
      refine Finset.prod_congr rfl fun p hp => ?_
      refine jacobiSym_pow_of_dvd A c u ?_ _
      have hfac : (fullPart A m).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
      rw [fullPart_factorization_apply] at hfac
      by_contra hc
      rw [if_neg hc] at hfac
      exact hfac rfl
    calc jacobiSym (A * u + c) m
        = jacobiSym (A * u + c) (coprimePart A m * fullPart A m) := by
            rw [coprimePart_mul_fullPart hm0]
      _ = jacobiSym (A * u + c) (coprimePart A m) * jacobiSym (A * u + c) (fullPart A m) :=
            jacobiSym.mul_right' _ hm'0 hm''0
      _ = (jacobiSym A (coprimePart A m) * jacobiSym (u + c') (coprimePart A m))
            * jacobiSym c (fullPart A m) := by rw [hα, hβ]
      _ = (jacobiSym A (coprimePart A m) * jacobiSym c (fullPart A m))
            * jacobiSym (u + c') (coprimePart A m) := by ring
  · intro p hp hpa
    exact coprimePart_factorization_of_not_dvd hpa
  · intro p hp hpa
    exact coprimePart_factorization_of_dvd hpa

end Work.FIArea7
