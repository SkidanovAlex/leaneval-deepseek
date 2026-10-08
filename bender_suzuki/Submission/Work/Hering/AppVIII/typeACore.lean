import Mathlib
import Submission.Work.Higman.bivariate_monomial_indep
import Submission.Work.Higman.coeff_vanishing_of_scale
import Submission.Work.Hering.AppVIII.FrobBasis
import Submission.Work.Hering.AppVIII.MonomialCoeff
import Submission.Work.Hering.AppVIII.TwoPowArith
import Submission.Work.Hering.AppVIII.supportSingleton

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Hering.AppVIII

/-- `x ^ (2 ^ n) = x` for `|K| = 2 ^ n`. -/
theorem pow_two_pow_cardField {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (x : K) : x ^ (2 ^ n) = x := by
  rw [← hcard]
  exact FiniteField.pow_card x

/-- **Coefficient extraction for sums of quadratic Frobenius monomials.**
If `∑_{a,b<n} D a b · x^(2^a) · x^(2^b) = 0` for every `x` in a finite field `K` of
characteristic two with `|K| = 2^n`, then the diagonal coefficients `D a a` vanish and `D` is
antisymmetric: `D a b + D b a = 0`. -/
theorem quadSplitCoeff {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (D : ℕ → ℕ → K)
    (h : ∀ x : K, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
        D a b * x ^ (2 ^ a) * x ^ (2 ^ b) = 0) :
    (∀ a ∈ Finset.range n, D a a = 0) ∧
      (∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n, D a b + D b a = 0) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun a ha => absurd ha (by simp), fun a ha => absurd ha (by simp)⟩
  have hpow : ∀ x : K, x ^ (2 ^ n) = x := pow_two_pow_cardField hcard
  have h2n : 2 ≤ 2 ^ n := by
    have := Nat.one_lt_pow (show n ≠ 0 by omega) (show (1:ℕ) < 2 by norm_num)
    omega
  -- ### Off-diagonal part, via polarization and `bivariate_monomial_indep`.
  have hoff : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n, D a b + D b a = 0 := by
    have hbiv : ∀ x y : K, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
        (D a b + D b a) * x ^ (2 ^ a) * y ^ (2 ^ b) = 0 := by
      intro x y
      set A : K := ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D a b * x ^ (2^a) * x ^ (2^b)
      set B : K := ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D a b * x ^ (2^a) * y ^ (2^b)
      set C : K := ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D a b * y ^ (2^a) * x ^ (2^b)
      set Dy : K := ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D a b * y ^ (2^a) * y ^ (2^b)
      have hA : A = 0 := h x
      have hDy : Dy = 0 := h y
      have h3 : ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
          D a b * (x + y) ^ (2 ^ a) * (x + y) ^ (2 ^ b) = 0 := h (x + y)
      have expand : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
          D a b * (x + y) ^ (2 ^ a) * (x + y) ^ (2 ^ b)) = A + B + C + Dy := by
        have hinner : ∀ a : ℕ, (∑ b ∈ Finset.range n,
            D a b * (x + y) ^ (2 ^ a) * (x + y) ^ (2 ^ b))
            = (∑ b ∈ Finset.range n, D a b * x ^ (2^a) * x ^ (2^b))
              + (∑ b ∈ Finset.range n, D a b * x ^ (2^a) * y ^ (2^b))
              + (∑ b ∈ Finset.range n, D a b * y ^ (2^a) * x ^ (2^b))
              + (∑ b ∈ Finset.range n, D a b * y ^ (2^a) * y ^ (2^b)) := by
          intro a
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [add_pow_char_pow, add_pow_char_pow]
          ring
        rw [Finset.sum_congr rfl (fun a _ => hinner a)]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [expand, hA, hDy, zero_add, add_zero] at h3
      -- h3 : B + C = 0
      have hCe : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D b a * x ^ (2^a) * y ^ (2^b)) = C := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
      have hsum2 : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
          (D a b + D b a) * x ^ (2 ^ a) * y ^ (2 ^ b)) = B + C := by
        have hterm : ∀ a b : ℕ, (D a b + D b a) * x ^ (2^a) * y ^ (2^b)
            = D a b * x ^ (2^a) * y ^ (2^b) + D b a * x ^ (2^a) * y ^ (2^b) :=
          fun a b => by ring
        calc (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, (D a b + D b a) * x ^ (2^a) * y ^ (2^b))
            = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
                (D a b * x ^ (2^a) * y ^ (2^b) + D b a * x ^ (2^a) * y ^ (2^b)) :=
              Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
          _ = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D a b * x ^ (2^a) * y ^ (2^b))
                + (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D b a * x ^ (2^a) * y ^ (2^b)) := by
              simp only [Finset.sum_add_distrib]
          _ = B + C := by rw [hCe]
      rw [hsum2]
      exact h3
    intro a ha b hb
    exact Work.Higman.bivariate_monomial_indep hcard (fun a b => D a b + D b a) hbiv a ha b hb
  -- ### Diagonal part, via a polynomial argument.
  have hdiag : ∀ a ∈ Finset.range n, D a a = 0 := by
    set P : Polynomial K := ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
        Polynomial.C (D a b) * Polynomial.X ^ (2 ^ a + 2 ^ b) with hP
    have hPeval : ∀ x : K, P.eval x = 0 := by
      intro x
      rw [hP, Polynomial.eval_finsetSum, ← h x]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        pow_add]
      ring
    have hPdeg : P.natDegree ≤ 2 ^ n := by
      rw [hP]
      refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range n)
        (fun a => ∑ b ∈ Finset.range n, Polynomial.C (D a b) * Polynomial.X ^ (2 ^ a + 2 ^ b)) ?_
      intro a ha
      refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range n)
        (fun b => Polynomial.C (D a b) * Polynomial.X ^ (2 ^ a + 2 ^ b)) ?_
      intro b hb
      refine (Polynomial.natDegree_C_mul_X_pow_le (D a b) (2 ^ a + 2 ^ b)).trans ?_
      have ha' : a < n := Finset.mem_range.mp ha
      have hb' : b < n := Finset.mem_range.mp hb
      have h1 : 2 ^ a ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ b ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        rw [← two_mul, ← Nat.pow_succ']
        congr 1
        omega
      omega
    set c : K := P.coeff (2 ^ n) with hc
    set E : Polynomial K := P - Polynomial.C c * (Polynomial.X ^ (2 ^ n) - Polynomial.X) with hE
    have hEeval : ∀ x : K, E.eval x = 0 := by
      intro x
      rw [hE, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, hPeval x, hpow x]
      ring
    have hEdeg : E.natDegree < 2 ^ n := by
      have hEq : E = (P - Polynomial.C c * Polynomial.X ^ (2 ^ n)) + Polynomial.C c * Polynomial.X := by
        rw [hE]; ring
      rw [hEq]
      have hR : (P - Polynomial.C c * Polynomial.X ^ (2 ^ n)).natDegree ≤ 2 ^ n - 1 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hc, Polynomial.coeff_X_pow]
        by_cases hN' : N = 2 ^ n
        · subst hN'; simp
        · rw [if_neg hN']
          have hPN : P.coeff N = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPdeg (by omega))
          rw [hPN]; ring
      have hS : (Polynomial.C c * Polynomial.X).natDegree ≤ 1 := by
        have hX : (Polynomial.X : Polynomial K) ^ 1 = Polynomial.X := pow_one _
        rw [← hX]
        exact Polynomial.natDegree_C_mul_X_pow_le c 1
      have hadd : ((P - Polynomial.C c * Polynomial.X ^ (2 ^ n)) + Polynomial.C c * Polynomial.X).natDegree
          < 2 ^ n := by
        refine lt_of_le_of_lt (Polynomial.natDegree_add_le
          (P - Polynomial.C c * Polynomial.X ^ (2 ^ n)) (Polynomial.C c * Polynomial.X)) ?_
        exact max_lt (lt_of_le_of_lt hR (by omega)) (lt_of_le_of_lt hS (by omega))
      exact hadd
    have hE0 : E = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' E Finset.univ
        (fun x _ => hEeval x) (by rw [Finset.card_univ, hcard]; exact hEdeg)
    have hPc : P = Polynomial.C c * (Polynomial.X ^ (2 ^ n) - Polynomial.X) := by
      have hsub : P - Polynomial.C c * (Polynomial.X ^ (2 ^ n) - Polynomial.X) = 0 := by
        rw [← hE]; exact hE0
      exact sub_eq_zero.mp hsub
    have hPcoeff1 : P.coeff 1 = 0 := by
      rw [hP]
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro hcon
      have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      omega
    have hPcoeff1' : P.coeff 1 = -c := by
      rw [hPc, Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, if_neg (by omega : ¬ (1 = 2 ^ n)), if_pos rfl]
      ring
    have hc0 : c = 0 := by
      rw [hPcoeff1'] at hPcoeff1
      exact neg_eq_zero.mp hPcoeff1
    have hPzero : P = 0 := by rw [hPc, hc0, Polynomial.C_0, zero_mul]
    have hPcoeff_form : ∀ m : ℕ, P.coeff m = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
        (if m = 2 ^ a + 2 ^ b then D a b else 0) := by
      intro m
      rw [hP]
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    have hcoeff : ∀ m : ℕ, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
        (if m = 2 ^ a + 2 ^ b then D a b else 0) = 0 := by
      intro m
      rw [← hPcoeff_form m, hPzero, Polynomial.coeff_zero]
    have diag_class : ∀ i j a : ℕ, 2 ^ (a + 1) = 2 ^ i + 2 ^ j → i = a ∧ j = a := by
      intro i j a hij
      have h' : 2 ^ i + 2 ^ j = 2 ^ a + 2 ^ a := by rw [← hij, pow_succ]; ring
      rcases twoPowAddEq' h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, h2⟩
    intro a ha
    have h0 := hcoeff (2 ^ (a + 1))
    have hsum : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (if 2 ^ (a + 1) = 2 ^ i + 2 ^ j then D i j else 0)) = D a a := by
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single a]
        · rw [if_pos (by rw [pow_succ]; ring)]
        · intro j hj hja
          rw [if_neg]; intro hcon; exact hja (diag_class a j a hcon).2
        · intro hna; exact absurd ha hna
      · intro i hi hia
        apply Finset.sum_eq_zero
        intro j hj
        rw [if_neg]; intro hcon; exact hia (diag_class i j a hcon).1
      · intro hna; exact absurd ha hna
    rw [hsum] at h0
    exact h0
  exact ⟨hdiag, hoff⟩

/-- `x ^ (2 ^ m)` depends on `m` only modulo `n`, when `|K| = 2 ^ n`. -/
theorem pow_two_pow_modulo {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (hn : 0 < n) (x : K) (m : ℕ) :
    x ^ (2 ^ m) = x ^ (2 ^ (m % n)) := by
  have hpow : ∀ y : K, y ^ (2 ^ n) = y := pow_two_pow_cardField hcard
  have hxq : ∀ q : ℕ, x ^ (2 ^ (n * q)) = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hpow]
  calc x ^ (2 ^ m) = x ^ (2 ^ (n * (m / n) + m % n)) := by rw [Nat.div_add_mod]
    _ = x ^ (2 ^ (n * (m / n)) * 2 ^ (m % n)) := by rw [pow_add]
    _ = (x ^ (2 ^ (n * (m / n)))) ^ (2 ^ (m % n)) := by rw [pow_mul]
    _ = x ^ (2 ^ (m % n)) := by rw [hxq (m / n)]

/-- Frobenius additivity for finite sums. -/
theorem sum_pow_two {K : Type*} [CommSemiring K] [CharP K 2] {ι : Type*} (s : Finset ι)
    (a : ι → K) (m : ℕ) : (∑ i ∈ s, a i) ^ (2 ^ m) = ∑ i ∈ s, (a i) ^ (2 ^ m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_pow_char_pow, ih]

/-- The shift `k ↦ (k + s) % n` followed by `- s` returns `k`. -/
theorem mod_shift_key {n s : ℕ} (hsn : s < n) {k : ℕ} (hk : k < n) :
    ((k + s) % n + n - s) % n = k := by
  have hsle : s ≤ n := le_of_lt hsn
  rw [Nat.add_sub_assoc hsle, Nat.mod_add_mod,
    show (k + s) + (n - s) = k + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- The shift `k ↦ (k + n - s) % n` followed by `+ s` returns `k`. -/
theorem mod_shift_key' {n s : ℕ} (hs : s ≤ n) {k : ℕ} (hk : k < n) :
    ((k + n - s) % n + s) % n = k := by
  rw [Nat.mod_add_mod]
  rw [show k + n - s + s = k + n by omega]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- Reindexing a sum over `range n` by the shift `b ↦ (b + n - s) % n`. -/
theorem sum_shift_mod {K : Type*} [Field K] (lam : ℕ → K) (x : K) {n s : ℕ}
    (hsn : s < n) (hn : 0 < n) :
    (∑ b ∈ Finset.range n, (lam ((b + n - s) % n)) ^ (2 ^ s) * x ^ (2 ^ b))
      = ∑ j ∈ Finset.range n, (lam j) ^ (2 ^ s) * x ^ (2 ^ ((j + s) % n)) := by
  refine (Finset.sum_bij (fun k _ => (k + s) % n) ?_ ?_ ?_ ?_).symm
  · intro k _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  · intro k1 hk1 k2 hk2 heq
    rw [← mod_shift_key hsn (Finset.mem_range.mp hk1),
      ← mod_shift_key hsn (Finset.mem_range.mp hk2), heq]
  · intro j hj
    exact ⟨(j + n - s) % n, Finset.mem_range.mpr (Nat.mod_lt _ hn),
      mod_shift_key' (le_of_lt hsn) (Finset.mem_range.mp hj)⟩
  · intro k hk
    rw [mod_shift_key hsn (Finset.mem_range.mp hk)]

/-- From the Frobenius expansions of additive maps `f, g` satisfying `g (x·x^{2^s}) = f x·(f x)^{2^s}`
one reads off the three structural relations used in Appendix VIII, Proposition 1. -/
theorem relationsFromIdentity {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    {n s : ℕ} (hcard : Fintype.card K = 2 ^ n) (hsn : s < n) (hs0 : s ≠ 0) (h4 : ¬ n ∣ 4 * s)
    (lam mu : ℕ → K) (f g : K → K)
    (hf : ∀ x : K, f x = ∑ i ∈ Finset.range n, lam i * x ^ (2 ^ i))
    (hg : ∀ x : K, g x = ∑ i ∈ Finset.range n, mu i * x ^ (2 ^ i))
    (hid : ∀ x : K, g (x * x ^ (2 ^ s)) = f x * (f x) ^ (2 ^ s)) :
    (∀ i < n, lam i * (lam ((i + n - s) % n)) ^ (2 ^ s) = 0) ∧
    (∀ i < n, mu i = lam i * (lam i) ^ (2 ^ s)
      + lam ((i + s) % n) * (lam ((i + n - s) % n)) ^ (2 ^ s)) ∧
    (∀ i < n, ∀ j < n, i ≠ j → (i + s) % n ≠ j → (j + s) % n ≠ i →
      lam i * (lam ((j + n - s) % n)) ^ (2 ^ s)
        + lam j * (lam ((i + n - s) % n)) ^ (2 ^ s) = 0) := by
  have hn : 0 < n := by omega
  have hsle : s ≤ n := le_of_lt hsn
  have h2s : ¬ n ∣ 2 * s := fun hd => h4 (by
    have := dvd_mul_of_dvd_right hd 2
    rwa [show 2 * (2 * s) = 4 * s by ring] at this)
  set D : ℕ → ℕ → K := fun a b =>
      (if b = (a + s) % n then mu a else 0)
        - lam a * (lam ((b + n - s) % n)) ^ (2 ^ s) with hD
  have hident : ∀ x : K, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
      D a b * x ^ (2 ^ a) * x ^ (2 ^ b) = 0 := by
    intro x
    have hsplit : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, D a b * x ^ (2^a) * x ^ (2^b))
        = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              (if b = (a + s) % n then mu a else 0) * x ^ (2^a) * x ^ (2^b))
          - (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              lam a * (lam ((b + n - s) % n)) ^ (2^s) * x ^ (2^a) * x ^ (2^b)) := by
      simp only [hD, sub_mul, Finset.sum_sub_distrib]
    have hP : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              (if b = (a + s) % n then mu a else 0) * x ^ (2^a) * x ^ (2^b))
        = g (x * x ^ (2^s)) := by
      have h1 : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              (if b = (a + s) % n then mu a else 0) * x ^ (2^a) * x ^ (2^b))
          = ∑ a ∈ Finset.range n, mu a * x ^ (2^a) * x ^ (2^((a + s) % n)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single ((a + s) % n)]
        · rw [if_pos rfl]
        · intro b _ hb; rw [if_neg hb, zero_mul, zero_mul]
        · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ hn)) hnot
      rw [h1, hg]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_pow, ← pow_mul]
      rw [show (2:ℕ) ^ s * 2 ^ a = 2 ^ (s + a) by rw [← pow_add]]
      rw [pow_two_pow_modulo hcard hn x (s + a), Nat.add_comm s a]
      ring
    have hM : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              lam a * (lam ((b + n - s) % n)) ^ (2^s) * x ^ (2^a) * x ^ (2^b))
        = f x * (f x) ^ (2^s) := by
      have hW : (∑ b ∈ Finset.range n, (lam ((b + n - s) % n)) ^ (2^s) * x ^ (2^b))
          = (f x) ^ (2^s) := by
        rw [sum_shift_mod lam x hsn hn, hf, sum_pow_two]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, ← pow_mul]
        rw [show (2:ℕ) ^ j * 2 ^ s = 2 ^ (j + s) by rw [← pow_add]]
        rw [pow_two_pow_modulo hcard hn x (j + s)]
      have h1 : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              lam a * (lam ((b + n - s) % n)) ^ (2^s) * x ^ (2^a) * x ^ (2^b))
          = (∑ a ∈ Finset.range n, lam a * x ^ (2^a))
              * (∑ b ∈ Finset.range n, (lam ((b + n - s) % n)) ^ (2^s) * x ^ (2^b)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [h1, hW, ← hf]
    rw [hsplit, hP, hM, hid x, sub_self]
  obtain ⟨hdiag, hoff⟩ := quadSplitCoeff hcard D hident
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := hdiag i (Finset.mem_range.mpr hi)
    have hii : ¬ (i = (i + s) % n) := by
      intro heq
      have hm : i ≡ i + s [MOD n] := by rw [Nat.ModEq, Nat.mod_eq_of_lt hi, ← heq]
      have hd : n ∣ s := by
        have := (Nat.modEq_iff_dvd' (by omega : i ≤ i + s)).mp hm
        rwa [show (i + s) - i = s by omega] at this
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hsn] at hd
      exact hs0 hd
    simp only [hD] at h
    rw [if_neg hii, zero_sub] at h
    exact neg_eq_zero.mp h
  · intro i hi
    have hb : (i + s) % n < n := Nat.mod_lt _ hn
    have h := hoff i (Finset.mem_range.mpr hi) ((i + s) % n) (Finset.mem_range.mpr hb)
    simp only [hD, if_true] at h
    have hcond : ¬ (i = ((i + s) % n + s) % n) := by
      intro heq
      have e1 : ((i + s) % n + s) % n = (i + 2 * s) % n := by
        rw [Nat.mod_add_mod]; congr 1; omega
      rw [e1] at heq
      have hm : i ≡ i + 2 * s [MOD n] := by rw [Nat.ModEq, Nat.mod_eq_of_lt hi, ← heq]
      have hd : n ∣ 2 * s := by
        have := (Nat.modEq_iff_dvd' (by omega : i ≤ i + 2 * s)).mp hm
        rwa [show (i + 2 * s) - i = 2 * s by omega] at this
      exact h2s hd
    rw [if_neg hcond, mod_shift_key hsn hi] at h
    linear_combination h
  · intro i hi j hj hij h1 h2
    have h := hoff i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj)
    simp only [hD] at h
    rw [if_neg (fun hc => h1 hc.symm), if_neg (fun hc => h2 hc.symm)] at h
    rw [zero_sub, zero_sub, ← neg_add] at h
    exact neg_eq_zero.mp h

theorem typeACore {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {n s : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (hsn : s < n) (hs0 : s ≠ 0) (h4 : ¬ n ∣ 4 * s)
    (f g : K → K) (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (hfnz : ∃ x, f x ≠ 0) (hid : ∀ x, g (x * x ^ (2 ^ s)) = f x * (f x) ^ (2 ^ s)) :
    ∃ (lam : K) (i : ℕ), lam ≠ 0 ∧ i < n ∧ (∀ x, f x = lam * x ^ (2 ^ i)) ∧
      (∀ z, g z = lam * lam ^ (2 ^ s) * z ^ (2 ^ i)) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt := Fintype.one_lt_card (α := K)
      rw [hcard, h] at hlt
      simp at hlt
    · exact h
  have h2s : ¬ n ∣ 2 * s := fun hd => h4 (by
    have := dvd_mul_of_dvd_right hd 2
    rwa [show 2 * (2 * s) = 4 * s by ring] at this)
  obtain ⟨lam0, hlam0, -⟩ := frobExpansion (E := K) (d := n) hcard (AddMonoidHom.mk' f hf)
  obtain ⟨mu0, hmu0, -⟩ := frobExpansion (E := K) (d := n) hcard (AddMonoidHom.mk' g hg)
  set lam : ℕ → K := fun a => lam0 ⟨a % n, Nat.mod_lt a hn⟩ with hlamdef
  set mu : ℕ → K := fun a => mu0 ⟨a % n, Nat.mod_lt a hn⟩ with hmudef
  have hf' : ∀ x, f x = ∑ i ∈ Finset.range n, lam i * x ^ (2 ^ i) := by
    intro x
    show (AddMonoidHom.mk' f hf) x = ∑ i ∈ Finset.range n, lam i * x ^ (2 ^ i)
    rw [hlam0 x, ← Fin.sum_univ_eq_sum_range (fun i => lam i * x ^ (2 ^ i)) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hli : lam (i : ℕ) = lam0 i := by
      simp only [hlamdef]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hli]
  have hg' : ∀ x, g x = ∑ i ∈ Finset.range n, mu i * x ^ (2 ^ i) := by
    intro x
    show (AddMonoidHom.mk' g hg) x = ∑ i ∈ Finset.range n, mu i * x ^ (2 ^ i)
    rw [hmu0 x, ← Fin.sum_univ_eq_sum_range (fun i => mu i * x ^ (2 ^ i)) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmi : mu (i : ℕ) = mu0 i := by
      simp only [hmudef]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hmi]
  obtain ⟨hrel1, hrel2, hrel3⟩ := relationsFromIdentity hcard hsn hs0 h4 lam mu f g hf' hg' hid
  have hne : ∃ k < n, lam k ≠ 0 := by
    obtain ⟨x, hx⟩ := hfnz
    by_contra h
    push_neg at h
    apply hx
    rw [hf' x]
    exact Finset.sum_eq_zero fun i hi => by rw [h i (Finset.mem_range.mp hi), zero_mul]
  obtain ⟨i0, hi0lt, hi0ne, hsupp⟩ := supportSingleton hsn hs0 h4 lam hne hrel1 hrel3
  have hs_ne : (i0 + s) % n ≠ i0 := by
    intro heq
    have hm : Nat.ModEq n i0 (i0 + s) := by
      show i0 % n = (i0 + s) % n
      rw [Nat.mod_eq_of_lt hi0lt, heq]
    have hd : n ∣ s := by
      have := (Nat.modEq_iff_dvd' (by omega : i0 ≤ i0 + s)).mp hm
      rwa [show (i0 + s) - i0 = s by omega] at this
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hsn] at hd
    exact hs0 hd
  have hs_ne' : (i0 + n - s) % n ≠ i0 := by
    intro heq
    have hm : Nat.ModEq n i0 (i0 + n - s) := by
      show i0 % n = (i0 + n - s) % n
      rw [Nat.mod_eq_of_lt hi0lt, heq]
    have hd : n ∣ s := by
      have h1 := (Nat.modEq_iff_dvd' (by omega : i0 ≤ i0 + n - s)).mp hm
      have h2 : n ∣ n - s := by rwa [show (i0 + n - s) - i0 = n - s by omega] at h1
      have h3 := Nat.dvd_sub (dvd_refl n) h2
      rwa [show n - (n - s) = s by omega] at h3
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hsn] at hd
    exact hs0 hd
  have hmu_i0 : mu i0 = lam i0 * (lam i0) ^ (2 ^ s) := by
    have h := hrel2 i0 hi0lt
    have h1 : lam ((i0 + s) % n) = 0 :=
      hsupp _ (Nat.mod_lt _ hn) hs_ne
    have h2 : lam ((i0 + n - s) % n) = 0 :=
      hsupp _ (Nat.mod_lt _ hn) hs_ne'
    rw [h1, h2] at h
    simpa using h
  have hmu_zero : ∀ j < n, j ≠ i0 → mu j = 0 := by
    intro j hj hjne
    have h := hrel2 j hj
    rw [hsupp j hj hjne, zero_mul, zero_add] at h
    rw [h]
    by_cases hc : (j + s) % n = i0
    · refine mul_eq_zero.mpr (Or.inr ?_)
      rw [pow_eq_zero_iff']
      refine ⟨hsupp _ (Nat.mod_lt _ hn) ?_, by positivity⟩
      intro h2eq
      have hm1 : Nat.ModEq n (j + s) (j + n - s) := by
        show (j + s) % n = (j + n - s) % n
        rw [hc, h2eq]
      have hm2 : Nat.ModEq n j (j + 2 * s) := by
        have h3 := hm1.add_right s
        rw [show (j + s) + s = j + 2 * s by ring, show (j + n - s) + s = j + n by omega] at h3
        have h4 : Nat.ModEq n (j + n) j := by
          show (j + n) % n = j % n
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]
        exact (h3.trans h4).symm
      have hd : n ∣ 2 * s := by
        have := (Nat.modEq_iff_dvd' (by omega : j ≤ j + 2 * s)).mp hm2
        rwa [show (j + 2 * s) - j = 2 * s by omega] at this
      exact h2s hd
    · exact mul_eq_zero.mpr (Or.inl (hsupp _ (Nat.mod_lt _ hn) hc))
  refine ⟨lam i0, i0, hi0ne, hi0lt, ?_, ?_⟩
  · intro x
    have hsum : (∑ i ∈ Finset.range n, lam i * x ^ (2 ^ i)) = lam i0 * x ^ (2 ^ i0) :=
      Finset.sum_eq_single i0
        (fun j hj hji => by rw [hsupp j (Finset.mem_range.mp hj) hji, zero_mul])
        (fun hnot => absurd (Finset.mem_range.mpr hi0lt) hnot)
    rw [hf' x, hsum]
  · intro z
    have hsum : (∑ i ∈ Finset.range n, mu i * z ^ (2 ^ i)) = mu i0 * z ^ (2 ^ i0) :=
      Finset.sum_eq_single i0
        (fun j hj hji => by rw [hmu_zero j (Finset.mem_range.mp hj) hji, zero_mul])
        (fun hnot => absurd (Finset.mem_range.mpr hi0lt) hnot)
    rw [hg' z, hsum, hmu_i0]

end Work.Hering.AppVIII
