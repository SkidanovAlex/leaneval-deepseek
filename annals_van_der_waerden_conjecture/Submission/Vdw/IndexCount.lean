import Mathlib
import Submission.Vdw.CaseIIClasses
import Submission.Vdw.SchmidtCount
import Submission.Vdw.CaseIDisc
import Submission.Vdw.CaseISmallPrime
import Submission.Vdw.PolyIndex
import Submission.Vdw.ResidueCompare
import Submission.Vdw.SquarefullSum
import Submission.Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le
import Submission.Commons.NumberTheory.Nat.pow_omega_le_const_mul_rpow
import Submission.Commons.Data.Set.ncard_le_prod_of_chain
import Submission.Commons.NumberTheory.Nat.ncard_squarefull_le_sqrt
import Submission.Commons.NumberTheory.Nat.prod_Icc_filter_factorization
import Submission.Commons.NumberTheory.Int.ncard_abs_le_modEq
import Submission.Commons.Data.Set.ncard_eq_natCard
import Submission.Commons.NumberTheory.Nat.pow_prod_filter_factorization_dvd
import Submission.Commons.NumberTheory.Nat.sq_prod_filter_primeFactors_dvd
import Submission.Commons.NumberTheory.Nat.two_mul_sub_one_le_mul
import Submission.Commons.NumberTheory.Nat.cast_half_mul_sub_one_div
import Submission.Commons.NumberTheory.Nat.sq_dvd_le_rpow_mul
import Submission.Commons.NumberTheory.Nat.pow_dvd_le_rpow_mul
import Submission.Commons.Analysis.Real.prod_range_pow_mul_rpow
-- PENDING import Submission.Commons.Analysis.Real.prod_ceil_natCast_le_prod_add_one

open Polynomial Filter Asymptotics
open scoped BigOperators NumberField Classical
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The index refinement: `FieldCountBound n (n/4 + ε)` (Bhargava, Thm. 1.2)

The Case-II field count with the exponent `β = (n+2)/4` is Schmidt's
(`SchmidtCount.fieldCountBound_schmidt`).  Bhargava's *index refinement*
(Theorem 1.2 of the Annals paper, resting on Proposition 4.x) improves it to
`β = (n+2)/4 − 1 + 1/ind(G) + ε`, which for a primitive `G ≠ Sₙ` (so
`ind(G) ≥ 2`) is `β = n/4 + ε`.

The proof counts, for each fixed discriminant `D`, the number of
discriminant-`D` fields appearing in the Case-II region:

* take the canonical trace-zero generator `α` of `K` with
  `house α ≪ |Disc|^{1/(2(n-1))}` (`SchmidtCount.exists_classPoly`), whose
  minimal polynomial `P = Xⁿ + a₂Xⁿ⁻² + … + aₙ` has `|aᵢ| ≪ D^{i/(2n-2)}`;
* for every prime `p > n` with `p | D`, Lemma 24
  (`ResidueCompare.lemma24_field_Kpoly`) gives `v_p(D) ≤ polyIndex(P mod p)`,
  so by Proposition 4.x
  (`Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le`) the
  coefficients `a_{n-j+1}, …, a_n` are determined modulo
  `D_j = ∏_{p : v_p(D) ≥ j} p` by `a₁, …, a_{n-j}` up to `C^{ω(D_j)}`
  possibilities;
* multiplying the ranges out gives `≪ C^{ω(D)} D^{(n+2)/4}/D_large`, where
  `D_large` is the part of `D` supported on primes `> n`.

Since `D = D_large · D_small` with `D_small ≤ primorial n ^ (n + n log₂ n)`
bounded (`CaseISmallPrime.discSmallPart_fieldDisc_le`), and since `D` is
squarefull (`CaseI.discr_squarefull_...`), this is
`≪ C_ε D^{(n+2)/4 - 1 + ε}`.  Summing over the `≪ √Y` squarefull `D ≤ Y`
yields `FieldCountBound n (n/4 + ε)`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## 1. The slicing moduli `D_j` -/

/-- The primes `p > n` dividing `D` with `v_p(D) ≥ j`. -/
def discJPrimes (n D j : ℕ) : Finset ℕ :=
  (Nat.primeFactors D).filter (fun p => n < p ∧ j ≤ D.factorization p)

/-- The `j`-th slicing modulus `D_j = ∏_{p | D, p > n, v_p(D) ≥ j} p`. -/
noncomputable def discJ (n D j : ℕ) : ℕ := ∏ p ∈ discJPrimes n D j, p

theorem discJ_eq_prod (n D j : ℕ) : discJ n D j = ∏ p ∈ discJPrimes n D j, p := rfl

theorem discJPrimes_subset_primeFactors (n D j : ℕ) :
    discJPrimes n D j ⊆ Nat.primeFactors D := Finset.filter_subset _ _

theorem discJPrimes_subset_filter (n D j : ℕ) :
    discJPrimes n D j ⊆ (Nat.primeFactors D).filter (fun p => n < p) := by
  intro p hp
  simp only [discJPrimes, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

theorem discJPrimes_antitone (n D : ℕ) {j j' : ℕ} (h : j ≤ j') :
    discJPrimes n D j' ⊆ discJPrimes n D j := by
  intro p hp
  simp only [discJPrimes, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, le_trans h hp.2.2⟩

theorem prime_of_mem_discJPrimes {n D j p : ℕ} (hp : p ∈ discJPrimes n D j) :
    Nat.Prime p :=
  Nat.prime_of_mem_primeFactors (discJPrimes_subset_primeFactors n D j hp)

theorem discJ_eq_indicator (n D j : ℕ) :
    discJ n D j = ∏ p ∈ Nat.primeFactors D,
      (if n < p ∧ j ≤ D.factorization p then p else 1) := by
  simp only [discJ, discJPrimes]
  rw [Finset.prod_filter]

theorem discLargePart_eq_indicator (n D : ℕ) :
    discLargePart n D = ∏ p ∈ Nat.primeFactors D, (if n < p then p ^ D.factorization p else 1) := by
  rw [discLargePart, Finset.prod_filter]

theorem discLargePart_pos (n D : ℕ) : 0 < discLargePart n D := by
  rw [discLargePart]
  refine Finset.prod_pos ?_
  intro p hp
  exact pow_pos (Nat.pos_of_ne_zero (Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_filter p hp)).ne_zero) _

theorem discJ_dvd_discLargePart (n D j : ℕ) : discJ n D j ∣ discLargePart n D := by
  rw [discJ_eq_indicator, discLargePart_eq_indicator]
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro p hp
  by_cases hQ : n < p ∧ j ≤ D.factorization p
  · rw [if_pos hQ, if_pos hQ.1]
    obtain ⟨hp_prime, hp_dvd, hp_ne⟩ := Nat.mem_primeFactors.mp hp
    have hpv : 0 < D.factorization p :=
      lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) ((hp_prime.dvd_iff_one_le_factorization hp_ne).mp hp_dvd)
    exact dvd_pow_self p hpv.ne'
  · rw [if_neg hQ]
    exact one_dvd _

theorem le_discJ (n D j : ℕ) : discJ n D j ≤ discLargePart n D :=
  Nat.le_of_dvd (discLargePart_pos n D) (discJ_dvd_discLargePart n D j)
/-! ## 2. Elementary counting lemmas -/

/-- Bhargava's index of the reduction of `P` modulo `p`. -/
noncomputable def polyIndexMod (p : ℕ) (hp : Nat.Prime p) (P : ℤ[X]) : ℕ :=
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  polyIndex (F := ZMod p) (P.map (Int.castRingHom (ZMod p)))

/-- A prime dividing a product of primes is one of them. -/
lemma prime_mem_of_dvd_prod {s : Finset ℕ} {a : ℕ} (ha : Nat.Prime a)
    (hs : ∀ p ∈ s, Nat.Prime p) (h : a ∣ ∏ p ∈ s, p) : a ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp at h
    have := ha.two_le
    omega
  | insert b t hbt ih =>
    rw [Finset.prod_insert hbt] at h
    rcases ha.dvd_mul.mp h with h1 | h2
    · have hb : Nat.Prime b := hs b (Finset.mem_insert_self b t)
      have : a = b := (Nat.prime_dvd_prime_iff_eq ha hb).mp h1
      rw [this]
      exact Finset.mem_insert_self b t
    · exact Finset.mem_insert_of_mem (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp)) h2)

/-- Coprimality of a prime with a product of primes not containing it. -/
lemma coprime_prod_primes {s : Finset ℕ} {a : ℕ} (ha : Nat.Prime a)
    (hs : ∀ p ∈ s, Nat.Prime p) (has : a ∉ s) : Nat.Coprime a (∏ p ∈ s, p) :=
  (ha.coprime_iff_not_dvd).mpr fun h => has (prime_mem_of_dvd_prod ha hs h)

/-- If every prime of a finite set divides `m`, so does the product. -/
lemma prod_dvd_of_prime_dvd {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) {m : ℤ}
    (h : ∀ p ∈ s, (p : ℤ) ∣ m) : ((∏ p ∈ s, p : ℕ) : ℤ) ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b t hbt ih =>
    rw [Finset.prod_insert hbt, Nat.cast_mul]
    refine IsCoprime.mul_dvd ?_ (h b (Finset.mem_insert_self b t))
      (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
        (fun p hp => h p (Finset.mem_insert_of_mem hp)))
    exact Nat.isCoprime_iff_coprime.mpr (coprime_prod_primes (hs b (Finset.mem_insert_self b t))
      (fun p hp => hs p (Finset.mem_insert_of_mem hp)) hbt)

/-- Cardinality of a union of fibres. -/
lemma ncard_le_ncard_image_mul {α β : Type*} (f : α → β) (A : Set α) (hA : A.Finite) (K : ℕ)
    (h : ∀ b : β, ({a ∈ A | f a = b} : Set α).ncard ≤ K) : A.ncard ≤ (f '' A).ncard * K := by
  classical
  have hcard := Finset.card_le_card_image_mul hA.toFinset f K (fun b => by
    have h1 : (hA.toFinset.filter (fun a => f a = b)).card =
        ({a ∈ A | f a = b} : Set α).ncard := by
      rw [Set.ncard_eq_toFinset_card _ (hA.subset (fun a ha => by
        simp only [Set.mem_setOf_eq] at ha; exact ha.1))]
      congr 1
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [h1]
    exact h b)
  have h1 : (Finset.image f hA.toFinset).card = (f '' A).ncard := by
    rw [← Set.ncard_coe_finset (Finset.image f hA.toFinset)]
    congr 1
    ext b
    simp only [Finset.mem_coe, Finset.mem_image, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, (Set.Finite.mem_toFinset hA).mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, (Set.Finite.mem_toFinset hA).mpr ha, rfl⟩
  rw [← Set.ncard_eq_toFinset_card _ hA, h1] at hcard
  exact hcard

/-- The set of monic degree-`n` polynomials with prescribed top coefficients and
index at least `k` is finite over a finite field. -/
noncomputable def fintype_prefix_index_set (F : Type) [Field F] [DecidableEq F] [Finite F] (n ℓ : ℕ)
    (hℓn : ℓ ≤ n) (x : Fin ℓ → F) (k : ℕ) :
    Fintype {P : F[X] // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin ℓ, P.coeff (n - 1 - (i : ℕ)) = x i) ∧ k ≤ polyIndex P} := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  refine Fintype.ofInjective (fun P : {P : F[X] // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin ℓ, P.coeff (n - 1 - (i : ℕ)) = x i) ∧ k ≤ polyIndex P} =>
      fun i : Fin (n + 1) => P.1.coeff i) ?_
  intro P Q h
  exact Subtype.ext (Polynomial.ext (fun i => by
    by_cases hi : i ≤ n
    · exact congrFun h ⟨i, by omega⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [P.2.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Q.2.2.1]; omega)]))

/-- Bhargava's Proposition 4.x in *prefix* form: if a suffix of the top
coefficients (positions `n-1, …, n-ℓ`, with `ℓ ≥ n-k`) is prescribed and the
index is at least `k ≤ n`, there are at most `(n+1)·n!·2ⁿ` such monic
degree-`n` polynomials over a finite field of characteristic prime to `n!`. -/
theorem ncard_prefix_index_le (F : Type) [Field F] [DecidableEq F] [Finite F] (n k ℓ : ℕ)
    (hk : k ≤ n) (hchar : (Nat.factorial n : F) ≠ 0) (hℓn : ℓ ≤ n) (hℓ : n - k ≤ ℓ)
    (x : Fin ℓ → F) :
    Nat.card {P : F[X] // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin ℓ, P.coeff (n - 1 - (i : ℕ)) = x i) ∧ k ≤ polyIndex P}
      ≤ (n + 1) * Nat.factorial n * 2 ^ n := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  set a : Fin (n - k) → F := fun j => x ⟨n - 1 - (k + (j : ℕ)), by
    have hj : (j : ℕ) < n - k := j.isLt
    omega⟩ with ha
  set T := {P : F[X] // P.Monic ∧ P.natDegree = n ∧
      (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = a i) ∧
      k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} with hT
  haveI : Fintype T := by
    refine Fintype.ofInjective (fun P : T => fun i : Fin (n + 1) => P.1.coeff i) ?_
    intro P Q h
    exact Subtype.ext (Polynomial.ext (fun i => by
      by_cases hi : i ≤ n
      · exact congrFun h ⟨i, by omega⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [P.2.2.1]; omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Q.2.2.1]; omega)]))
  have hTcard : Nat.card T ≤ (n + 1) * Nat.factorial n * 2 ^ n := by
    have h := Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le F n k hk hchar a
    rw [hT]
    exact h
  let g : {P : F[X] // P.Monic ∧ P.natDegree = n ∧
      (∀ i : Fin ℓ, P.coeff (n - 1 - (i : ℕ)) = x i) ∧ k ≤ polyIndex P} → T :=
    fun P => ⟨P.1, P.2.1, P.2.2.1, (fun i => by
      have hi : (k + (i : ℕ)) = n - 1 - (⟨n - 1 - (k + (i : ℕ)), by
        have hi' : (i : ℕ) < n - k := i.isLt
        omega⟩ : Fin ℓ) := by
        simp only
        omega
      rw [hi]
      exact P.2.2.2.1 _), (by
      have hpoly : polyIndex P.1
          = P.1.natDegree - (UniqueFactorizationMonoid.radical P.1).natDegree := rfl
      have h := P.2.2.2.2
      rw [hpoly, P.2.2.1] at h
      exact h)⟩
  have hg : Function.Injective g := fun P Q h => Subtype.ext (congrArg (fun x : T => x.1) h)
  exact le_trans (Nat.card_le_card_of_injective g hg) hTcard

/-! ## 3. The fibre chain -/

/-- **Abstract fibre-counting step.**  If for every prime `p ∈ σ` the residues of
the elements of a bounded set `A ⊆ ℤ` lie in a set `R p` of at most `C`
elements, then `#A ≤ C^{#σ}·(2B/M + 2)` where `M = ∏_{p ∈ σ} p`. -/
theorem fiber_le_of_residue_sets (σ : Finset ℕ) (hσ : ∀ p ∈ σ, Nat.Prime p) (M : ℕ)
    (hM : M = ∏ p ∈ σ, p)
    (A : Set ℤ) (hA : A.Finite) (B C : ℕ)
    (R : (p : {p // p ∈ σ}) → Finset (ZMod ((p : {p // p ∈ σ}) : ℕ)))
    (hR : ∀ p, (R p).card ≤ C)
    (hAmem : ∀ a ∈ A, ∀ p : {p // p ∈ σ}, (a : ZMod ((p : {p // p ∈ σ}) : ℕ)) ∈ R p)
    (hAb : ∀ a ∈ A, |a| ≤ (B : ℤ)) :
    (A.ncard : ℝ) ≤ (C : ℝ) ^ σ.card * (2 * (B : ℝ) / (M : ℝ) + 2) := by
  classical
  set φ : ℤ → ((p : {p // p ∈ σ}) → ZMod ((p : {p // p ∈ σ}) : ℕ)) :=
    fun a p => (a : ZMod ((p : {p // p ∈ σ}) : ℕ)) with hφ
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact Finset.one_le_prod (fun p hp => (hσ p hp).one_le)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le one_pos hM1)
  -- the fibre bound
  have hK : ∀ r : (p : {p // p ∈ σ}) → ZMod ((p : {p // p ∈ σ}) : ℕ),
      ({a ∈ A | φ a = r} : Set ℤ).ncard ≤ ⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ := by
    intro r
    by_cases hne : ∃ a ∈ A, φ a = r
    · obtain ⟨a₀, ha₀A, ha₀⟩ := hne
      have hfin : ({a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq ((M : ℕ) : ℤ) a a₀} : Set ℤ).Finite :=
        (Set.finite_Icc (-(B : ℤ)) (B : ℤ)).subset (fun a ha => by
          simp only [Set.mem_setOf_eq, Set.mem_Icc] at ha ⊢
          exact abs_le.mp ha.1)
      have hsub : {a ∈ A | φ a = r} ⊆
          {a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq ((M : ℕ) : ℤ) a a₀} := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        refine ⟨hAb a ha.1, ?_⟩
        refine Int.modEq_iff_dvd.mpr ?_
        have hdvd : ∀ p ∈ σ, (p : ℤ) ∣ (a₀ - a) := by
          intro p hp
          have h1 : (a : ZMod p) = (a₀ : ZMod p) := by
            have h2 := congrFun (ha.2.trans ha₀.symm) ⟨p, hp⟩
            simpa [hφ] using h2
          exact (ZMod.intCast_eq_intCast_iff_dvd_sub a a₀ p).mp h1
        have h2 := prod_dvd_of_prime_dvd (s := σ) hσ hdvd
        rw [← hM] at h2
        exact h2
      have h1 : (({a ∈ A | φ a = r} : Set ℤ).ncard : ℝ)
          ≤ (({a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq ((M : ℕ) : ℤ) a a₀} : Set ℤ).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      have h2 : (({a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq ((M : ℕ) : ℤ) a a₀} : Set ℤ).ncard : ℝ)
          ≤ 2 * (B : ℝ) / (M : ℝ) + 1 :=
        Commons.NumberTheory.Int.ncard_abs_le_modEq B M hM1 a₀
      have h3 : (({a : ℤ | |a| ≤ (B : ℤ) ∧ Int.ModEq ((M : ℕ) : ℤ) a a₀} : Set ℤ).ncard : ℝ)
          ≤ (⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ : ℝ) :=
        le_trans h2 (Nat.le_ceil _)
      exact_mod_cast le_trans h1 h3
    · push_neg at hne
      have hemp : {a ∈ A | φ a = r} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact hne a
      rw [hemp, Set.ncard_empty]
      exact Nat.zero_le _
  -- the image bound
  have himg : ((φ '' A).ncard : ℝ) ≤ (C : ℝ) ^ σ.card := by
    have hsub : φ '' A ⊆
        (↑(Fintype.piFinset R) : Set ((p : {p // p ∈ σ}) → ZMod ((p : {p // p ∈ σ}) : ℕ))) := by
      rintro r ⟨a, haA, rfl⟩
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      exact hAmem a haA
    have h1 : (φ '' A).ncard ≤ ∏ q : {q // q ∈ σ}, (R q).card := by
      calc (φ '' A).ncard ≤
            (↑(Fintype.piFinset R) : Set
              ((p : {p // p ∈ σ}) → ZMod ((p : {p // p ∈ σ}) : ℕ))).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (Fintype.piFinset R).card := Set.ncard_coe_finset _
        _ = ∏ q : {q // q ∈ σ}, (R q).card := Fintype.card_piFinset R
    have h2 : (∏ q : {q // q ∈ σ}, (R q).card) ≤ ∏ _q : {q // q ∈ σ}, C :=
      Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun q _ => hR q)
    have h3 : (∏ _q : {q // q ∈ σ}, C) = C ^ σ.card := by
      rw [Finset.prod_const]
      congr 1
      simp [Finset.card_univ, Fintype.card_coe]
    calc ((φ '' A).ncard : ℝ) ≤ ((∏ q : {q // q ∈ σ}, (R q).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ ((∏ _q : {q // q ∈ σ}, C : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (C : ℝ) ^ σ.card := by rw [h3]; push_cast; ring
  have hmain := ncard_le_ncard_image_mul φ A hA ⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ hK
  have hfib' : (⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ : ℝ) ≤ 2 * (B : ℝ) / (M : ℝ) + 2 := by
    have h2 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * (B : ℝ) / (M : ℝ) + 1 by positivity)
    have h3 : ((⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ : ℕ) : ℝ) < 2 * (B : ℝ) / (M : ℝ) + 1 + 1 := h2
    linarith
  calc (A.ncard : ℝ) ≤ (((φ '' A).ncard * ⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast hmain
    _ = ((φ '' A).ncard : ℝ) * (⌈2 * (B : ℝ) / (M : ℝ) + 1⌉₊ : ℝ) := by push_cast; ring
    _ ≤ (C : ℝ) ^ σ.card * (2 * (B : ℝ) / (M : ℝ) + 2) := by
        exact mul_le_mul himg hfib' (Nat.cast_nonneg _) (by positivity)

/-! ## 4. The residue-set bound (Proposition 4.x in the count) -/

/-- For a monic polynomial of positive degree over a field, the index is at most
`deg - 1` (the radical has positive degree). -/
lemma polyIndex_le_natDegree_sub_one {F : Type*} [Field F] [DecidableEq F] (P : F[X])
    (hP : P.Monic) (hd : 0 < P.natDegree) : polyIndex P ≤ P.natDegree - 1 := by
  rw [polyIndex]
  have hne : UniqueFactorizationMonoid.radical P ≠ 1 := by
    intro h
    rcases (UniqueFactorizationMonoid.radical_eq_one_iff).mp h with h0 | hu
    · exact hP.ne_zero h0
    · rcases (Polynomial.isUnit_iff).mp hu with ⟨r, -, hr⟩
      rw [← hr, Polynomial.natDegree_C] at hd
      omega
  have hmono : (UniqueFactorizationMonoid.radical P).Monic := by
    rw [← monicRadical_eq_radical (F := F)]
    exact monicRadical_monic P
  have hge : 1 ≤ (UniqueFactorizationMonoid.radical P).natDegree := by
    by_contra h
    have h0 : (UniqueFactorizationMonoid.radical P).natDegree = 0 := by omega
    have h1 : (UniqueFactorizationMonoid.radical P).coeff 0 = 1 := by
      have := hmono.leadingCoeff
      rwa [Polynomial.leadingCoeff, h0] at this
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, h1, Polynomial.C_1] at hne
    exact hne rfl
  omega

/-- The coefficient bound for `coeff i` of the canonical polynomial of a class
of discriminant `D`. -/
noncomputable def cBnd (n D i : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (2 ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i)

/-- The candidate polynomials for degree-`n` fields of discriminant `D` inside
the Case-II region: monic of degree `n`, trace-zero top coefficient, coefficients
bounded by `cBnd`, and `v_p(D) ≤ polyIndex(P mod p)` at every prime `p > n`
dividing `D` (Lemma 24). -/
def GoodPoly (n D : ℕ) : Set ℤ[X] :=
  {P | P.Monic ∧ P.natDegree = n ∧ P.coeff (n - 1) = 0 ∧
       (∀ i, i ≤ n → i ≠ n - 1 → |((P.coeff i : ℤ) : ℝ)| ≤ cBnd n D i) ∧
       (∀ (p : ℕ) (hp : Nat.Prime p), n < p → p ∣ D →
          padicValNat p D ≤ polyIndexMod p hp P)}

/-- **The residue set at a prime `p ∈ D_{n-k}` has at most `C` elements.**  The
reductions of the candidate polynomials with a prescribed prefix form a subset
of the Proposition 4.x set, so their values at the next coefficient lie in a set
of at most `(n+1)·n!·2ⁿ` residues. -/
theorem residueSet_card_le (n D k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n - 1)
    (x : Fin k → ℤ) (p : ℕ) (hp : Nat.Prime p) (hpn : n < p) (hpd : p ∣ D)
    (hkp : n - k ≤ D.factorization p) (hknp : D.factorization p ≤ n)
    (S : Set ℤ[X]) (hS : ∀ P ∈ S, P.Monic ∧ P.natDegree = n)
    (hidx : ∀ P ∈ S, ∀ (q : ℕ) (hq : Nat.Prime q), n < q → q ∣ D →
        padicValNat q D ≤ polyIndexMod q hq P) :
    Set.ncard {y : ZMod p | ∃ P ∈ S,
        (∀ i : Fin k, (P.coeff (n - 1 - (i : ℕ)) : ZMod p) = (x i : ZMod p)) ∧
        (P.coeff (n - 1 - k) : ZMod p) = y}
      ≤ (n + 1) * Nat.factorial n * 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hkn' : k ≤ n := by omega
  have hchar : (Nat.factorial n : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ Nat.factorial n :=
      (CharP.cast_eq_zero_iff (ZMod p) p (Nat.factorial n)).mp h
    have := (hp.dvd_factorial).mp hdvd
    omega
  set kp := D.factorization p with hkpdef
  set xZ : Fin k → ZMod p := fun i => ((x i : ℤ) : ZMod p) with hxZ
  set T : Set (ZMod p)[X] := {Q : (ZMod p)[X] | Q.Monic ∧ Q.natDegree = n ∧
      (∀ i : Fin k, Q.coeff (n - 1 - (i : ℕ)) = xZ i) ∧ kp ≤ polyIndex Q} with hT
  set cf : (ZMod p)[X] → ZMod p := fun Q => Q.coeff (n - 1 - k) with hcf
  have hTcard : Nat.card {Qq : (ZMod p)[X] // Qq.Monic ∧ Qq.natDegree = n ∧
      (∀ i : Fin k, Qq.coeff (n - 1 - (i : ℕ)) = xZ i) ∧ kp ≤ polyIndex Qq}
      ≤ (n + 1) * Nat.factorial n * 2 ^ n :=
    ncard_prefix_index_le (ZMod p) n kp k hknp hchar hkn' (by omega) xZ
  have hsub : {y : ZMod p | ∃ P ∈ S,
        (∀ i : Fin k, (P.coeff (n - 1 - (i : ℕ)) : ZMod p) = (x i : ZMod p)) ∧
        (P.coeff (n - 1 - k) : ZMod p) = y}
      ⊆ cf '' T := by
    rintro y ⟨P, hPS, hpre, hy⟩
    refine ⟨P.map (Int.castRingHom (ZMod p)), ?_, ?_⟩
    · refine ⟨(hS P hPS).1.map _, ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
        · exact (hS P hPS).2
        · rw [(hS P hPS).1.leadingCoeff]
          simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
      · intro i
        rw [Polynomial.coeff_map, hxZ]
        exact hpre i
      · show kp ≤ polyIndex (P.map (Int.castRingHom (ZMod p)))
        rw [hkpdef, Nat.factorization_def D hp]
        exact hidx P hPS p hp hpn hpd
    · show cf (P.map (Int.castRingHom (ZMod p))) = y
      simp only [hcf]
      rw [Polynomial.coeff_map]
      exact hy
  haveI : Fintype ↥T := fintype_prefix_index_set (ZMod p) n k hkn' xZ kp
  have hTile : T.Finite := Set.toFinite T
  refine le_trans (Set.ncard_le_ncard hsub (hTile.image cf)) ?_
  refine le_trans (Set.ncard_image_le (f := cf) hTile) ?_
  rw [Commons.Data.Set.ncard_eq_natCard]
  exact hTcard

/-! ## 5. The per-discriminant field count -/

/-- The canonical polynomial of a class of the Case-II region lies in
`GoodPoly n (classDisc q)`: it is monic, trace-zero, coefficient-bounded, and
satisfies Lemma 24 at every tame ramified prime. -/
theorem classPoly_mem_goodPoly (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n)
    (q : Quotient (fieldIsoSetoid n H hn)) :
    classPoly n H hn hnn q ∈ GoodPoly n (classDisc n H hn q) := by
  classical
  obtain ⟨hPmonic, hPdeg, hPnext, hPbdd, hwit⟩ := classPoly_spec n H hn hnn q
  obtain ⟨y, hygen, hymin⟩ := hwit
  haveI hIrr : Fact (Irreducible (((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]).map φℚ)) :=
    ⟨subcaseI_P2_irreducible n H hn (Quotient.out q)⟩
  haveI hIrrP : Fact (Irreducible ((classPoly n H hn hnn q).map φℚ)) := by
    have hyintq : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
    rw [← hymin]
    exact ⟨minpoly.irreducible hyintq⟩
  -- integrality of the generator over ℤ
  have hyint : IsIntegral ℤ y := by
    refine ⟨classPoly n H hn hnn q, hPmonic, ?_⟩
    have h1 : (Polynomial.aeval y) (minpoly ℚ y) = 0 := minpoly.aeval ℚ y
    have h2 : minpoly ℚ y = (classPoly n H hn hnn q).map φℚ := hymin
    rw [h2] at h1
    have h3 : (Polynomial.aeval y)
        ((classPoly n H hn hnn q).map (algebraMap ℤ ℚ)) = 0 := by
      simpa only [φℚ] using h1
    rw [Polynomial.aeval_map_algebraMap (A := ℚ) y (classPoly n H hn hnn q)] at h3
    exact h3
  -- the associated element of the ring of integers
  have hθy : ((IsIntegralClosure.mk' (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])))
      y hyint : 𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) :
      Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) = y :=
    IsIntegralClosure.algebraMap_mk' _ y hyint
  -- the minimal polynomial of the integral generator
  have hminθ : minpoly ℤ (IsIntegralClosure.mk' (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])))
      y hyint) = classPoly n H hn hnn q := by
    have h1 : minpoly ℤ y = classPoly n H hn hnn q := by
      have h2 := minpoly.isIntegrallyClosed_eq_field_fractions ℚ
        (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) hyint
      have h2' : minpoly ℚ y = Polynomial.map φℚ (minpoly ℤ y) := by
        simpa only [Algebra.algebraMap_self_apply, φℚ] using h2
      have h4 : Polynomial.map φℚ (minpoly ℤ y) = Polynomial.map φℚ (classPoly n H hn hnn q) :=
        h2'.symm.trans hymin
      exact (Polynomial.map_injective φℚ (fun a b h => by simpa [φℚ] using h) h4.symm).symm
    rw [← h1]
    have h3 := minpoly.algebraMap_eq
      (B := 𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])))
      (B' := Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))
      (A := ℤ) (IsIntegralClosure.algebraMap_injective
        (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) ℤ
        (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])))
      (IsIntegralClosure.mk' (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) y hyint)
    exact h3.symm.trans (congrArg (minpoly ℤ) hθy)
  -- finrank
  have hfin : Module.finrank ℚ (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) = n := by
    have hbox : ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]) ∈ Box n H :=
      subcaseI_P2_subset_Box n H (Quotient.out q).2
    exact finrank_Kpoly hbox.1 (Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1)
  refine ⟨hPmonic, hPdeg, hPnext, ?_, ?_⟩
  · intro i hi hne
    rw [cBnd, classDisc_out n H hn q]
    exact hPbdd i hi hne
  · intro p hp hpn hpd
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hgt : Module.finrank ℚ (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) < p := by
      rw [hfin]; exact hpn
    have hdeg : 1 ≤ (minpoly ℤ (IsIntegralClosure.mk'
        (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) y hyint)).natDegree := by
      rw [hminθ, hPdeg]; omega
    have hgen : (minpoly ℤ (IsIntegralClosure.mk'
        (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) y hyint)).natDegree =
        Module.finrank ℚ (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])) := by
      rw [hminθ, hPdeg, hfin]
    have h24 := lemma24_field_index_ge_discrVal
      (K := Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))
      (IsIntegralClosure.mk' (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) y hyint)
      p hdeg hgen hgt
    rw [hminθ] at h24
    have hD : (NumberField.discr (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))).natAbs
        = classDisc n H hn q := by
      rw [classDisc_out n H hn q]
      rfl
    rw [hD] at h24
    exact h24

/-- The coefficient vectors of the candidate polynomials. -/
noncomputable def GoodVec (n D : ℕ) : Set (Fin n → ℤ) :=
  {v | ∃ P ∈ GoodPoly n D, ∀ i : Fin n, v i = P.coeff (n - 1 - (i : ℕ))}

/-- `GoodVec n D` is finite (the coefficients are bounded). -/
lemma finite_goodVec (n D : ℕ) : (GoodVec n D).Finite := by
  classical
  refine Set.Finite.subset (Set.Finite.pi (fun i : Fin n => Set.finite_Icc
    (-(⌈cBnd n D (n - 1 - (i : ℕ))⌉₊ : ℤ) - 1) ⌈cBnd n D (n - 1 - (i : ℕ))⌉₊)) ?_
  rintro v ⟨P, hP, hv⟩
  rw [Set.mem_pi]
  intro i _
  rw [hv i]
  have hb := hP.2.2.1
  by_cases hcase : (n - 1 - (i : ℕ)) = n - 1
  · rw [hcase, hb]
    have h1 : (0 : ℝ) ≤ cBnd n D (n - 1 - (i : ℕ)) := by
      rw [hcase, cBnd]; positivity
    have h2 : (0 : ℤ) ≤ (⌈cBnd n D (n - 1 - (i : ℕ))⌉₊ : ℤ) := Int.natCast_nonneg _
    simp only [Set.mem_Icc, abs_nonpos_iff]
    constructor <;> omega
  · have hle : (P.coeff (n - 1 - (i : ℕ)) : ℝ) ≤ cBnd n D (n - 1 - (i : ℕ)) := by
      have := hP.2.2.2.1 (n - 1 - (i : ℕ)) (by omega) hcase
      exact (abs_le.mp this).2
    have hge : -(cBnd n D (n - 1 - (i : ℕ))) ≤ (P.coeff (n - 1 - (i : ℕ)) : ℝ) := by
      have := hP.2.2.2.1 (n - 1 - (i : ℕ)) (by omega) hcase
      exact (abs_le.mp this).1
    have h3 : ((P.coeff (n - 1 - (i : ℕ)) : ℤ) : ℝ) ≤ (⌈cBnd n D (n - 1 - (i : ℕ))⌉₊ : ℝ) :=
      le_trans hle (Nat.le_ceil _)
    have h4 : (-(⌈cBnd n D (n - 1 - (i : ℕ))⌉₊ : ℤ) - 1 : ℝ) ≤
        ((P.coeff (n - 1 - (i : ℕ)) : ℤ) : ℝ) := by
      have : -(cBnd n D (n - 1 - (i : ℕ))) ≤ (P.coeff (n - 1 - (i : ℕ)) : ℝ) := hge
      have h5 : (-(⌈cBnd n D (n - 1 - (i : ℕ))⌉₊ : ℤ) - 1 : ℝ) ≤
          -(cBnd n D (n - 1 - (i : ℕ))) := by
        push_cast
        have := Nat.le_ceil (cBnd n D (n - 1 - (i : ℕ)))
        linarith
      linarith
    simp only [Set.mem_Icc]
    constructor
    · exact_mod_cast h4
    · exact_mod_cast h3

/-- The classes of discriminant `D` inject into `GoodVec n D`. -/
lemma classCount_le_goodVec (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n) (D : ℕ) :
    Nat.card {q : Quotient (fieldIsoSetoid n H hn) // classDisc n H hn q = D}
      ≤ (GoodVec n D).ncard := by
  classical
  haveI : Fintype ↥(SubcaseI_P2 n H) := ((box_finite n H).subset (subcaseI_P2_subset_Box n H)).fintype
  haveI : Fintype (Quotient (fieldIsoSetoid n H hn)) := Quotient.fintype _
  haveI : Finite ↥(GoodVec n D) := (finite_goodVec n D).fintype.finite
  refine Nat.card_le_card_of_injective
    (fun q : {q : Quotient (fieldIsoSetoid n H hn) // classDisc n H hn q = D} =>
      (⟨fun i : Fin n => (classPoly n H hn hnn q.1).coeff (n - 1 - (i : ℕ)),
        ⟨classPoly n H hn hnn q.1,
          by simpa only [q.2] using classPoly_mem_goodPoly n H hn hnn q.1,
          fun i => rfl⟩⟩ : ↥(GoodVec n D))) ?_
  intro q₁ q₂ h
  have hv : (fun i : Fin n => (classPoly n H hn hnn q₁.1).coeff (n - 1 - (i : ℕ)))
      = fun i : Fin n => (classPoly n H hn hnn q₂.1).coeff (n - 1 - (i : ℕ)) :=
    congrArg Subtype.val h
  have hpoly : classPoly n H hn hnn q₁.1 = classPoly n H hn hnn q₂.1 := by
    refine Polynomial.ext (fun i => ?_)
    by_cases hi : i ≤ n - 1
    · have h2 := congrFun hv ⟨n - 1 - i, by omega⟩
      simp only at h2
      rw [show n - 1 - (n - 1 - i) = i by omega] at h2
      exact h2
    · by_cases h1 : i = n
      · rw [h1]
        have e1 : (classPoly n H hn hnn q₁.1).coeff n = 1 := by
          have h2 : (classPoly n H hn hnn q₁.1).coeff (classPoly n H hn hnn q₁.1).natDegree = 1 := by
            rw [Polynomial.coeff_natDegree, (classPoly_monic n H hn hnn q₁.1).leadingCoeff]
          rwa [classPoly_natDegree n H hn hnn q₁.1] at h2
        have e2 : (classPoly n H hn hnn q₂.1).coeff n = 1 := by
          have h2 : (classPoly n H hn hnn q₂.1).coeff (classPoly n H hn hnn q₂.1).natDegree = 1 := by
            rw [Polynomial.coeff_natDegree, (classPoly_monic n H hn hnn q₂.1).leadingCoeff]
          rwa [classPoly_natDegree n H hn hnn q₂.1] at h2
        rw [e1, e2]
      · have h2 : n < i := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [classPoly_natDegree n H hn hnn q₁.1]; omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [classPoly_natDegree n H hn hnn q₂.1]; omega)]
  exact Subtype.ext (classPoly_inj n H hn hnn hpoly)

/-- The prime exponents of the discriminant of a `GoodPoly` member are at most `n-1`
at every tame ramified prime. -/
lemma GoodPoly_factorization_le (n D : ℕ) (hD : 1 ≤ D) (hn : 1 ≤ n) {p : ℕ}
    (hp : Nat.Prime p) (hpn : n < p) (hpd : p ∣ D) (hne : (GoodPoly n D).Nonempty) :
    D.factorization p ≤ n - 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨P, hP⟩ := hne
  have h1 : padicValNat p D ≤ polyIndex (F := ZMod p)
      (P.map (Int.castRingHom (ZMod p))) := hP.2.2.2.2 p hp hpn hpd
  rw [Nat.factorization_def D hp]
  refine le_trans h1 ?_
  have hmapdeg : (P.map (Int.castRingHom (ZMod p))).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
    · exact hP.2.1
    · rw [hP.1.leadingCoeff]
      simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hmono : (P.map (Int.castRingHom (ZMod p))).Monic := hP.1.map _
  have hpos : 0 < (P.map (Int.castRingHom (ZMod p))).natDegree := by rw [hmapdeg]; omega
  exact le_trans (polyIndex_le_natDegree_sub_one _ hmono hpos) (le_of_eq (by rw [hmapdeg]))

/-- Natural-number form of the abstract fibre-counting step. -/
theorem fiber_le_of_residue_sets_nat (σ : Finset ℕ) (hσ : ∀ p ∈ σ, Nat.Prime p) (M : ℕ)
    (hM : M = ∏ p ∈ σ, p)
    (A : Set ℤ) (hA : A.Finite) (B C : ℕ)
    (R : (p : {p // p ∈ σ}) → Finset (ZMod ((p : {p // p ∈ σ}) : ℕ)))
    (hR : ∀ p, (R p).card ≤ C)
    (hAmem : ∀ a ∈ A, ∀ p : {p // p ∈ σ}, (a : ZMod ((p : {p // p ∈ σ}) : ℕ)) ∈ R p)
    (hAb : ∀ a ∈ A, |a| ≤ (B : ℤ)) :
    A.ncard ≤ C ^ σ.card * ⌈2 * (B : ℝ) / (M : ℝ) + 2⌉₊ := by
  have h := fiber_le_of_residue_sets σ hσ M hM A hA B C R hR hAmem hAb
  have h2 : (2 * (B : ℝ) / (M : ℝ) + 2) ≤ ((⌈2 * (B : ℝ) / (M : ℝ) + 2⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have h3 : (A.ncard : ℝ) ≤ ((C ^ σ.card * ⌈2 * (B : ℝ) / (M : ℝ) + 2⌉₊ : ℕ) : ℝ) := by
    calc (A.ncard : ℝ) ≤ (C : ℝ) ^ σ.card * (2 * (B : ℝ) / (M : ℝ) + 2) := h
      _ ≤ (C : ℝ) ^ σ.card * ((⌈2 * (B : ℝ) / (M : ℝ) + 2⌉₊ : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((C ^ σ.card * ⌈2 * (B : ℝ) / (M : ℝ) + 2⌉₊ : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast h3

/-- The Finset of residues of the next coefficient of `GoodPoly` members with a
given prefix. -/
noncomputable def residueFinset (n D k : ℕ) (x : Fin k → ℤ) (p : ℕ) (hp : Nat.Prime p) :
    Finset (ZMod p) :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  Finset.univ.filter (fun y => ∃ P ∈ GoodPoly n D,
    (∀ i : Fin k, (P.coeff (n - 1 - (i : ℕ)) : ZMod p) = ((x i : ℤ) : ZMod p)) ∧
    (P.coeff (n - 1 - k) : ZMod p) = y)

/-- **The chain bound for `GoodVec`.** -/
theorem goodVec_ncard_le_prod (n D : ℕ) (hn : 3 ≤ n) (hD : 1 ≤ D)
    (hv : ∀ p : ℕ, Nat.Prime p → n < p → p ∣ D → D.factorization p ≤ n - 1) :
    (GoodVec n D).ncard ≤
      ∏ k ∈ Finset.range n,
        (if k = 0 then 1 else
          ((n + 1) * Nat.factorial n * 2 ^ n) ^ (discJPrimes n D (n - k)).card
            * ⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊) := by
  classical
  refine Commons.Data.Set.ncard_le_prod_of_chain (GoodVec n D) (finite_goodVec n D) _ ?_
  intro k hk x
  by_cases hk0 : k = 0
  · subst hk0
    have hsub : {y : ℤ | ∃ a ∈ GoodVec n D,
        (∀ i : Fin 0, a (Fin.castLE (Nat.le_of_lt hk) i) = x i) ∧ a ⟨0, hk⟩ = y} ⊆ {0} := by
      rintro y ⟨a, ha, -, hay⟩
      obtain ⟨P, hP, hva⟩ := ha
      have hb := hP.2.2.1
      have h0 : a ⟨0, hk⟩ = 0 := by
        rw [hva ⟨0, hk⟩]
        simpa using hb
      rw [← hay, h0]
      exact Set.mem_singleton 0
    have hc := Set.ncard_le_ncard hsub (Set.finite_singleton (0 : ℤ))
    simp only [Set.ncard_singleton] at hc
    simpa using hc
  · have hk1 : 1 ≤ k := by omega
    have hkn : k ≤ n - 1 := by omega
    have hn1 : 1 ≤ n := by omega
    set A : Set ℤ := {y : ℤ | ∃ a ∈ GoodVec n D,
        (∀ i : Fin k, a (Fin.castLE (Nat.le_of_lt hk) i) = x i) ∧ a ⟨k, hk⟩ = y} with hAdef
    have hAeq : A = {y : ℤ | ∃ P ∈ GoodPoly n D,
        (∀ i : Fin k, P.coeff (n - 1 - (i : ℕ)) = x i) ∧ P.coeff (n - 1 - k) = y} := by
      ext y
      constructor
      · rintro ⟨a, ⟨P, hP, hva⟩, hpre, hay⟩
        refine ⟨P, hP, ?_, ?_⟩
        · intro i
          have h2 := hpre i
          rw [hva (Fin.castLE (Nat.le_of_lt hk) i)] at h2
          simpa [Fin.val_castLE] using h2
        · rw [← hay]
          exact (hva ⟨k, hk⟩).symm
      · rintro ⟨P, hP, hpre, hpy⟩
        refine ⟨fun i : Fin n => P.coeff (n - 1 - (i : ℕ)), ⟨P, hP, fun i => rfl⟩, ?_, ?_⟩
        · intro i
          simp only [Fin.val_castLE]
          exact hpre i
        · simpa using hpy
    have hfin : A.Finite := by
      rw [hAeq]
      refine Set.Finite.subset ((finite_goodVec n D).image (fun a : Fin n → ℤ => a ⟨k, hk⟩)) ?_
      rintro y ⟨P, hP, -, hpy⟩
      refine ⟨(fun i : Fin n => P.coeff (n - 1 - (i : ℕ))), ⟨P, hP, fun i => rfl⟩, ?_⟩
      simpa using hpy
    -- the residue sets
    set R : (p : {p // p ∈ discJPrimes n D (n - k)}) →
        Finset (ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ)) :=
      fun p => residueFinset n D k x p.1 (prime_of_mem_discJPrimes p.2) with hRdef
    have hRcard : ∀ p : {p // p ∈ discJPrimes n D (n - k)},
        (R p).card ≤ (n + 1) * Nat.factorial n * 2 ^ n := by
      intro p
      by_cases hne : (GoodPoly n D).Nonempty
      · obtain ⟨hpD, hpn, hkp⟩ := Finset.mem_filter.mp p.2
        have hp : Nat.Prime p.1 := prime_of_mem_discJPrimes p.2
        have hpd : p.1 ∣ D := (Nat.mem_primeFactors.mp hpD).2.1
        have hknp : D.factorization p.1 ≤ n :=
          le_trans (GoodPoly_factorization_le n D hD hn1 hp hpn hpd hne) (by omega)
        have hset : (↑(R p) : Set (ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ)))
            = {y : ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ) |
                ∃ P ∈ GoodPoly n D,
                  (∀ i : Fin k, (P.coeff (n - 1 - (i : ℕ)) :
                      ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ))
                    = ((x i : ℤ) : ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ))) ∧
                  (P.coeff (n - 1 - k) : ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ)) = y} := by
          ext y
          simp only [Finset.mem_coe, hRdef, residueFinset, Finset.mem_filter, Finset.mem_univ,
            true_and, Set.mem_setOf_eq]
        rw [← Set.ncard_coe_finset (R p), hset]
        exact residueSet_card_le n D k hk1 hkn x p.1 hp hpn hpd hkp hknp
          (GoodPoly n D) (fun P hP => ⟨hP.1, hP.2.1⟩)
          (fun P hP q hq hnq hqd => hP.2.2.2.2 q hq hnq hqd)
      · have hempty : R p = ∅ := by
          rw [hRdef]
          refine Finset.filter_eq_empty_iff.mpr ?_
          intro y _
          simp only [not_exists, not_and]
          intro P hP
          exact absurd ⟨P, hP⟩ hne
        rw [hempty]
        simp
    have hAmem : ∀ a ∈ A, ∀ p : {p // p ∈ discJPrimes n D (n - k)},
        (a : ZMod ((p : {p // p ∈ discJPrimes n D (n - k)}) : ℕ)) ∈ R p := by
      intro a ha p
      rw [hAeq] at ha
      obtain ⟨P, hP, hpre, hpa⟩ := ha
      simp only [hRdef, residueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨P, hP, fun i => by rw [hpre i], by rw [hpa]⟩
    have hAb : ∀ a ∈ A, |a| ≤ ((⌈cBnd n D (n - 1 - k)⌉₊ : ℕ) : ℤ) := by
      intro a ha
      rw [hAeq] at ha
      obtain ⟨P, hP, hpre, hpa⟩ := ha
      rw [← hpa]
      have hb := hP.2.2.2.1 (n - 1 - k) (by omega) (by intro hc; omega)
      have h1 : ((P.coeff (n - 1 - k) : ℤ) : ℝ) ≤ (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) :=
        le_trans (abs_le.mp hb).2 (Nat.le_ceil _)
      have h2 : -(((⌈cBnd n D (n - 1 - k)⌉₊ : ℕ)) : ℝ) ≤ ((P.coeff (n - 1 - k) : ℤ) : ℝ) :=
        le_trans (neg_le_neg (Nat.le_ceil _)) (abs_le.mp hb).1
      exact abs_le.mpr ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    have hmain := fiber_le_of_residue_sets_nat (discJPrimes n D (n - k))
      (fun p hp => prime_of_mem_discJPrimes hp) (discJ n D (n - k)) (discJ_eq_prod n D (n - k))
      A hfin (⌈cBnd n D (n - 1 - k)⌉₊) ((n + 1) * Nat.factorial n * 2 ^ n) R hRcard hAmem hAb
    rw [if_neg hk0]
    exact hAdef ▸ hmain

/-- **The slicing modulus is bounded by the coefficient range.**  For
`1 ≤ j ≤ n-1` and a squarefull discriminant `D`, `discJ n D j ≤ cBnd n D (j-1)`
(the paper's `D_j ≪ D^{(n+1-j)/(2n-2)}`). -/
lemma discJ_le_cBnd (n D j : ℕ) (hn : 3 ≤ n) (hD : 1 ≤ D) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1)
    (hsq : ∀ p : ℕ, Nat.Prime p → p ∣ D → p ^ 2 ∣ D) :
    (discJ n D j : ℝ) ≤ cBnd n D (j - 1) := by
  have hn2 : 2 ≤ n := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  rw [cBnd]
  by_cases hj : j = 1
  · subst hj
    have h1 : discJ n D 1 = ∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p), p := by
      show ∏ p ∈ discJPrimes n D 1, p = _
      congr 1
      rw [discJPrimes]
      refine Finset.filter_congr ?_
      intro p hp
      constructor
      · intro h; exact h.1
      · intro h
        refine ⟨h, ?_⟩
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
        have hpd : p ∣ D := (Nat.mem_primeFactors.mp hp).2.1
        exact (hpp.dvd_iff_one_le_factorization (by omega : D ≠ 0)).mp hpd
    rw [h1]
    have hdvd := Commons.NumberTheory.Nat.sq_prod_filter_primeFactors_dvd n D hsq
    have h2 := Commons.NumberTheory.Nat.sq_dvd_le_rpow_mul n D
      (∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p), p) hn2 hD hdvd
    have h3 : (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ n *
        (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) = cBnd n D 0 := by
      rw [cBnd, Nat.sub_zero, mul_pow]
      have e2 : ((D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ n
          = (D : ℝ) ^ ((n : ℝ) / (2 * ((n : ℝ) - 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]
        congr 1
        push_cast
        rw [div_mul_eq_mul_div, one_mul]
      rw [e2]
      ring
    exact h2.trans (le_of_eq h3)
  · have hj2 : 2 ≤ j := by omega
    have hineq := Commons.NumberTheory.Nat.two_mul_sub_one_le_mul n j hn2 hj2 hjn
    have hdvd := Commons.NumberTheory.Nat.pow_prod_filter_factorization_dvd n D j
    have h2 := Commons.NumberTheory.Nat.pow_dvd_le_rpow_mul n j D (discJ n D j)
      (by omega : 1 ≤ n) hD hj2 (by omega : j ≤ n) hdvd hineq
    have h3 : (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6)) ^ (n + 1 - j) *
        (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) = cBnd n D (j - 1) := by
      rw [cBnd, mul_pow]
      have e1 : n - (j - 1) = n + 1 - j := by omega
      rw [e1]
      have e2 : ((D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n + 1 - j)
          = (D : ℝ) ^ (((n + 1 - j : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]
        congr 1
        push_cast
        rw [div_mul_eq_mul_div, one_mul]
      rw [e2]
      ring
    exact h2.trans (le_of_eq h3)

/-- The product of the slicing moduli over `j = 1, …, n-1` is the large-prime
part of `D`. -/
lemma prod_discJ_eq_discLargePart (n D : ℕ)
    (hv : ∀ p : ℕ, Nat.Prime p → n < p → p ∣ D → D.factorization p ≤ n - 1) :
    ∏ k ∈ Finset.Icc 1 (n - 1), discJ n D (n - k) = discLargePart n D := by
  classical
  have h1 : ∏ k ∈ Finset.Icc 1 (n - 1), discJ n D (n - k)
      = ∏ j ∈ Finset.Icc 1 (n - 1), discJ n D j := by
    refine Finset.prod_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k1 hk1 k2 hk2 h
      have h1 := (Finset.mem_Icc.mp hk1).2
      have h2 := (Finset.mem_Icc.mp hk2).2
      omega
    · intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      exact ⟨n - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; rfl
  rw [h1, Finset.prod_congr rfl (fun j _ => discJ_eq_prod n D j)]
  simp only [discJPrimes]
  rw [Commons.NumberTheory.Nat.prod_Icc_filter_factorization n D]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp' : p ∈ Nat.primeFactors D := (Finset.mem_filter.mp hp).1
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp').1
  have hpd : p ∣ D := (Nat.mem_primeFactors.mp hp').2.1
  have hpn : n < p := (Finset.mem_filter.mp hp).2
  rw [min_eq_left (hv p hpp hpn hpd)]

/-- The product of the coefficient bounds over the chain equals an explicit
power of `D`. -/
lemma prod_cBnd_eq (n D : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Finset.Icc 1 (n - 1), cBnd n D (n - 1 - k)
      = (2 : ℝ) ^ (n * (n - 1)) *
        ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n * (n + 1) / 2 - 1) := by
  classical
  have h1 : ∏ k ∈ Finset.Icc 1 (n - 1), cBnd n D (n - 1 - k)
      = ∏ i ∈ Finset.range (n - 1), cBnd n D i := by
    refine Finset.prod_bij (fun k _ => n - 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro k1 hk1 k2 hk2 h
      have h1 := (Finset.mem_Icc.mp hk1).2
      have h2 := (Finset.mem_Icc.mp hk2).2
      omega
    · intro i hi
      have hi' : i < n - 1 := Finset.mem_range.mp hi
      exact ⟨n - 1 - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; rfl
  rw [h1]
  have h2 : ∏ i ∈ Finset.range (n - 1), cBnd n D i
      = ∏ i ∈ Finset.range (n - 1),
          (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [cBnd]
  rw [h2, Commons.Analysis.Real.prod_range_pow_mul_rpow n (2 : ℝ)
    ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) hn]

/-! ## 6. The index-refined field count -/

/-- The chain product bound, in the form used for the per-discriminant count. -/
lemma goodVec_ncard_le_prod' (n D : ℕ) (hn : 3 ≤ n) (hD : 1 ≤ D)
    (hv : ∀ p : ℕ, Nat.Prime p → n < p → p ∣ D → D.factorization p ≤ n - 1) :
    (GoodVec n D).ncard ≤
      ∏ k ∈ Finset.Icc 1 (n - 1),
        (((n + 1) * Nat.factorial n * 2 ^ n) ^ (discJPrimes n D (n - k)).card
          * ⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have h := goodVec_ncard_le_prod n D hn hD hv
  set F : ℕ → ℕ := fun k =>
    if k = 0 then 1 else
      ((n + 1) * Nat.factorial n * 2 ^ n) ^ (discJPrimes n D (n - k)).card
        * ⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊ with hF
  set G : ℕ → ℕ := fun k =>
    ((n + 1) * Nat.factorial n * 2 ^ n) ^ (discJPrimes n D (n - 1 - k)).card
      * ⌈2 * (⌈cBnd n D (n - 2 - k)⌉₊ : ℝ) / ((discJ n D (n - 1 - k) : ℕ) : ℝ) + 2⌉₊ with hG
  have h1 : ∏ k ∈ Finset.range n, F k = ∏ k ∈ Finset.range (n - 1), G k := by
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    conv_lhs => rw [← hn']
    rw [Finset.prod_range_succ']
    have hF0 : F 0 = 1 := by rw [hF]; simp
    rw [hF0]
    simp only [one_mul, mul_one]
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hk' : ¬ (k + 1 = 0) := by omega
    simp only [hF, hG]
    rw [if_neg hk']
    have e1 : n - (k + 1) = n - 1 - k := by omega
    have e2 : n - 1 - (k + 1) = n - 2 - k := by omega
    rw [e1, e2]
  have h2 : ∏ k ∈ Finset.range (n - 1), G k
      = ∏ k ∈ Finset.Icc 1 (n - 1),
        (((n + 1) * Nat.factorial n * 2 ^ n) ^ (discJPrimes n D (n - k)).card
          * ⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊) := by
    refine Finset.prod_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k1 h1 k2 h2 hh
      have h1' : k1 < n - 1 := Finset.mem_range.mp h1
      omega
    · intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hj2 : j ≤ n - 1 := (Finset.mem_Icc.mp hj).2
      refine ⟨j - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]; omega
      · omega
    · intro k hk
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      rw [hG]
      simp only [show n - 2 - k = n - 1 - (k + 1) by omega,
        show n - 1 - k = n - (k + 1) by omega]
  rw [h1, h2] at h
  exact h

theorem goodVec_ncard_le (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D : ℕ, 1 ≤ D →
      (∀ p : ℕ, Nat.Prime p → n < p → p ∣ D → D.factorization p ≤ n - 1) →
      (∀ p : ℕ, Nat.Prime p → p ∣ D → p ^ 2 ∣ D) →
      ((GoodVec n D).ncard : ℝ) ≤ K * (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε) /
        (discLargePart n D : ℝ) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnR : (1 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := by omega
    exact_mod_cast this
  have hden : 0 < 2 * ((n : ℝ) - 1) := by linarith
  set ε' : ℝ := ε / (2 * ((n : ℝ) - 1)) with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; exact div_pos hε hden
  obtain ⟨Cω, hCωpos, hCω⟩ := Commons.NumberTheory.Nat.pow_omega_le_const_mul_rpow
    ((((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ)) ε' (by positivity) hε'
  set K : ℝ := (2 : ℝ) ^ (n * (n - 1)) * ((2 : ℝ) ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) *
    8 ^ (n - 1) * Cω ^ (n - 1) with hKdef
  refine ⟨K, by rw [hKdef]; positivity, ?_⟩
  intro D hD hv hsq
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set g : ℕ → ℕ := fun k => ((n + 1) * Nat.factorial n * 2 ^ n) ^ (discJPrimes n D (n - k)).card
      * ⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊ with hg
  set G : ℕ → ℝ := fun k => (Cω * (D : ℝ) ^ ε') *
      (8 * cBnd n D (n - 1 - k) / (discJ n D (n - k) : ℝ)) with hGdef
  have hchain : (GoodVec n D).ncard ≤ ∏ k ∈ Finset.Icc 1 (n - 1), g k := by
    have h := goodVec_ncard_le_prod' n D hn hD hv
    simpa only [hg] using h
  have hpoint : ∀ k ∈ Finset.Icc 1 (n - 1), ((g k : ℕ) : ℝ) ≤ G k := by
    intro k hk
    rw [hg, hGdef]
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    have hkj : 1 ≤ n - k := by omega
    have hkjn : n - k ≤ n - 1 := by omega
    have hMle : (discJ n D (n - k) : ℝ) ≤ cBnd n D (n - 1 - k) := by
      have h1 := discJ_le_cBnd n D (n - k) hn hD hkj hkjn hsq
      have h2 : n - k - 1 = n - 1 - k := by omega
      simpa [h2] using h1
    have hMpos : (0 : ℝ) < (discJ n D (n - k) : ℝ) := by
      have : 0 < discJ n D (n - k) := Nat.pos_of_ne_zero (by
        rw [discJ]
        exact Finset.prod_ne_zero_iff.mpr (fun p hp => (prime_of_mem_discJPrimes hp).ne_zero))
      exact_mod_cast this
    have hcBnd1 : (1 : ℝ) ≤ cBnd n D (n - 1 - k) := by
      rw [cBnd]
      have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1))) := by
        have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * n + 6) := one_le_pow₀ (by norm_num)
        have h5 : (1 : ℝ) ≤ (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1))) :=
          Real.one_le_rpow hD1 (by positivity)
        nlinarith
      have hexp : n - (n - 1 - k) = k + 1 := by omega
      rw [hexp]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (one_le_pow₀ hbase)
    have hceil : (⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊ : ℝ)
        ≤ 8 * cBnd n D (n - 1 - k) / (discJ n D (n - k) : ℝ) := by
      have hBle : ((⌈cBnd n D (n - 1 - k)⌉₊ : ℕ) : ℝ) ≤ cBnd n D (n - 1 - k) + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (by positivity))
      have hX0 : (0 : ℝ) ≤ 2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) /
          ((discJ n D (n - k) : ℕ) : ℝ) + 2 := by positivity
      have hc1 : (⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) /
          ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊ : ℝ)
          ≤ 2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / ((discJ n D (n - k) : ℕ) : ℝ) + 2 + 1 :=
        le_of_lt (Nat.ceil_lt_add_one hX0)
      have hEq : 2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) / (discJ n D (n - k) : ℝ) + 2 + 1
          = (2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) + 3 * (discJ n D (n - k) : ℝ)) /
            (discJ n D (n - k) : ℝ) := by
        field_simp
        ring
      have h3 : (2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) + 3 * (discJ n D (n - k) : ℝ)) /
          (discJ n D (n - k) : ℝ) ≤ 8 * cBnd n D (n - 1 - k) / (discJ n D (n - k) : ℝ) := by
        rw [div_le_div_iff₀ hMpos hMpos]
        nlinarith [hBle, hMle, hcBnd1, hMpos, le_of_lt hMpos]
      exact le_trans hc1 (hEq ▸ h3)
    have hCbound : (((n : ℝ) + 1) * (n.factorial : ℝ) * 2 ^ n) ^
        (discJPrimes n D (n - k)).card ≤ Cω * (D : ℝ) ^ ε' := by
      have heq : (((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ)
          = ((n : ℝ) + 1) * (n.factorial : ℝ) * 2 ^ n := by push_cast; ring
      have hb : (1 : ℝ) ≤ (((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ) := by
        have hb' : (1 : ℕ) ≤ (n + 1) * Nat.factorial n * 2 ^ n :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact_mod_cast hb'
      have h1 : (((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ) ^ (discJPrimes n D (n - k)).card
          ≤ (((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ) ^ (D.primeFactors.card) :=
        pow_le_pow_right₀ hb (Finset.card_le_card (discJPrimes_subset_primeFactors n D (n - k)))
      have h4 : (((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ) ^ (D.primeFactors.card)
          ≤ Cω * (D : ℝ) ^ ε' := hCω D hD
      have h5 : (((n + 1) * Nat.factorial n * 2 ^ n : ℕ) : ℝ) ^ (discJPrimes n D (n - k)).card
          ≤ Cω * (D : ℝ) ^ ε' := le_trans h1 h4
      rwa [heq] at h5
    push_cast
    have h1 : (0:ℝ) ≤ ((⌈2 * (⌈cBnd n D (n - 1 - k)⌉₊ : ℝ) /
        ((discJ n D (n - k) : ℕ) : ℝ) + 2⌉₊ : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ Cω * (D : ℝ) ^ ε' := by positivity
    exact mul_le_mul hCbound hceil h1 h2
  have hprod : ((∏ k ∈ Finset.Icc 1 (n - 1), g k : ℕ) : ℝ) ≤
      ∏ k ∈ Finset.Icc 1 (n - 1), G k := by
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod (fun k hk => by positivity) hpoint
  have hval : ∏ k ∈ Finset.Icc 1 (n - 1), G k
      = (Cω * (D : ℝ) ^ ε') ^ (n - 1) * 8 ^ (n - 1) *
          ((2 : ℝ) ^ (n * (n - 1)) *
            ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n * (n + 1) / 2 - 1)) /
          (discLargePart n D : ℝ) := by
    rw [hGdef, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
    have h2 : (∏ k ∈ Finset.Icc 1 (n - 1), (8 * cBnd n D (n - 1 - k) / (discJ n D (n - k) : ℝ)))
        = 8 ^ (n - 1) * (∏ k ∈ Finset.Icc 1 (n - 1), cBnd n D (n - 1 - k)) /
          (∏ k ∈ Finset.Icc 1 (n - 1), (discJ n D (n - k) : ℝ)) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Nat.card_Icc, Nat.add_sub_cancel]
    rw [h2, prod_cBnd_eq n D hn1]
    have h3 : (∏ k ∈ Finset.Icc 1 (n - 1), (discJ n D (n - k) : ℝ))
        = (discLargePart n D : ℝ) := by
      rw [← Nat.cast_prod, prod_discJ_eq_discLargePart n D hv]
    rw [h3]
    field_simp
  -- the final comparison
  have hLpos : (0 : ℝ) < (discLargePart n D : ℝ) := by
    have : 0 < discLargePart n D := discLargePart_pos n D
    exact_mod_cast this
  have hmul1 : ((n - 1 : ℕ) : ℝ) * ε' = ε / 2 := by
    rw [hε'def, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have h1 : (2 * ((n : ℝ) - 1)) ≠ 0 := ne_of_gt hden
    have h2 : ((n : ℝ) - 1) ≠ 0 := by linarith
    field_simp
  have hK : K = Cω ^ (n - 1) * 8 ^ (n - 1) *
      ((2 : ℝ) ^ (n * (n - 1)) * ((2 : ℝ) ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1)) := by
    rw [hKdef]; ring
  have hval2 : (Cω * (D : ℝ) ^ ε') ^ (n - 1) * 8 ^ (n - 1) *
        ((2 : ℝ) ^ (n * (n - 1)) *
          ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n * (n + 1) / 2 - 1)) /
        (discLargePart n D : ℝ)
      ≤ K * (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε) / (discLargePart n D : ℝ) := by
    rw [hK, div_le_div_iff_of_pos_right hLpos]
    have h1 : (Cω * (D : ℝ) ^ ε') ^ (n - 1)
        = Cω ^ (n - 1) * (D : ℝ) ^ (((n - 1 : ℕ) : ℝ) * ε') := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le, mul_comm]
    have h2 : ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n * (n + 1) / 2 - 1)
        = ((2 : ℝ) ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) *
          (D : ℝ) ^ (((n * (n + 1) / 2 - 1 : ℕ) : ℝ) / (2 * ((n : ℝ) - 1))) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]
      congr 1
      push_cast
      rw [div_mul_eq_mul_div]
      ring
    rw [h1, h2, hmul1, Commons.NumberTheory.Nat.cast_half_mul_sub_one_div n hn2]
    have hle : (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε / 2) ≤ (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
    have hA : (0 : ℝ) ≤ Cω ^ (n - 1) * 8 ^ (n - 1) *
        (2 ^ (n * (n - 1)) * ((2 : ℝ) ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1)) := by
      positivity
    have hrewrite : Cω ^ (n - 1) * (D : ℝ) ^ (ε / 2) * 8 ^ (n - 1) *
          (2 ^ (n * (n - 1)) *
            (((2 : ℝ) ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) * (D : ℝ) ^ (((n : ℝ) + 2) / 4)))
        = (Cω ^ (n - 1) * 8 ^ (n - 1) *
            (2 ^ (n * (n - 1)) * ((2 : ℝ) ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1))) *
          (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε / 2) := by
      rw [Real.rpow_add hDpos]
      ring
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hle hA
  calc ((GoodVec n D).ncard : ℝ)
      ≤ ((∏ k ∈ Finset.Icc 1 (n - 1), g k : ℕ) : ℝ) := by exact_mod_cast hchain
    _ ≤ ∏ k ∈ Finset.Icc 1 (n - 1), G k := hprod
    _ = (Cω * (D : ℝ) ^ ε') ^ (n - 1) * 8 ^ (n - 1) *
          ((2 : ℝ) ^ (n * (n - 1)) *
            ((2 : ℝ) ^ (2 * n + 6) * (D : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n * (n + 1) / 2 - 1)) /
          (discLargePart n D : ℝ) := hval
    _ ≤ K * (D : ℝ) ^ (((n : ℝ) + 2) / 4 + ε) / (discLargePart n D : ℝ) := hval2


end

end Submission.Vdw
