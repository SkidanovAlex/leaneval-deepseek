import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.KrullDimension.PID

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped NumberField BigOperators

namespace Commons.NumberTheory.NumberField

/-- The radical of a finite product of powers of pairwise-distinct maximal ideals equals the
product of the ideals themselves. -/
lemma radical_finset_prod_prime_pow {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι)
    (P : ι → Ideal R) (e : ι → ℕ) :
    (∀ i ∈ s, (P i).IsMaximal) → (∀ i ∈ s, e i ≠ 0) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ≠ P j) →
        (∏ i ∈ s, P i ^ e i).radical = ∏ i ∈ s, P i := by
  classical
  refine Finset.induction_on s ?base ?step
  · intro hmax he hne
    simp [Ideal.radical]
  · intro a t has ih hmax he hne
    have hmaxa : (P a).IsMaximal := hmax a (Finset.mem_insert_self a t)
    have hea : e a ≠ 0 := he a (Finset.mem_insert_self a t)
    have ih' : (∏ i ∈ t, P i ^ e i).radical = ∏ i ∈ t, P i :=
      ih (fun i hi => hmax i (Finset.mem_insert_of_mem hi))
         (fun i hi => he i (Finset.mem_insert_of_mem hi))
         (fun i hi j hj hneij => hne i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hneij)
    calc
      (∏ i ∈ insert a t, P i ^ e i).radical
          = ((P a ^ e a) * ∏ i ∈ t, P i ^ e i).radical := by rw [Finset.prod_insert has]
      _ = (P a ^ e a).radical ⊓ (∏ i ∈ t, P i ^ e i).radical := by rw [Ideal.radical_mul]
      _ = (P a) ⊓ (∏ i ∈ t, P i ^ e i).radical := by
          congr 1
          rw [Ideal.radical_pow (P a) hea]
          exact (Ideal.IsPrime.radical hmaxa.isPrime)
      _ = P a ⊓ ∏ i ∈ t, P i := by rw [ih']
      _ = P a * ∏ i ∈ t, P i := by
          have hcop : IsCoprime (P a) (∏ i ∈ t, P i) := by
            apply IsCoprime.prod_right
            intro i hi
            apply (Ideal.isCoprime_iff_sup_eq).mpr
            apply Ideal.IsMaximal.coprime_of_ne hmaxa (hmax i (Finset.mem_insert_of_mem hi))
            intro hPi
            have hai : a = i := by
              by_contra hai
              exact (hne a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) hai) hPi
            exact has (by simpa [hai] using hi)
          exact (Ideal.mul_eq_inf_of_isCoprime hcop).symm
      _ = ∏ i ∈ insert a t, P i := by rw [Finset.prod_insert has]

theorem radical_map_eq_prod_primesOver {K : Type*} [Field K] [NumberField K] (p : ℕ)
    [Fact (Nat.Prime p)] :
    ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))).radical =
      ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K), P := by
  classical
  set p₀ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  set s : Finset (Ideal (𝓞 K)) := IsDedekindDomain.primesOverFinset p₀ (𝓞 K)
  set F : Finset (Ideal (𝓞 K)) := (p₀.primesOver (𝓞 K)).toFinset
  have hp₀ne : p₀ ≠ ⊥ := by
    simp [p₀]
    exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  haveI hp₀max : p₀.IsMaximal := by
    simpa [p₀] using (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).isMaximal_span_singleton
  have hsplit : p₀.map (algebraMap ℤ (𝓞 K)) = ∏ P ∈ F, P ^ P.ramificationIdx ℤ := by
    dsimp [F]
    exact Ideal.map_algebraMap_eq_finsetProd_pow (R := (𝓞 K)) (S := ℤ) (p := p₀) hp₀ne
  have hF : F = s := by
    apply Finset.ext
    intro P
    constructor
    · intro hPF
      have hP : P ∈ p₀.primesOver (𝓞 K) := Set.mem_toFinset.mp hPF
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp₀ne (𝓞 K)).mpr hP
    · intro hPs
      have hP : P ∈ p₀.primesOver (𝓞 K) :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp₀ne (𝓞 K)).mp hPs
      exact Set.mem_toFinset.mpr hP
  have hmaxP : ∀ P ∈ F, P.IsMaximal := by
    intro P hPF
    have hP : P ∈ p₀.primesOver (𝓞 K) := Set.mem_toFinset.mp hPF
    have hPprime : P.IsPrime := hP.1
    have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp₀ne hP
    exact Ideal.IsPrime.isMaximal hPprime hPbot
  have heP : ∀ P ∈ F, P.ramificationIdx ℤ ≠ 0 := by
    intro P hPF
    have hP : P ∈ p₀.primesOver (𝓞 K) := Set.mem_toFinset.mp hPF
    haveI : P.IsPrime := hP.1
    exact (Ideal.ramificationIdx_pos (q := P) (R := ℤ)).ne'
  have hneP : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → P ≠ Q := by
    intro P hPF Q hQF hPQ
    exact hPQ
  calc
    (p₀.map (algebraMap ℤ (𝓞 K))).radical
        = (∏ P ∈ F, P ^ P.ramificationIdx ℤ).radical := by rw [hsplit]
    _ = ∏ P ∈ F, P := by
        exact radical_finset_prod_prime_pow F (fun P : Ideal (𝓞 K) => P)
          (fun P : Ideal (𝓞 K) => P.ramificationIdx ℤ) hmaxP heP hneP
    _ = ∏ P ∈ s, P := by rw [hF]

end Commons.NumberTheory.NumberField