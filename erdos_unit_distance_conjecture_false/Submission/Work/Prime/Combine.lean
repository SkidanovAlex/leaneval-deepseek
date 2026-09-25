import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Arithmetic.Splitting

namespace Work.Prime

open scoped nonZeroDivisors
open NumberField

/-- A prime ideal of `𝓞 K` contains at most one rational prime: if `p` and `p'` are rational
primes both lying in a prime ideal `𝔭`, then `p = p'`. -/
lemma eq_of_prime_of_mem {K : Type*} [Field K] [NumberField K]
    {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭.IsPrime) {p p' : ℕ} (hp : Nat.Prime p) (hp' : Nat.Prime p')
    (h1 : (p : 𝓞 K) ∈ 𝔭) (h2 : (p' : 𝓞 K) ∈ 𝔭) : p = p' := by
  by_contra hne
  have hcop : Nat.Coprime p p' := (Nat.coprime_primes hp hp').mpr hne
  have hcopZ : IsCoprime (p : ℤ) (p' : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop
  have hcopO : IsCoprime (p : 𝓞 K) (p' : 𝓞 K) := by
    have h := hcopZ.map (Int.castRingHom (𝓞 K))
    simpa using h
  obtain ⟨a, b, hab⟩ := hcopO
  have hmem : (1 : 𝓞 K) ∈ 𝔭 := by
    rw [← hab]
    exact add_mem (Ideal.mul_mem_left 𝔭 a h1) (Ideal.mul_mem_left 𝔭 b h2)
  exact h𝔭.ne_top ((Ideal.eq_top_iff_one 𝔭).mpr hmem)

/-- **Prime families**: a finite injective family of primes `q ≡ 1 mod 4` which all split
completely in a CM field `K` produces `t · [K⁺:ℚ]` prime ideals of `𝒪_K` which are pairwise
distinct and pairwise non-conjugate.

This is obtained by pasting the `t` families supplied by `Work.Arithmetic.Splitting`. Two primes
lying above distinct rational primes `q b` cannot be equal, because a prime ideal contains at most
one rational prime. -/
theorem Combine (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K]
    (t : ℕ) (q : Fin t → ℕ) (hq : ∀ b, Nat.Prime (q b)) (hqi : Function.Injective q)
    (hq4 : ∀ b, q b % 4 = 1) (hsplit : ∀ b, Work.Defs.SplitsCompletely (q b) K) :
    ∃ P : Fin (t * Module.finrank ℚ (NumberField.maximalRealSubfield K)) → Ideal (𝓞 K),
      (∀ i, (P i).IsPrime) ∧ (∀ i j, i ≠ j → P i ≠ P j) ∧
      (∀ i j, Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j) ∧
      (∀ i, ∃ p : ℕ, p ∣ (∏ b, q b) ∧ Nat.Prime p ∧ Ideal.span {(p : 𝓞 K)} ≤ P i) := by
  classical
  have hfam : ∀ b : Fin t,
      ∃ P : Fin (Module.finrank ℚ (NumberField.maximalRealSubfield K)) → Ideal (𝓞 K),
        (∀ i, (P i).IsPrime) ∧ (∀ i, (q b : 𝓞 K) ∈ P i) ∧
        (∀ i j, i ≠ j → P i ≠ P j) ∧
        (∀ i j,
          Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j) :=
    fun b => Work.Arithmetic.Splitting K (q b) (hq b) (hq4 b) (hsplit b)
  choose P hPprime hPmem hPne hPconj using hfam
  let e : Fin (t * Module.finrank ℚ (NumberField.maximalRealSubfield K)) ≃
      Fin t × Fin (Module.finrank ℚ (NumberField.maximalRealSubfield K)) :=
    (finProdFinEquiv (m := t)
      (n := Module.finrank ℚ (NumberField.maximalRealSubfield K))).symm
  let Q : Fin (t * Module.finrank ℚ (NumberField.maximalRealSubfield K)) → Ideal (𝓞 K) :=
    fun i => P (e i).1 (e i).2
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hPprime _ _
  · intro i j hij heq
    have heq' : P (e i).1 (e i).2 = P (e j).1 (e j).2 := heq
    have hmem2 : (q (e j).1 : 𝓞 K) ∈ P (e i).1 (e i).2 := by rw [heq']; exact hPmem _ _
    have hpb : q (e i).1 = q (e j).1 :=
      eq_of_prime_of_mem (hPprime _ _) (hq _) (hq _) (hPmem _ _) hmem2
    have hb : (e i).1 = (e j).1 := hqi hpb
    have hjj : (e i).2 = (e j).2 := by
      by_contra h2
      rw [hb] at heq'
      exact hPne (e j).1 (e i).2 (e j).2 h2 heq'
    exact hij (e.injective (Prod.ext hb hjj))
  · intro i j heq
    have heq' : Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom
        (P (e i).1 (e i).2) = P (e j).1 (e j).2 := heq
    have hmem1 : (q (e i).1 : 𝓞 K) ∈
        Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom
          (P (e i).1 (e i).2) := by
      simpa only [map_natCast] using
        Ideal.mem_map_of_mem ((NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom)
          (hPmem (e i).1 (e i).2)
    rw [heq'] at hmem1
    have hpb : q (e i).1 = q (e j).1 :=
      eq_of_prime_of_mem (hPprime _ _) (hq _) (hq _) hmem1 (hPmem _ _)
    have hb : (e i).1 = (e j).1 := hqi hpb
    rw [hb] at heq'
    exact hPconj (e j).1 (e i).2 (e j).2 heq'
  · intro i
    refine ⟨q (e i).1, Finset.dvd_prod_of_mem q (Finset.mem_univ _), hq _, ?_⟩
    rw [Ideal.span_singleton_le_iff_mem]
    exact hPmem _ _

end Work.Prime
