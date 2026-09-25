import Mathlib
import Submission.Work.Arithmetic.CMDefs

/-!
# `A_η * A'_ε` divides `(Q)²`

Auxiliary divisibility for the class-group pigeonhole (Proposition 2.2 of the paper).

Let `K` be a CM field and `P 1, …, P m` prime ideals of `𝓞 K` that are pairwise distinct and
pairwise non-conjugate (`conjI (P i) ≠ P j` for all `i, j`).  Suppose moreover that each `P i`
lies above a rational prime `p i` dividing a fixed natural number `Q`.

Then for any signs `η`, the ideal `A_η = ∏ i, (if η i then P i else conjI (P i))` is a product
of pairwise distinct prime ideals, each of which contains the principal ideal `(Q)`.  As distinct
nonzero prime ideals are pairwise coprime (in a Dedekind domain), the product divides `(Q)`.  The
same applies to `A'_ε = ∏ i, (if ε i then conjI (P i) else P i)`, and multiplying the two
divisibilities gives `A_η * A'_ε ∣ (Q)²`.
-/

namespace Work.Arithmetic.PigeonholeAux

open NumberField

theorem dvd_span_sq {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]
    (m : ℕ) (P : Fin m → Ideal (NumberField.RingOfIntegers K))
    (hP : ∀ i, (P i).IsPrime) (hPne : ∀ i j, i ≠ j → P i ≠ P j)
    (hconj : ∀ i j, Work.Arithmetic.conjI (P i) ≠ P j)
    (Q : ℕ) (hQ : ∀ i, ∃ p : ℕ, p ∣ Q ∧ Nat.Prime p ∧ Ideal.span {(p : NumberField.RingOfIntegers K)} ≤ P i)
    (η ε : Fin m → Bool) :
    Work.Arithmetic.ASet m P η * Work.Arithmetic.ASet' m P ε ∣ Ideal.span {((Q : NumberField.RingOfIntegers K) ^ 2)} := by
  -- `P i` is nonzero: it contains `span {p}` for a rational prime `p`.
  have hPi_ne_bot : ∀ i, P i ≠ ⊥ := by
    intro i hbot
    obtain ⟨p, -, hpprime, hple⟩ := hQ i
    rw [hbot] at hple
    have hmem : (p : 𝓞 K) ∈ (⊥ : Ideal (𝓞 K)) :=
      (Ideal.span_singleton_le_iff_mem (⊥ : Ideal (𝓞 K))).mp hple
    rw [Ideal.mem_bot] at hmem
    exact Nat.cast_ne_zero.mpr hpprime.ne_zero hmem
  -- Maximality of the various primes involved.
  have hmaxP : ∀ i, (P i).IsMaximal := fun i => (hP i).isMaximal (hPi_ne_bot i)
  have hmaxC : ∀ i, (conjI (P i)).IsMaximal :=
    fun i => (conjI_prime (hP i)).isMaximal (conjI_ne_bot (hPi_ne_bot i))
  -- The principal ideal `(Q)` is contained in every `P i` and every `conjI (P i)`.
  have hdvdP : ∀ i, P i ∣ Ideal.span {(Q : 𝓞 K)} := by
    intro i
    obtain ⟨p, hpdvd, -, hple⟩ := hQ i
    rw [Ideal.dvd_iff_le]
    have hdvd_cast : (p : 𝓞 K) ∣ (Q : 𝓞 K) := by
      obtain ⟨t, ht⟩ := hpdvd
      refine ⟨(t : 𝓞 K), ?_⟩
      rw [← Nat.cast_mul, ht]
    exact le_trans
      ((Ideal.span_singleton_le_iff_mem (Ideal.span {(p : 𝓞 K)})).mpr
        (Ideal.mem_span_singleton.mpr hdvd_cast)) hple
  have hdvdC : ∀ i, conjI (P i) ∣ Ideal.span {(Q : 𝓞 K)} := by
    intro i
    rw [Ideal.dvd_iff_le]
    have h := conjI_mono (Ideal.dvd_iff_le.mp (hdvdP i))
    rwa [conjI_span_nat] at h
  -- Any product picking `P i` or `conjI (P i)` at each place divides `(Q)`.
  have key : ∀ F : Fin m → Ideal (𝓞 K), (∀ i, F i = P i ∨ F i = conjI (P i)) →
      (∏ i, F i) ∣ Ideal.span {(Q : 𝓞 K)} := by
    intro F hF
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      show IsCoprime (F a) (F b)
      rw [Ideal.isCoprime_iff_sup_eq]
      obtain hFa | hFa := hF a
      · obtain hFb | hFb := hF b
        · rw [hFa, hFb]
          exact Ideal.IsMaximal.coprime_of_ne (hmaxP a) (hmaxP b) (hPne a b hab)
        · rw [hFa, hFb]
          exact Ideal.IsMaximal.coprime_of_ne (hmaxP a) (hmaxC b) (hconj b a).symm
      · obtain hFb | hFb := hF b
        · rw [hFa, hFb]
          exact Ideal.IsMaximal.coprime_of_ne (hmaxC a) (hmaxP b) (hconj a b)
        · rw [hFa, hFb]
          exact Ideal.IsMaximal.coprime_of_ne (hmaxC a) (hmaxC b)
            (fun h => hPne a b hab (by simpa using congrArg conjI h))
    · intro i _
      obtain hFi | hFi := hF i
      · rw [hFi]; exact hdvdP i
      · rw [hFi]; exact hdvdC i
  have choice : ∀ (θ : Fin m → Bool) (i : Fin m),
      (if θ i then P i else conjI (P i)) = P i ∨
        (if θ i then P i else conjI (P i)) = conjI (P i) := by
    intro θ i
    by_cases h : θ i = true
    · left; simp [h]
    · right; simp [h]
  have choice' : ∀ (θ : Fin m → Bool) (i : Fin m),
      (if θ i then conjI (P i) else P i) = P i ∨
        (if θ i then conjI (P i) else P i) = conjI (P i) := by
    intro θ i
    by_cases h : θ i = true
    · right; simp [h]
    · left; simp [h]
  have hη : ASet m P η ∣ Ideal.span {(Q : 𝓞 K)} := by
    rw [ASet_eq_prod]
    exact key (fun i => if η i then P i else conjI (P i)) (choice η)
  have hε : ASet' m P ε ∣ Ideal.span {(Q : 𝓞 K)} := by
    rw [ASet'_eq_prod]
    exact key (fun i => if ε i then conjI (P i) else P i) (choice' ε)
  have hmain : ASet m P η * ASet' m P ε ∣ Ideal.span {(Q : 𝓞 K)} * Ideal.span {(Q : 𝓞 K)} :=
    mul_dvd_mul hη hε
  rwa [Ideal.span_singleton_mul_span_singleton, ← pow_two] at hmain

end Work.Arithmetic.PigeonholeAux
