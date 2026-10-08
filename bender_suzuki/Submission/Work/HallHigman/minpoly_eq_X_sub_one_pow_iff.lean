import Mathlib
import Submission.Work.HallHigman.sub_one_pow_prime_pow_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

open Polynomial

/-- A monic polynomial over a field dividing `(X - 1) ^ N` is itself a power of `X - 1`. -/
lemma monic_dvd_X_sub_one_pow {K : Type*} [Field K] (N : ℕ) (P : K[X])
    (hP : P.Monic) (h : P ∣ (X - 1) ^ N) : ∃ k ≤ N, P = (X - 1) ^ k := by
  revert P
  refine Nat.strong_induction_on N ?_
  intro N ih P hP h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨0, le_refl 0, by rw [pow_zero]; exact (hP.isUnit_iff).mp (isUnit_of_dvd_one h)⟩
  · by_cases hdvd : (X - 1 : K[X]) ∣ P
    · obtain ⟨P', rfl⟩ := hdvd
      have hP' : P'.Monic := Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C 1) hP
      have hdvd' : P' ∣ (X - 1) ^ (N - 1) := by
        have h' : (X - 1 : K[X]) * P' ∣ (X - 1) * (X - 1) ^ (N - 1) := by
          rwa [← pow_succ', Nat.sub_add_cancel hN]
        exact (mul_dvd_mul_iff_left (Polynomial.X_sub_C_ne_zero 1)).mp h'
      obtain ⟨k, hkN, hk⟩ := ih (N - 1) (by omega) P' hP' hdvd'
      exact ⟨k + 1, by omega, by rw [hk, pow_succ]; ring⟩
    · have hp : IsRelPrime P (X - 1 : K[X]) :=
        (((Polynomial.irreducible_X_sub_C (1 : K)).isRelPrime_iff_not_dvd).mpr hdvd).symm
      have hu : IsUnit P := (IsRelPrime.pow_right hp).isUnit_of_dvd h
      exact ⟨0, Nat.zero_le _, by rw [pow_zero]; exact (hP.isUnit_iff).mp hu⟩

open Polynomial in
/-- The sharp criterion for the minimal polynomial of a `p^n`-th root of unity in a ring of
endomorphisms over a field of characteristic `p` to be `(X - 1) ^ (p ^ n)`: exactly when
`(f - 1) ^ (p ^ n - 1) ≠ 0`. -/
lemma minpoly_eq_X_sub_one_pow_iff {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {p n : ℕ} [Fact p.Prime] [CharP K p] (f : Module.End K M) (h : f ^ (p ^ n) = 1) :
    minpoly K f = (X - 1) ^ (p ^ n) ↔ (f - 1) ^ (p ^ n - 1) ≠ 0 := by
  have hpow : (f - 1) ^ (p ^ n) = 0 := sub_one_pow_prime_pow_eq_zero f h
  have hX1 : (Polynomial.aeval f) (X - 1 : K[X]) = f - 1 := by simp
  have haeval : ∀ k : ℕ, (Polynomial.aeval f) ((X - 1 : K[X]) ^ k) = (f - 1) ^ k := by
    intro k
    rw [map_pow, hX1]
  have hint : IsIntegral K f :=
    ⟨(X - 1 : K[X]) ^ (p ^ n), (Polynomial.monic_X_sub_C 1).pow _,
      by rw [← Polynomial.aeval_def, haeval, hpow]⟩
  have hmem : minpoly K f ∣ (X - 1 : K[X]) ^ (p ^ n) :=
    minpoly.dvd_iff.mpr (by rw [haeval, hpow])
  refine ⟨?_, ?_⟩
  · intro heq hzero
    have hdvd : (X - 1 : K[X]) ^ (p ^ n) ∣ (X - 1) ^ (p ^ n - 1) := by
      rw [← heq]
      exact minpoly.dvd_iff.mpr (by rw [haeval, hzero])
    have hnd1 : ((X - 1 : K[X]) ^ (p ^ n)).natDegree = p ^ n := by
      rw [Polynomial.natDegree_pow, ← Polynomial.C_1, Polynomial.natDegree_X_sub_C, mul_one]
    have hnd2 : ((X - 1 : K[X]) ^ (p ^ n - 1)).natDegree = p ^ n - 1 := by
      rw [Polynomial.natDegree_pow, ← Polynomial.C_1, Polynomial.natDegree_X_sub_C, mul_one]
    have hne : (X - 1 : K[X]) ^ (p ^ n - 1) ≠ 0 :=
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [hnd1, hnd2] at hle
    have hp1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    omega
  · intro hne
    obtain ⟨k, hk_le, hk⟩ :=
      monic_dvd_X_sub_one_pow (p ^ n) (minpoly K f) (minpoly.monic hint) hmem
    rw [hk]
    have hk_eq : k = p ^ n := by
      by_contra hne'
      have hlt : k < p ^ n := lt_of_le_of_ne hk_le hne'
      have hle : k ≤ p ^ n - 1 := Nat.le_sub_one_of_lt hlt
      have hdvd : (X - 1 : K[X]) ^ k ∣ (X - 1) ^ (p ^ n - 1) := pow_dvd_pow _ hle
      have hzero : (f - 1) ^ (p ^ n - 1) = 0 := by
        have hann := minpoly.dvd_iff.mp (hk.symm ▸ hdvd)
        rwa [haeval] at hann
      exact hne hzero
    rw [hk_eq]

end Work.HallHigman
