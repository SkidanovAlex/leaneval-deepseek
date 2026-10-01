import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

namespace Commons.Algebra.Polynomial

open Finset

/-- Over a domain in which `(-1)^(j+1)·j ≠ 0` for `1 ≤ j ≤ k`, the power sums of orders
`1,…,k` determine the value multiset (Newton's identities + `∏(T - zᵢ)`). -/
theorem power_sums_determine_multiset_domain {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (hne : ∀ j, 1 ≤ j → j ≤ k → ((-1 : R) ^ (j + 1)) * (j : R) ≠ 0)
    (z w : Fin k → R) (h : ∀ m, 1 ≤ m → m ≤ k → (∑ i, (z i) ^ m) = (∑ i, (w i) ^ m)) :
    Finset.univ.val.map z = Finset.univ.val.map w := by
  classical
  -- Newton's identities, in the concrete form used below, obtained by evaluating the
  -- `MvPolynomial` version at `X i ↦ u i`.
  have newton : ∀ (u : Fin k → R) (m : ℕ),
      (m : R) * (Finset.univ.val.map u).esymm m =
        (-1 : R) ^ (m + 1) *
          ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m with a.1 < m,
            (-1 : R) ^ a.1 * (Finset.univ.val.map u).esymm a.1 * (∑ i, (u i) ^ a.2) := by
    intro u m
    have key := congrArg (MvPolynomial.aeval u) (MvPolynomial.mul_esymm_eq_sum (Fin k) R m)
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
      MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X]
      at key
    exact key
  -- The elementary symmetric functions of `z` and `w` agree.
  have hesymm : ∀ m, m ≤ k →
      (Finset.univ.val.map z).esymm m = (Finset.univ.val.map w).esymm m := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hmk
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp [Multiset.esymm]
    · have hne_m : (m : R) ≠ 0 := by
        intro hzero
        exact hne m hmpos hmk (by simp [hzero])
      have hz := newton z m
      have hw := newton w m
      have hsum : (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m with a.1 < m,
            (-1 : R) ^ a.1 * (Finset.univ.val.map z).esymm a.1 * (∑ i, (z i) ^ a.2))
          = (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m with a.1 < m,
            (-1 : R) ^ a.1 * (Finset.univ.val.map w).esymm a.1 * (∑ i, (w i) ^ a.2)) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        obtain ⟨hsum_eq, ha_lt⟩ := ha
        have h1 : (Finset.univ.val.map z).esymm a.1 = (Finset.univ.val.map w).esymm a.1 :=
          ih a.1 ha_lt (by omega)
        have h2 : (∑ i, (z i) ^ a.2) = (∑ i, (w i) ^ a.2) := by
          apply h <;> omega
        rw [h1, h2]
      rw [hsum] at hz
      exact mul_left_cancel₀ hne_m (hz.trans hw.symm)
  -- The value multisets are determined by `∏ (T - ·)`, whose coefficients are the `esymm`.
  have hcardz : (Finset.univ.val.map z).card = k := by simp
  have hcardw : (Finset.univ.val.map w).card = k := by simp
  have hP : (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Finset.univ.val.map z)).prod
      = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Finset.univ.val.map w)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    rw [hcardz, hcardw]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hesymm j (by omega)]
  have h1 := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map z)
  have h2 := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map w)
  rw [hP] at h1
  rw [← h1, h2]

end Commons.Algebra.Polynomial