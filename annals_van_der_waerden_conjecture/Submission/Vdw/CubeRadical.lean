import Mathlib
import Submission.Vdw.PolyIndex
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le
import Submission.Commons.Algebra.Polynomial.sum_natDegree_mul_count_normalizedFactors

open Polynomial
open scoped BigOperators

namespace Submission.Vdw

open UniqueFactorizationMonoid

set_option autoImplicit false

/-- A monic cubic polynomial whose radical has degree at most one is the cube of
a linear polynomial. -/
theorem eq_cube_of_monic_cubic_radical {F : Type*} [Field F] [DecidableEq F]
    (Q : F[X]) (hmon : Q.Monic) (hdeg : Q.natDegree = 3)
    (hrad : (UniqueFactorizationMonoid.radical Q).natDegree ≤ 1) :
    ∃ a : F, Q = (X - C a) ^ 3 := by
  classical
  have hQ0 : Q ≠ 0 := hmon.ne_zero
  set s : Finset F[X] := (normalizedFactors Q).toFinset with hs
  have hsm : ∀ g ∈ s, g ∈ normalizedFactors Q := fun g hg => by
    rw [hs] at hg; exact Multiset.mem_toFinset.mp hg
  have hmonic : ∀ g ∈ s, g.Monic := fun g hg =>
    Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hQ0 (hsm g hg)
  have hirr : ∀ g ∈ s, Irreducible g := fun g hg =>
    Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors hQ0 (hsm g hg)
  -- the radical is the product of the distinct factors
  have hrad_eq : UniqueFactorizationMonoid.radical Q = ∏ g ∈ s, g := by
    rw [Commons.FieldTheory.Polynomial.radical_eq_toFinset_prod Q, ← hs]
    rfl
  -- the radical's degree is the sum of the degrees
  have hsum : s.sum (fun g => g.natDegree) = (UniqueFactorizationMonoid.radical Q).natDegree := by
    rw [hrad_eq, Polynomial.natDegree_prod s (fun g => g) (fun g hg => (hmonic g hg).ne_zero)]
  have hsum_le : s.sum (fun g => g.natDegree) ≤ 1 := by
    rw [hsum]; exact hrad
  -- the weighted degree sum is 3
  have hcount : s.sum (fun g => g.natDegree * (normalizedFactors Q).count g) = 3 := by
    have h := Commons.Algebra.Polynomial.sum_natDegree_mul_count_normalizedFactors Q hmon
    rw [hdeg] at h
    rw [← hs] at h
    exact h
  -- at most one distinct factor
  have hcard : s.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro g₁ h₁ g₂ h₂
    by_contra hne
    have i1 : 1 ≤ g₁.natDegree := (hirr g₁ h₁).natDegree_pos
    have i2 : 1 ≤ g₂.natDegree := (hirr g₂ h₂).natDegree_pos
    have hsub : ({g₁, g₂} : Finset F[X]) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h₁
      · rw [Finset.mem_singleton] at hx; rw [hx]; exact h₂
    have hle : ({g₁, g₂} : Finset F[X]).sum (fun g => g.natDegree) ≤
        s.sum (fun g => g.natDegree) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.zero_le _)
    have hpair : ({g₁, g₂} : Finset F[X]).sum (fun g => g.natDegree) =
        g₁.natDegree + g₂.natDegree := by
      rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    omega
  -- hence exactly one factor, with multiplicity three
  obtain ⟨g, hgs⟩ : ∃ g, s = {g} := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · exfalso
      have hs0 : s = ∅ := Finset.card_eq_zero.mp h
      have hQ1 : Q = 1 := by
        rw [← Commons.FieldTheory.Polynomial.prod_normalizedFactors_of_monic Q hmon,
          Finset.prod_multiset_count, ← hs, hs0]
        simp
      rw [hQ1] at hdeg
      simp at hdeg
    · exact Finset.card_eq_one.mp (by omega)
  have hgnat : g.natDegree = 1 := by
    have : s.sum (fun g => g.natDegree) = g.natDegree := by rw [hgs]; simp
    have : g.natDegree * (normalizedFactors Q).count g = 3 := by
      have h : s.sum (fun g => g.natDegree * (normalizedFactors Q).count g) = 
          g.natDegree * (normalizedFactors Q).count g := by rw [hgs]; simp
      rw [← h]; exact hcount
    have hg1 : 1 ≤ g.natDegree := (hirr g (by rw [hgs]; exact Finset.mem_singleton_self g)).natDegree_pos
    omega
  have hgcount : (normalizedFactors Q).count g = 3 := by
    have h : s.sum (fun g => g.natDegree * (normalizedFactors Q).count g) =
        g.natDegree * (normalizedFactors Q).count g := by rw [hgs]; simp
    rw [h, hgnat, one_mul] at hcount
    exact hcount
  have hQ : Q = g ^ 3 := by
    have h1 : (normalizedFactors Q).prod = Q :=
      Commons.FieldTheory.Polynomial.prod_normalizedFactors_of_monic Q hmon
    rw [← h1, Finset.prod_multiset_count, ← hs, hgs]
    simp [hgcount]
  have hgmon : g.Monic := hmonic g (by rw [hgs]; exact Finset.mem_singleton_self g)
  have hcoeff1 : g.coeff 1 = 1 := by
    have := hgmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hgnat] at this
  have hgle : g = X + C (g.coeff 0) := by
    ext n
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp [Polynomial.coeff_X, hcoeff1]
      · have hz : g.coeff (n + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hgnat]; omega)
        simp [hz, Polynomial.coeff_X]
  refine ⟨-g.coeff 0, ?_⟩
  rw [hQ, hgle]
  simp


/-! ## The cubic congruence `index ≥ 2 ⟹ the linear and constant coefficients vanish` -/

/-- For `p > 3`, a monic cubic `X³ + bX + c` over `𝔽_p` of index at least two is
`X³`; equivalently `b = c = 0`.  (The index-`≥ 2` condition forces a triple
root, and the `X²`-coefficient vanishes by the trace-zero normalisation.) -/
theorem coeff_eq_zero_of_polyIndex_ge_two (p : ℕ) [Fact (Nat.Prime p)] (hp : 3 < p)
    (b c : ZMod p) (h : 2 ≤ polyIndex (X ^ 3 + C b * X + C c)) :
    b = 0 ∧ c = 0 := by
  classical
  set Q : (ZMod p)[X] := X ^ 3 + C b * X + C c with hQ
  have hh : 2 ≤ polyIndex Q := by rw [hQ]; exact h
  have hmon : Q.Monic := by rw [hQ]; monicity!
  have hdeg : Q.natDegree = 3 := by rw [hQ]; compute_degree!
  have hrad : (UniqueFactorizationMonoid.radical Q).natDegree ≤ 1 := by
    have h2 : polyIndex Q = Q.natDegree - (UniqueFactorizationMonoid.radical Q).natDegree := rfl
    omega
  obtain ⟨a, ha⟩ := eq_cube_of_monic_cubic_radical Q hmon hdeg hrad
  have hexp : (X - C a) ^ 3 = X ^ 3 - C (3 * a) * X ^ 2 + C (3 * a ^ 2) * X - C (a ^ 3) := by
    simp only [C_mul, C_pow, C_add, C_sub, C_neg, C_ofNat, C_1, C_0]
    ring
  have hfull : X ^ 3 + C b * X + C c
      = X ^ 3 - C (3 * a) * X ^ 2 + C (3 * a ^ 2) * X - C (a ^ 3) := by
    rw [← hQ, ha, hexp]
  have hc2 := congrArg (fun f : (ZMod p)[X] => f.coeff 2) hfull
  have hc1 := congrArg (fun f : (ZMod p)[X] => f.coeff 1) hfull
  have hc0 := congrArg (fun f : (ZMod p)[X] => f.coeff 0) hfull
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
    Polynomial.coeff_one, Polynomial.coeff_zero] at hc2 hc1 hc0
  norm_num at hc2 hc1 hc0
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hcon
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcon
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have ha0 : a = 0 := by
    rcases hc2 with h' | h'
    · exact absurd h' h3
    · exact h'
  subst ha0
  exact ⟨by simpa using hc1, by simpa using hc0⟩

end Submission.Vdw
