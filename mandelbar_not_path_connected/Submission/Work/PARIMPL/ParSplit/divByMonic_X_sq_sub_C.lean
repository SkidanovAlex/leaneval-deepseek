import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

open scoped BigOperators

/-- Telescoping identity for the geometric-type sums appearing in the division by `X ^ 2 - C g`.

`∑_{j<N+1} g^j a(m+2j) - g ∑_{j<N+1} g^j a(m+2+2j) = a m - g^{N+1} a(m+2(N+1))`. -/
private lemma telescoping (a : ℕ → ℂ) (g : ℂ) (m N : ℕ) :
    (∑ j ∈ Finset.range (N+1), g^j * a (m + 2*j))
    - g * (∑ j ∈ Finset.range (N+1), g^j * a (m + 2 + 2*j))
    = a m - g^(N+1) * a (m + 2*(N+1)) := by
  have hg : g * (∑ j ∈ Finset.range (N+1), g^j * a (m + 2 + 2*j))
      = ∑ j ∈ Finset.range (N+1), g^(j+1) * a (m + 2*(j+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hidx : m + 2 + 2*j = m + 2*(j+1) := by omega
    rw [← mul_assoc, ← pow_succ', hidx]
  rw [hg]
  have e1 : (∑ j ∈ Finset.range (N+1), g^j * a (m + 2*j))
      = (∑ k ∈ Finset.range N, g^(k+1) * a (m + 2*(k+1))) + (g^0 * a (m + 2*0)) :=
    Finset.sum_range_succ' (fun k => g^k * a (m + 2*k)) N
  have e2 : (∑ j ∈ Finset.range (N+1), g^(j+1) * a (m + 2*(j+1)))
      = (∑ k ∈ Finset.range N, g^(k+1) * a (m + 2*(k+1))) + (g^(N+1) * a (m + 2*(N+1))) :=
    Finset.sum_range_succ (fun k => g^(k+1) * a (m + 2*(k+1))) N
  rw [e1, e2]
  simp only [pow_zero, one_mul, Nat.mul_zero, Nat.add_zero]
  ring

/-- The telescoping identity written with the index `(m-2)` in the first sum. -/
private lemma telescoping2 (a : ℕ → ℂ) (g : ℂ) (m N : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ Finset.range (N+1), g^j * a ((m-2) + 2 + 2*j))
    - g * (∑ j ∈ Finset.range (N+1), g^j * a (m + 2 + 2*j))
    = a m - g^(N+1) * a (m + 2*(N+1)) := by
  have h1 : (∑ j ∈ Finset.range (N+1), g^j * a ((m-2) + 2 + 2*j))
      = (∑ j ∈ Finset.range (N+1), g^j * a (m + 2*j)) := by
    apply Finset.sum_congr rfl
    intro j _
    have : (m-2) + 2 + 2*j = m + 2*j := by omega
    rw [this]
  rw [h1, telescoping a g m N]

/-- Coefficient of `∑_{k<N+1} C (s k) * X^k` is `s m`, provided `s` vanishes above `N`. -/
private lemma coeff_Q (s : ℕ → ℂ) (N : ℕ) (hs : ∀ m, N < m → s m = 0) (m : ℕ) :
    (∑ k ∈ Finset.range (N+1), Polynomial.C (s k) * Polynomial.X ^ k).coeff m = s m := by
  have h1 : (∑ k ∈ Finset.range (N+1), Polynomial.C (s k) * Polynomial.X ^ k).coeff m
        = ∑ k ∈ Finset.range (N+1), (if m = k then s k else 0) := by simp
  rw [h1, Finset.sum_ite_eq]
  by_cases hm : m < N + 1
  · rw [ite_eq_left (Finset.mem_range.mpr hm)]
  · rw [ite_eq_right (by simpa [Finset.mem_range] using hm)]
    exact (hs m (by omega)).symm

theorem divByMonic_X_sq_sub_C {P : Polynomial ℂ} {g : ℂ} :
    P /ₘ (Polynomial.X ^ 2 - Polynomial.C g) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (∑ j ∈ Finset.range (P.natDegree + 1), g ^ j * P.coeff (k + 2 + 2 * j))
          * Polynomial.X ^ k := by
  set A : Polynomial ℂ := Polynomial.X ^ 2 - Polynomial.C g with hA
  set s : ℕ → ℂ := fun k =>
    ∑ j ∈ Finset.range (P.natDegree + 1), g ^ j * P.coeff (k + 2 + 2 * j) with hs
  set Q : Polynomial ℂ :=
    ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (s k) * Polynomial.X ^ k with hQ
  have hmonic : A.Monic := by
    rw [hA]; exact Polynomial.monic_X_pow_sub_C g (by norm_num)
  have hQc : ∀ m, Q.coeff m = s m := by
    intro m
    rw [hQ]
    refine coeff_Q s P.natDegree ?_ m
    intro n hn
    simp only [hs]
    apply Finset.sum_eq_zero
    intro j _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (show P.natDegree < n + 2 + 2 * j by omega), mul_zero]
  have hAQ : ∀ m, 2 ≤ m → (A * Q).coeff m = P.coeff m := by
    intro m hm
    have hc : (A * Q).coeff m = s (m - 2) - g * s m := by
      rw [hA, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul' Q 2 m,
        Polynomial.coeff_C_mul]
      rw [ite_eq_left hm]
      rw [hQc, hQc]
    rw [hc]
    have ht := telescoping2 P.coeff g m P.natDegree hm
    have hs1 : s (m - 2) =
        ∑ j ∈ Finset.range (P.natDegree + 1), g ^ j * P.coeff ((m - 2) + 2 + 2 * j) := by
      simp only [hs]
    have hs2 : s m =
        ∑ j ∈ Finset.range (P.natDegree + 1), g ^ j * P.coeff (m + 2 + 2 * j) := by
      simp only [hs]
    rw [hs1, hs2, ht]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (show P.natDegree < m + 2*(P.natDegree+1) by omega), mul_zero, sub_zero]
  have hdeg : (P - A * Q).degree < ((2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [Polynomial.coeff_sub, hAQ m hm, sub_self]
  have hdegA : (P - A * Q).degree < A.degree := by
    have h2 : A.degree = ((2 : ℕ) : WithBot ℕ) := by
      rw [hA]; exact Polynomial.degree_X_pow_sub_C (by norm_num) g
    rw [h2]; exact hdeg
  have hmain : P /ₘ A = Q := by
    refine (Polynomial.div_modByMonic_unique Q (P - A*Q) hmonic ⟨?_, hdegA⟩).1
    exact sub_add_cancel P (A*Q)
  exact hmain

end Work.PARIMPL.ParSplit
