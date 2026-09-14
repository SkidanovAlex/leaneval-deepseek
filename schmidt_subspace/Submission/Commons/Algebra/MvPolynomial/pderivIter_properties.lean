import Mathlib.Algebra.MvPolynomial.PDeriv

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators
open _root_.MvPolynomial

/-- Iterated formal partial derivative `∂^m` of a multivariate polynomial, indexed by a
multi-index `m : σ →₀ ℕ`.  On a monomial it is given by
`∂^m (c • X^{m'}) = (c * ∏ i, (m' i).descFactorial (m i)) • X^{m' - m}` if `m ≤ m'` and `0`
otherwise. -/
noncomputable def pderivIter {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ m' ∈ P.support,
    if h : m ≤ m' then
      MvPolynomial.monomial (m' - m) (P.coeff m' * ∏ i : σ, (m' i).descFactorial (m i))
    else 0

/-- The monomial-wise formula underlying `pderivIter`: the image of the monomial
`monomial s a` under `∂^m`. -/
noncomputable def pderivIterMonomial {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m s : σ →₀ ℕ) (a : R) : MvPolynomial σ R :=
  if h : m ≤ s then
    MvPolynomial.monomial (s - m) (a * ∏ i : σ, (s i).descFactorial (m i))
  else 0

theorem pderivIter_eq_sum {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    pderivIter m P = ∑ s ∈ P.support, pderivIterMonomial m s (P.coeff s) := rfl

theorem pderivIterMonomial_zero {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m s : σ →₀ ℕ) : pderivIterMonomial m s (0 : R) = 0 := by
  rw [pderivIterMonomial]
  split
  · rw [zero_mul, MvPolynomial.monomial_zero]
  · rfl

theorem pderivIter_eq_sum_of_subset {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) {P : MvPolynomial σ R} {T : Finset (σ →₀ ℕ)} (h : P.support ⊆ T) :
    pderivIter m P = ∑ s ∈ T, pderivIterMonomial m s (P.coeff s) := by
  rw [pderivIter_eq_sum]
  exact Finset.sum_subset h fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.mp hx, pderivIterMonomial_zero]

theorem pderivIterMonomial_zero_index {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (s : σ →₀ ℕ) (a : R) :
    pderivIterMonomial (0 : σ →₀ ℕ) s a = MvPolynomial.monomial s a := by
  rw [pderivIterMonomial]
  simp

theorem pderivIterMonomial_C_mul {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m s : σ →₀ ℕ) (c a : R) :
    pderivIterMonomial m s (c * a) = MvPolynomial.C c * pderivIterMonomial m s a := by
  by_cases h : m ≤ s
  · rw [pderivIterMonomial, pderivIterMonomial, dif_pos h, dif_pos h, mul_assoc,
      MvPolynomial.C_mul_monomial]
  · rw [pderivIterMonomial, pderivIterMonomial, dif_neg h, dif_neg h, mul_zero]

theorem pderivIterMonomial_single {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (i : σ) (s : σ →₀ ℕ) (a : R) :
    pderivIterMonomial (Finsupp.single i 1) s a = MvPolynomial.pderiv i (MvPolynomial.monomial s a) := by
  classical
  rw [MvPolynomial.pderiv_monomial, pderivIterMonomial]
  by_cases h : Finsupp.single i 1 ≤ s
  · rw [dif_pos h]
    have hp : (∏ j : σ, (s j).descFactorial ((Finsupp.single i 1) j)) = s i := by
      rw [Finset.prod_eq_single i]
      · rw [Finsupp.single_eq_same, Nat.descFactorial_one]
      · intro b _ hb
        rw [Finsupp.single_eq_of_ne hb, Nat.descFactorial_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hp]
  · rw [dif_neg h]
    have hs : s i = 0 := by
      rw [Finsupp.single_le_iff] at h
      omega
    rw [hs, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]

theorem le_add_single_iff {σ : Type*} [Fintype σ] (m s : σ →₀ ℕ) (i : σ) :
    m + Finsupp.single i 1 ≤ s ↔ m ≤ s ∧ (s - m) i ≠ 0 := by
  constructor
  · intro h
    refine ⟨le_trans (le_add_right (le_refl m)) h, ?_⟩
    have hi : m i + 1 ≤ s i := by
      have h' := (Finsupp.le_def.mp h) i
      rwa [Finsupp.add_apply, Finsupp.single_eq_same] at h'
    rw [Finsupp.tsub_apply]
    omega
  · rintro ⟨hle, hne⟩
    rw [Finsupp.le_def] at hle
    rw [Finsupp.le_def]
    intro j
    rw [Finsupp.add_apply]
    by_cases hj : j = i
    · rw [hj, Finsupp.single_eq_same]
      have hz : s i - m i ≠ 0 := by simpa [Finsupp.tsub_apply] using hne
      omega
    · rw [Finsupp.single_eq_of_ne hj, add_zero]
      exact hle j

theorem prod_descFactorial_add_single {σ : Type*} [Fintype σ] (m s : σ →₀ ℕ) (i : σ) :
    (∏ j : σ, (s j).descFactorial ((m + Finsupp.single i 1 : σ →₀ ℕ) j)) =
      (∏ j : σ, (s j).descFactorial (m j)) * (s i - m i) := by
  classical
  have hf : (∏ j : σ, (s j).descFactorial ((m + Finsupp.single i 1 : σ →₀ ℕ) j))
      = (s i).descFactorial ((m + Finsupp.single i 1 : σ →₀ ℕ) i) *
        ∏ j ∈ ({i}ᶜ : Finset σ), (s j).descFactorial ((m + Finsupp.single i 1 : σ →₀ ℕ) j) :=
    Fintype.prod_eq_mul_prod_compl i _
  have hg : (∏ j : σ, (s j).descFactorial (m j))
      = (s i).descFactorial (m i) * ∏ j ∈ ({i}ᶜ : Finset σ), (s j).descFactorial (m j) :=
    Fintype.prod_eq_mul_prod_compl i _
  have hcompl : ∏ j ∈ ({i}ᶜ : Finset σ), (s j).descFactorial ((m + Finsupp.single i 1 : σ →₀ ℕ) j)
      = ∏ j ∈ ({i}ᶜ : Finset σ), (s j).descFactorial (m j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hji, add_zero]
  rw [hf, hg, hcompl, Finsupp.add_apply, Finsupp.single_eq_same, Nat.descFactorial_succ]
  ring

theorem pderiv_pderivIterMonomial {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (i : σ) (m s : σ →₀ ℕ) (a : R) :
    MvPolynomial.pderiv i (pderivIterMonomial m s a) =
      pderivIterMonomial (m + Finsupp.single i 1) s a := by
  have hsub : s - (m + Finsupp.single i 1) = (s - m) - Finsupp.single i 1 := by
    ext j
    by_cases hj : j = i
    · rw [hj]
      simp [Finsupp.tsub_apply, Finsupp.add_apply, Nat.sub_sub]
    · simp [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne hj]
  rw [pderivIterMonomial, pderivIterMonomial]
  by_cases hA : m ≤ s
  · rw [dif_pos hA]
    by_cases hB : m + Finsupp.single i 1 ≤ s
    · rw [dif_pos hB, MvPolynomial.pderiv_monomial, hsub]
      congr 1
      rw [prod_descFactorial_add_single, Finsupp.tsub_apply, Nat.cast_mul, mul_assoc]
    · rw [dif_neg hB, MvPolynomial.pderiv_monomial]
      have hz : (s - m) i = 0 := by
        by_contra h
        exact hB ((le_add_single_iff m s i).mpr ⟨hA, h⟩)
      rw [hz, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
  · have hB' : ¬ (m + Finsupp.single i 1 ≤ s) :=
      fun h => hA ((le_add_single_iff m s i).mp h).1
    rw [dif_neg hA, dif_neg hB', Derivation.map_zero]

theorem pderivIter_properties {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ] :
    (∀ P : MvPolynomial σ R, pderivIter (0 : σ →₀ ℕ) P = P) ∧
    (∀ (i : σ) (P : MvPolynomial σ R),
      pderivIter (Finsupp.single i 1) P = MvPolynomial.pderiv i P) ∧
    (∀ (i : σ) (m : σ →₀ ℕ) (P : MvPolynomial σ R),
      MvPolynomial.pderiv i (pderivIter m P) = pderivIter (m + Finsupp.single i 1) P) ∧
    (∀ (m : σ →₀ ℕ) (c : R) (P : MvPolynomial σ R),
      pderivIter m (MvPolynomial.C c * P) = MvPolynomial.C c * pderivIter m P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P
    rw [pderivIter_eq_sum]
    rw [Finset.sum_congr rfl fun s _ => pderivIterMonomial_zero_index s (P.coeff s)]
    exact MvPolynomial.support_sum_monomial_coeff P
  · intro i P
    have h1 : (∑ s ∈ P.support, pderivIterMonomial (Finsupp.single i 1) s (P.coeff s))
        = ∑ s ∈ P.support, MvPolynomial.pderiv i (MvPolynomial.monomial s (P.coeff s)) :=
      Finset.sum_congr rfl fun s _ => pderivIterMonomial_single i s (P.coeff s)
    rw [pderivIter_eq_sum, h1, ← map_sum (MvPolynomial.pderiv i)
      (fun s => MvPolynomial.monomial s (P.coeff s)), MvPolynomial.support_sum_monomial_coeff]
  · intro i m P
    have h1 : MvPolynomial.pderiv i (pderivIter m P)
        = ∑ s ∈ P.support, MvPolynomial.pderiv i (pderivIterMonomial m s (P.coeff s)) := by
      rw [pderivIter_eq_sum, map_sum]
    have h2 : (∑ s ∈ P.support, MvPolynomial.pderiv i (pderivIterMonomial m s (P.coeff s)))
        = ∑ s ∈ P.support, pderivIterMonomial (m + Finsupp.single i 1) s (P.coeff s) :=
      Finset.sum_congr rfl fun s _ => pderiv_pderivIterMonomial i m s (P.coeff s)
    rw [h1, h2, ← pderivIter_eq_sum]
  · intro m c P
    have hsub : (MvPolynomial.C c * P).support ⊆ P.support := by
      intro s hs
      rw [MvPolynomial.mem_support_iff] at hs ⊢
      intro h
      exact hs (by rw [MvPolynomial.coeff_C_mul, h, mul_zero])
    have h2 : (∑ s ∈ P.support, pderivIterMonomial m s (MvPolynomial.coeff s (MvPolynomial.C c * P)))
        = MvPolynomial.C c * ∑ s ∈ P.support, pderivIterMonomial m s (MvPolynomial.coeff s P) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [MvPolynomial.coeff_C_mul]
      exact pderivIterMonomial_C_mul m s c (MvPolynomial.coeff s P)
    rw [pderivIter_eq_sum_of_subset m hsub, h2, ← pderivIter_eq_sum]

end Commons.Algebra.MvPolynomial