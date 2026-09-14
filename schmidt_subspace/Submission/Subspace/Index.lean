import Mathlib
import Submission.Commons.Algebra.MvPolynomial.index_add_ne_zero
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.min_weight_mul
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.Algebra.MvPolynomial.indexTay_pderivIter

/-!
# The index of a multivariate polynomial

Schmidt's subspace theorem (and Roth's lemma) are governed by the *index* of a polynomial
`P` at a point `α` with respect to weights `r` (Schmidt, LNM 785; survey arXiv:2502.00731,
§"Index"):

`Ind_{α,r}(P) = min { ∑ i, m i / r i : m ∈ support(Taylor_α P) }`,

where `Taylor_α P` is the expansion of `P` around `α`.  Equivalently, the minimum is over
multi-indices `m` with `(1/m!) ∂^m P (α) ≠ 0`.

The underlying Taylor shift `indexTay`, the weighted functional `indexWt` and the index set
`indexSet` (together with injectivity of the shift, its constant coefficient, nonnegativity,
the vanishing criterion for positive weights, and subadditivity) live in the shared commons
(`Commons.Algebra.MvPolynomial.indexTay/indexWt/indexSet`, `index_add_ne_zero`,
`index_properties_pos_vanishing`).  Here we bundle them as `index` and add further lemmas
(minimising monomial, multiplicativity in preparation).
-/

open scoped BigOperators

namespace Submission.Subspace

open Commons.Algebra.MvPolynomial (indexWt indexTay indexSet pderivIter)

variable {σ : Type*} [Fintype σ]

/-- The **index** of `P` at the point `α` with respect to the weights `r`. -/
noncomputable def index {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ)
    (P : MvPolynomial σ K) : ℝ :=
  sInf (indexSet α r P)

@[simp]
lemma index_def {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ)
    (P : MvPolynomial σ K) : index α r P = sInf (indexSet α r P) := rfl

/-- The index is nonnegative. -/
lemma index_nonneg {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ)
    (P : MvPolynomial σ K) : 0 ≤ index α r P :=
  Commons.Algebra.MvPolynomial.indexSet_sInf_nonneg α r P

/-- The index of the zero polynomial is `0` (an artefact of the `sInf ∅ = 0` convention). -/
lemma index_zero {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ) :
    index α r (0 : MvPolynomial σ K) = 0 := by
  rw [index_def]
  have h : indexSet α r (0 : MvPolynomial σ K) = (∅ : Set ℝ) := by
    ext t
    simp [indexSet, indexTay]
  rw [h, Real.sInf_empty]

/-- **Vanishing criterion** (positive weights).  A nonzero polynomial has index `0` iff it
does not vanish at `α`. -/
lemma index_eq_zero_iff {K : Type*} [Field K] [CharZero K] (α : σ → K) (r : σ → ℕ)
    (hr : ∀ i, 0 < r i) (P : MvPolynomial σ K) (hP : P ≠ 0) :
    index α r P = 0 ↔ MvPolynomial.eval α P ≠ 0 := by
  have h := (Commons.Algebra.MvPolynomial.index_properties_pos_vanishing α r hr).2.2 P hP
  simpa only [index_def, indexSet, indexTay, indexWt] using h

/-- **Subadditivity** (in the sharp form requiring `P + Q ≠ 0`). -/
lemma min_index_le_index_add {K : Type*} [Field K] [CharZero K] (α : σ → K) (r : σ → ℕ)
    (P Q : MvPolynomial σ K) (hPQ : P + Q ≠ 0) :
    min (index α r P) (index α r Q) ≤ index α r (P + Q) := by
  have h := Commons.Algebra.MvPolynomial.index_add_ne_zero (α := α) r P Q hPQ
  simpa only [index_def, indexSet, indexTay, indexWt] using h

/-- The index of a nonzero polynomial is attained at a monomial of its Taylor expansion. -/
lemma index_eq_indexWt_of_min {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ)
    (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ∃ m ∈ (indexTay α P).support,
      index α r P = indexWt r m ∧ ∀ m' ∈ (indexTay α P).support, indexWt r m ≤ indexWt r m' := by
  have hne : (indexTay α P).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr ((Commons.Algebra.MvPolynomial.indexTay_injective α).ne hP)
  obtain ⟨m, hm, hmin⟩ := (indexTay α P).support.exists_min_image (indexWt r) hne
  have himg : indexSet α r P = (((indexTay α P).support.image (indexWt r) : Finset ℝ) : Set ℝ) :=
    Commons.Algebra.MvPolynomial.indexSet_eq_image α r P
  have hmimg : indexWt r m ∈ (((indexTay α P).support.image (indexWt r) : Finset ℝ) : Set ℝ) :=
    Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hbdd : ∀ x ∈ (((indexTay α P).support.image (indexWt r) : Finset ℝ) : Set ℝ),
      (0 : ℝ) ≤ x := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rcases Finset.mem_image.mp hx with ⟨m', _, rfl⟩
    exact Commons.Algebra.MvPolynomial.indexWt_nonneg m'
  have hle : index α r P ≤ indexWt r m := by
    rw [index_def, himg]
    exact csInf_le ⟨0, hbdd⟩ hmimg
  have hge : indexWt r m ≤ index α r P := by
    rw [index_def, himg]
    exact le_csInf ⟨indexWt r m, hmimg⟩ (fun x hx => by
      rw [Finset.mem_coe] at hx
      rcases Finset.mem_image.mp hx with ⟨m', hm', rfl⟩
      exact hmin m' hm')
  exact ⟨m, hm, le_antisymm hle hge, hmin⟩

/-- **Multiplicativity** of the index: `Ind(PQ) = Ind(P) + Ind(Q)` (over a field). -/
lemma index_mul {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ)
    (P Q : MvPolynomial σ K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    index α r (P * Q) = index α r P + index α r Q := by
  have hP' : indexTay α P ≠ 0 := (Commons.Algebra.MvPolynomial.indexTay_injective α).ne hP
  have hQ' : indexTay α Q ≠ 0 := (Commons.Algebra.MvPolynomial.indexTay_injective α).ne hQ
  have h := Commons.Algebra.MvPolynomial.min_weight_mul (σ := σ) r (indexTay α P) (indexTay α Q)
    hP' hQ'
  have ht : indexTay α (P * Q) = indexTay α P * indexTay α Q := by
    simp only [indexTay, map_mul]
  simp only [index_def, indexSet, ht]
  simpa only [indexWt] using h

/-- The weighted functional is additive in the multi-index. -/
lemma indexWt_add (r : σ → ℕ) (m n : σ →₀ ℕ) :
    indexWt r (m + n) = indexWt r m + indexWt r n := by
  simp only [indexWt, Finsupp.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]

/-- **The index under differentiation** (survey §"Index", inequality under differentiation):
for a multi-index `m` with `∂^m P ≠ 0`,
`Ind(P) - ∑ᵢ mᵢ/rᵢ ≤ Ind(∂^m P)`. -/
lemma index_sub_indexWt_le_index_pderivIter {K : Type*} [Field K] [CharZero K]
    (α : σ → K) (r : σ → ℕ) (m : σ →₀ ℕ) (P : MvPolynomial σ K)
    (hQ : pderivIter m P ≠ 0) :
    index α r P - indexWt r m ≤ index α r (pderivIter m P) := by
  classical
  have htay : indexTay α (pderivIter m P) = pderivIter m (indexTay α P) :=
    Commons.Algebra.MvPolynomial.indexTay_pderivIter α m P
  have hQne : pderivIter m (indexTay α P) ≠ 0 := by
    rw [← htay]
    exact (Commons.Algebra.MvPolynomial.indexTay_injective α).ne hQ
  obtain ⟨n₀, hn₀⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hne : (indexSet α r (pderivIter m P)).Nonempty := by
    refine ⟨indexWt r n₀, ?_⟩
    change ∃ m' ∈ (indexTay α (pderivIter m P)).support, indexWt r n₀ = indexWt r m'
    exact ⟨n₀, by rw [htay]; exact hn₀, rfl⟩
  change sInf (indexSet α r P) - indexWt r m ≤ sInf (indexSet α r (pderivIter m P))
  refine le_csInf hne ?_
  intro b hb
  rcases hb with ⟨n, hn, rfl⟩
  rw [htay] at hn
  have hcoeff : MvPolynomial.coeff n (pderivIter m (indexTay α P)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hn
  rw [Commons.Algebra.MvPolynomial.coeff_pderivIter] at hcoeff
  have hcoeffQ : MvPolynomial.coeff (n + m) (indexTay α P) ≠ 0 := by
    intro h0
    exact hcoeff (by rw [h0, zero_mul])
  have hmem : n + m ∈ (indexTay α P).support := MvPolynomial.mem_support_iff.mpr hcoeffQ
  have hwt : indexWt r n = indexWt r (n + m) - indexWt r m := by
    have h := indexWt_add r n m
    linarith
  have hle : sInf (indexSet α r P) ≤ indexWt r (n + m) := by
    refine csInf_le ⟨0, ?_⟩ ?_
    · intro x hx
      rcases hx with ⟨m', _, rfl⟩
      exact Commons.Algebra.MvPolynomial.indexWt_nonneg m'
    · exact ⟨n + m, hmem, rfl⟩
  linarith

/-- The index is monotone under divisibility. -/
lemma index_le_of_dvd {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ)
    {P Q : MvPolynomial σ K} (hP : P ≠ 0) (hQ : Q ≠ 0) (hdvd : P ∣ Q) :
    index α r P ≤ index α r Q := by
  rcases hdvd with ⟨R, rfl⟩
  have hR : R ≠ 0 := by
    rintro rfl
    exact hQ (mul_zero P)
  rw [index_mul α r P R hP hR]
  have := index_nonneg α r R
  linarith

/-- The index of a constant polynomial is `0`. -/
lemma index_C {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ) (c : K) :
    index α r (MvPolynomial.C c) = 0 := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [map_zero]
    exact index_zero α r
  · have htay : indexTay α (MvPolynomial.C c) = MvPolynomial.C c := by simp [indexTay]
    have hmem : indexWt r (0 : σ →₀ ℕ) ∈ indexSet α r (MvPolynomial.C c) := by
      refine ⟨0, ?_, rfl⟩
      rw [htay]
      exact MvPolynomial.mem_support_iff.mpr (by simpa using hc)
    have hmem0 : (0 : ℝ) ∈ indexSet α r (MvPolynomial.C c) := by
      rw [← Commons.Algebra.MvPolynomial.indexWt_zero r]
      exact hmem
    rw [index_def]
    refine le_antisymm ?_ (le_csInf ⟨_, hmem0⟩ ?_)
    · exact csInf_le ⟨0, fun x hx => by
        rcases hx with ⟨m', _, rfl⟩
        exact Commons.Algebra.MvPolynomial.indexWt_nonneg m'⟩ hmem0
    · intro b hb
      rcases hb with ⟨m', _, rfl⟩
      exact Commons.Algebra.MvPolynomial.indexWt_nonneg m'

/-- The index is invariant under multiplying by a nonzero constant. -/
lemma index_C_mul {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ) (c : K) (hc : c ≠ 0)
    (P : MvPolynomial σ K) (hP : P ≠ 0) :
    index α r (MvPolynomial.C c * P) = index α r P := by
  rw [index_mul α r (MvPolynomial.C c) P (MvPolynomial.C_ne_zero.mpr hc) hP, index_C, zero_add]

/-- **Multiplicativity over a finite product.** -/
lemma index_prod {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ) {ι : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ K) (hP : ∀ i ∈ s, P i ≠ 0) :
    index α r (∏ i ∈ s, P i) = ∑ i ∈ s, index α r (P i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using index_C α r (1 : K)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        index_mul α r (P a) (∏ i ∈ s, P i) (hP a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr (fun i hi => hP i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))]

/-- **Subadditivity over a finite sum.**  Some summand has index at most that of the sum. -/
lemma exists_index_le_index_sum {K : Type*} [Field K] [CharZero K] (α : σ → K) (r : σ → ℕ)
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ K)
    (hne : ∑ i ∈ s, P i ≠ 0) :
    ∃ j ∈ s, index α r (P j) ≤ index α r (∑ i ∈ s, P i) := by
  classical
  refine Finset.induction
    (motive := fun s => ∀ P : ι → MvPolynomial σ K,
      (∑ i ∈ s, P i) ≠ 0 → ∃ j ∈ s, index α r (P j) ≤ index α r (∑ i ∈ s, P i))
    ?_ ?_ s P hne
  · intro P hne
    exact absurd rfl hne
  · intro a s ha ih P hne
    rw [Finset.sum_insert ha] at hne ⊢
    by_cases hs0 : (∑ i ∈ s, P i) = 0
    · rw [hs0, add_zero] at hne ⊢
      exact ⟨a, Finset.mem_insert_self a s, le_rfl⟩
    · have hmin := min_index_le_index_add α r (P a) (∑ i ∈ s, P i) hne
      rcases le_or_gt (index α r (P a)) (index α r (∑ i ∈ s, P i)) with hle | hlt
      · rw [min_eq_left hle] at hmin
        exact ⟨a, Finset.mem_insert_self a s, hmin⟩
      · rw [min_eq_right (le_of_lt hlt)] at hmin
        obtain ⟨j, hj, hjle⟩ := ih P hs0
        exact ⟨j, Finset.mem_insert_of_mem hj, le_trans hjle hmin⟩

/-- **Multiplicativity for powers.** -/
lemma index_pow {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ) (P : MvPolynomial σ K)
    (hP : P ≠ 0) (n : ℕ) : index α r (P ^ n) = (n : ℝ) * index α r P := by
  induction n with
  | zero => simpa using index_C α r (1 : K)
  | succ n ih =>
      rw [pow_succ, index_mul α r (P ^ n) P (pow_ne_zero n hP) hP, ih]
      push_cast
      ring

/-- The index of a finite product is the sum of the indices. -/
lemma index_prod_univ {K : Type*} [Field K] (α : σ → K) (r : σ → ℕ) {κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial σ K) (hP : ∀ i, P i ≠ 0) :
    index α r (∏ i, P i) = ∑ i, index α r (P i) := by
  simpa using index_prod α r (Finset.univ : Finset κ) P (fun i _ => hP i)

end Submission.Subspace
