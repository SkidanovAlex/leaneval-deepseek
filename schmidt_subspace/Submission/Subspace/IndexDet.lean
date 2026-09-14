import Mathlib
import Submission.Subspace.Index

/-!
# The index of a determinant

The classical determinant bound for the index (Schmidt, *Diophantine approximation*, and the
survey arXiv:2502.00731, §"Roth's lemma"): if `A` is a `k × k` matrix of polynomials and every
entry of the `j`-th column has index at least `b j` (or is zero), then every summand in the
Laplace expansion of `det A` — and hence the determinant itself — has index at least
`∑ j, b j`.

The reason the statement is phrased with "or is zero" is that the paper's index of the zero
polynomial is `+∞` whereas our `index` (an `sInf` over an empty set) is `0`.  The predicate
`IndexGE` below captures the paper's convention in a way that is closed under addition and
multiplication, which is exactly what the Laplace expansion needs.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K]

/-- `IndexGE α r t P` says that `P` vanishes at `α` to index at least `t`, with the convention
`Ind(0) = +∞`: thus either `P = 0`, or its index is at least `t`. -/
def IndexGE (α : σ → K) (r : σ → ℕ) (t : ℝ) (P : MvPolynomial σ K) : Prop :=
  P = 0 ∨ t ≤ index α r P

lemma indexGE_iff {α : σ → K} {r : σ → ℕ} {t : ℝ} {P : MvPolynomial σ K} :
    IndexGE α r t P ↔ P = 0 ∨ t ≤ index α r P := Iff.rfl

lemma indexGE_zero (α : σ → K) (r : σ → ℕ) (t : ℝ) :
    IndexGE α r t (0 : MvPolynomial σ K) := Or.inl rfl

lemma IndexGE.mono {α : σ → K} {r : σ → ℕ} {s t : ℝ} {P : MvPolynomial σ K}
    (h : IndexGE α r t P) (hts : s ≤ t) : IndexGE α r s P :=
  h.imp id (fun h => le_trans hts h)

lemma indexGE_one [CharZero K] (α : σ → K) (r : σ → ℕ) {t : ℝ} (ht : t ≤ 0) :
    IndexGE α r t (1 : MvPolynomial σ K) := by
  refine Or.inr ?_
  rw [show (1 : MvPolynomial σ K) = MvPolynomial.C 1 from by simp, index_C]
  linarith

lemma IndexGE.of_le {α : σ → K} {r : σ → ℕ} {s t : ℝ} {P : MvPolynomial σ K}
    (h : IndexGE α r t P) (ht : s ≤ t) : IndexGE α r s P := h.mono ht

lemma indexGE_neg [CharZero K] {α : σ → K} {r : σ → ℕ} {t : ℝ} {P : MvPolynomial σ K} :
    IndexGE α r t (-P) ↔ IndexGE α r t P := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  have hneg : -P ≠ 0 := neg_ne_zero.mpr hP
  have : index α r (-P) = index α r P := by
    rw [show -P = MvPolynomial.C (-1 : K) * P from by simp]
    exact index_C_mul α r (-1) (by norm_num) P hP
  simp only [IndexGE, hneg, hP, false_or, this]

lemma indexGE_add [CharZero K] {α : σ → K} {r : σ → ℕ} {t : ℝ} {P Q : MvPolynomial σ K}
    (hP : IndexGE α r t P) (hQ : IndexGE α r t Q) : IndexGE α r t (P + Q) := by
  by_cases hP0 : P = 0
  · rw [hP0, zero_add]; exact hQ
  by_cases hQ0 : Q = 0
  · rw [hQ0, add_zero]; exact hP
  have hp : t ≤ index α r P := hP.resolve_left hP0
  have hq : t ≤ index α r Q := hQ.resolve_left hQ0
  rcases eq_or_ne (P + Q) 0 with h | h
  · exact Or.inl h
  exact Or.inr (le_trans (le_min hp hq) (min_index_le_index_add α r P Q h))

lemma indexGE_finset_sum [CharZero K] {α : σ → K} {r : σ → ℕ} {t : ℝ} {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial σ K) (h : ∀ i ∈ s, IndexGE α r t (f i)) :
    IndexGE α r t (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using indexGE_zero α r t
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact indexGE_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma indexGE_mul [CharZero K] {α : σ → K} {r : σ → ℕ} {s t : ℝ} {P Q : MvPolynomial σ K}
    (hP : IndexGE α r s P) (hQ : IndexGE α r t Q) : IndexGE α r (s + t) (P * Q) := by
  by_cases hP0 : P = 0
  · rw [hP0, zero_mul]; exact indexGE_zero α r _
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero]; exact indexGE_zero α r _
  rcases eq_or_ne (P * Q) 0 with h | h
  · exact Or.inl h
  have hp : s ≤ index α r P := hP.resolve_left hP0
  have hq : t ≤ index α r Q := hQ.resolve_left hQ0
  exact Or.inr (by rw [index_mul α r P Q hP0 hQ0]; linarith)

lemma indexGE_C_mul [CharZero K] {α : σ → K} {r : σ → ℕ} {t : ℝ} (c : K) {P : MvPolynomial σ K}
    (hc : c ≠ 0) : IndexGE α r t (MvPolynomial.C c * P) ↔ IndexGE α r t P := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  have hsm : MvPolynomial.C c * P ≠ 0 := mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc) hP
  have : index α r (MvPolynomial.C c * P) = index α r P := index_C_mul α r c hc P hP
  simp only [IndexGE, hsm, hP, false_or, this]

lemma indexGE_prod [CharZero K] {α : σ → K} {r : σ → ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial σ K) (b : ι → ℝ)
    (h : ∀ i ∈ s, IndexGE α r (b i) (f i)) : IndexGE α r (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using indexGE_one α r (le_refl (0 : ℝ))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact indexGE_mul (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Scaling a polynomial by a unit `±1` does not change its index. -/
lemma indexGE_units_smul [CharZero K] {α : σ → K} {r : σ → ℕ} {t : ℝ} (u : ℤˣ)
    {P : MvPolynomial σ K} (h : IndexGE α r t P) : IndexGE α r t (u • P) := by
  rcases Int.units_eq_one_or u with hu | hu
  · rw [hu]; simpa using h
  · rw [hu]
    simpa using indexGE_neg.mpr h

/-- **The index of a determinant.**  If every entry of the `j`-th column of `A` is either `0`
or has index at least `b j`, then `det A` is either `0` or has index at least `∑ j, b j`. -/
theorem indexGE_det [CharZero K] {k : ℕ} {α : σ → K} {r : σ → ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial σ K)) (b : Fin k → ℝ)
    (hA : ∀ i j, IndexGE α r (b j) (A i j)) :
    IndexGE α r (∑ j, b j) A.det := by
  classical
  rw [Matrix.det_apply]
  refine indexGE_finset_sum _ _ (fun σ' _ => ?_)
  exact indexGE_units_smul _ (indexGE_prod Finset.univ (fun i => A (σ' i) i) b
    (fun i _ => hA (σ' i) i))

/-- **Lower bound for the index of a determinant** (Schmidt).  If `det A ≠ 0` and every entry of
the `j`-th column has index at least `b j` (zeros being allowed, with the convention that a
zero entry satisfies every bound), then `∑ j, b j ≤ Ind(det A)`. -/
theorem index_det_ge [CharZero K] {k : ℕ} {α : σ → K} {r : σ → ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial σ K)) (hdet : A.det ≠ 0) (b : Fin k → ℝ)
    (hA : ∀ i j, A i j = 0 ∨ b j ≤ index α r (A i j)) :
    ∑ j, b j ≤ index α r A.det := by
  rcases indexGE_det A b hA with h | h
  · exact absurd h hdet
  · exact h

/-- **Lower bound for the index of a determinant, in terms of column minima.**  If `det A ≠ 0`
and `b j` is at most the index of every entry of the `j`-th column that is nonzero, then
`∑ j, b j ≤ Ind(det A)`. -/
theorem index_det_ge_min [CharZero K] {k : ℕ} {α : σ → K} {r : σ → ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial σ K)) (hdet : A.det ≠ 0) (b : Fin k → ℝ)
    (hA : ∀ i j, A i j ≠ 0 → b j ≤ index α r (A i j)) :
    ∑ j, b j ≤ index α r A.det :=
  index_det_ge A hdet b fun i j => by
    by_cases h : A i j = 0
    · exact Or.inl h
    · exact Or.inr (hA i j h)

end Submission.Subspace
