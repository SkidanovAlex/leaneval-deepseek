import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.trace_adjoint_comp_eq_coord_sq_sum
import Submission.Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq

namespace Commons.Analysis.Sigma2

open scoped BigOperators

/-! ## Elementary algebra of triangular pair sums

These two combinatorial lemmas are the core of the identity
`∑_{i<j} (A_{ii}A_{jj} - A_{ij}²) = (tr T² - tr T²)/2`
for the coordinate matrix `A_{ij} = ⟪T vᵢ, vⱼ⟫` of a self-adjoint operator in an
orthonormal basis, stated here for an arbitrary finite linearly ordered index type. -/

private lemma ite_lt_trichotomy {ι : Type*} [LinearOrder ι] (i j : ι) (x : ℝ) :
    x = (if i = j then x else 0) + (if i < j then x else 0) + (if j < i then x else 0) := by
  rcases lt_trichotomy i j with h | h | h
  · have hji : ¬ j < i := lt_asymm h
    have hij : ¬ i = j := h.ne
    simp [h, hji, hij]
  · subst h; simp
  · have hij : ¬ i < j := lt_asymm h
    have hne : ¬ i = j := (ne_of_lt h).symm
    simp [h, hij, hne]

private lemma ite_sub_real {p : Prop} [Decidable p] (x y : ℝ) :
    (if p then x - y else 0) = (if p then x else 0) - (if p then y else 0) := by
  by_cases h : p <;> simp [h]

private lemma pairSum_sq_gen {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → ℝ) :
    (∑ i : ι, a i) ^ 2 =
      (∑ i : ι, (a i) ^ 2) + 2 * (∑ j : ι, ∑ i : ι, if i < j then a i * a j else 0) := by
  let M : ℝ := ∑ i : ι, ∑ j : ι, if i < j then a i * a j else 0
  let R : ℝ := ∑ i : ι, ∑ j : ι, if j < i then a i * a j else 0
  let P : ℝ := ∑ j : ι, ∑ i : ι, if i < j then a i * a j else 0
  have hsplit :
      (∑ i : ι, ∑ j : ι, a i * a j) =
        (∑ i : ι, ∑ j : ι, if i = j then a i * a j else 0) +
          (∑ i : ι, ∑ j : ι, if i < j then a i * a j else 0) +
            (∑ i : ι, ∑ j : ι, if j < i then a i * a j else 0) := by
    calc
      (∑ i : ι, ∑ j : ι, a i * a j) =
          ∑ i : ι, ((∑ j : ι, if i = j then a i * a j else 0) +
            (∑ j : ι, if i < j then a i * a j else 0) +
              (∑ j : ι, if j < i then a i * a j else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact ite_lt_trichotomy i j (a i * a j)
      _ = (∑ i : ι, ∑ j : ι, if i = j then a i * a j else 0) +
          (∑ i : ι, ∑ j : ι, if i < j then a i * a j else 0) +
            (∑ i : ι, ∑ j : ι, if j < i then a i * a j else 0) := by
        simp [Finset.sum_add_distrib, add_assoc]
  have hdiag : (∑ i : ι, ∑ j : ι, if i = j then a i * a j else 0) =
      ∑ i : ι, a i * a i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.sum_ite_eq]
  have hP : P = M := by
    dsimp [P, M]
    rw [Finset.sum_comm]
  have hR : R = M := by
    dsimp [R]
    calc
      (∑ i : ι, ∑ j : ι, if j < i then a i * a j else 0) =
          ∑ j : ι, ∑ i : ι, if i < j then a j * a i else 0 := by rfl
      _ = (∑ j : ι, ∑ i : ι, if i < j then a i * a j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
      _ = M := by
        dsimp [M]
        rw [Finset.sum_comm]
  have hmainsq : (∑ i : ι, a i) ^ 2 = (∑ i : ι, a i * a i) + M + R := by
    calc
      (∑ i : ι, a i) ^ 2 = (∑ i : ι, a i) * (∑ i : ι, a i) := by rw [pow_two]
      _ = ∑ i : ι, ∑ j : ι, a i * a j := by rw [Fintype.sum_mul_sum]
      _ = (∑ i : ι, ∑ j : ι, if i = j then a i * a j else 0) +
          (∑ i : ι, ∑ j : ι, if i < j then a i * a j else 0) +
            (∑ i : ι, ∑ j : ι, if j < i then a i * a j else 0) := hsplit
      _ = (∑ i : ι, a i * a i) + M + R := by
        rw [hdiag]
  calc
    (∑ i : ι, a i) ^ 2 = (∑ i : ι, a i * a i) + M + R := hmainsq
    _ = (∑ i : ι, (a i) ^ 2) + 2 * P := by
      rw [hR, hP]
      simp [pow_two, two_mul, add_assoc]

private lemma pairSum_eq_gen {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → ℝ) :
    (∑ j : ι, ∑ i : ι, if i < j then a i * a j else 0) =
      ((∑ i : ι, a i) ^ 2 - ∑ i : ι, (a i) ^ 2) / 2 := by
  have h := pairSum_sq_gen (a := a)
  linarith

private lemma two_mul_sum_lt_sq_gen {ι : Type*} [Fintype ι] [LinearOrder ι]
    (B : ι → ι → ℝ) (hB : ∀ i j, B i j = B j i) :
    2 * (∑ j : ι, ∑ i : ι, if i < j then B i j else 0)
      = (∑ i : ι, ∑ j : ι, B i j) - (∑ i : ι, B i i) := by
  let Q : ℝ := ∑ j : ι, ∑ i : ι, if i < j then B i j else 0
  let P : ℝ := ∑ i : ι, ∑ j : ι, if i < j then B i j else 0
  let R : ℝ := ∑ i : ι, ∑ j : ι, if j < i then B i j else 0
  let Diag : ℝ := ∑ i : ι, ∑ j : ι, if i = j then B i j else 0
  have hPQ : P = Q := by
    dsimp only [P, Q]; rw [Finset.sum_comm]
  have hRQ : R = Q := by
    dsimp only [R, Q]
    calc (∑ i : ι, ∑ j : ι, if j < i then B i j else 0)
        = (∑ j : ι, ∑ i : ι, if i < j then B j i else 0) := rfl
      _ = (∑ j : ι, ∑ i : ι, if i < j then B i j else 0) := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          rw [hB]
  have hDiag : Diag = ∑ i : ι, B i i := by
    dsimp only [Diag]
    apply Finset.sum_congr rfl; intro i _
    simp [Finset.sum_ite_eq]
  have hsplit : (∑ i : ι, ∑ j : ι, B i j) = Diag + P + R := by
    calc (∑ i : ι, ∑ j : ι, B i j)
        = ∑ i : ι, ((∑ j : ι, if i = j then B i j else 0)
            + (∑ j : ι, if i < j then B i j else 0)
            + (∑ j : ι, if j < i then B i j else 0)) := by
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _
          exact ite_lt_trichotomy i j (B i j)
      _ = Diag + P + R := by
          dsimp only [Diag, P, R]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hDiag] at hsplit
  rw [hPQ, hRQ] at hsplit
  linarith

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem coord_minor_sum_eq_trace_invariants {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    {ι : Type*} [Fintype ι] [LinearOrder ι] (v : OrthonormalBasis ι ℝ E) :
    (∑ j : ι, ∑ i : ι, if i < j then
        (⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ - ⟪T (v i), v j⟫ ^ 2) else 0) =
      ((LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)) ^ 2
        - LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E))) / 2 := by
  classical
  set A : ι → ι → ℝ := fun i j => ⟪T (v i), v j⟫ with hA
  -- Symmetry of the coordinate matrix.
  have hAsym : ∀ i j : ι, A i j = A j i := by
    intro i j
    simp only [hA]
    rw [hT.apply_clm, real_inner_comm]
  -- Split the integrand into the `AA` part and the `A²` part.
  have hsub : (∑ j : ι, ∑ i : ι, if i < j then (A i i * A j j - A i j ^ 2) else 0) =
      (∑ j : ι, ∑ i : ι, if i < j then A i i * A j j else 0)
      - (∑ j : ι, ∑ i : ι, if i < j then A i j ^ 2 else 0) := by
    simp only [ite_sub_real, Finset.sum_sub_distrib]
  -- Diagonal part.
  have hPD : (∑ j : ι, ∑ i : ι, if i < j then A i i * A j j else 0) =
      ((∑ i : ι, A i i) ^ 2 - ∑ i : ι, (A i i) ^ 2) / 2 :=
    pairSum_eq_gen (a := fun i => A i i)
  -- Off-diagonal squared part.
  have hQQ : 2 * (∑ j : ι, ∑ i : ι, if i < j then A i j ^ 2 else 0) =
      (∑ i : ι, ∑ j : ι, A i j ^ 2) - ∑ i : ι, (A i i) ^ 2 :=
    two_mul_sum_lt_sq_gen (B := fun i j => A i j ^ 2) (fun i j => by rw [hAsym i j])
  -- First trace.
  have hc1 : (∑ i : ι, A i i) = LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) := by
    rw [LinearMap.trace_eq_sum_inner (T : E →ₗ[ℝ] E) v]
    apply Finset.sum_congr rfl; intro i _
    simp only [hA]
    exact real_inner_comm _ _
  -- Second trace.
  have hc2 : (∑ i : ι, ∑ j : ι, A i j ^ 2) =
      LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) := by
    rw [← Commons.Analysis.Calculus.FDeriv.trace_adjoint_comp_eq_coord_sq_sum v,
      trace_adjoint_sq_eq_trace_sq hT]
  -- Combine.
  have hR : (∑ j : ι, ∑ i : ι, if i < j then (A i i * A j j - A i j ^ 2) else 0) =
      ((∑ i : ι, A i i) ^ 2 - ∑ i : ι, ∑ j : ι, A i j ^ 2) / 2 := by
    rw [hsub, hPD]
    have hQ : (∑ j : ι, ∑ i : ι, if i < j then A i j ^ 2 else 0) =
        ((∑ i : ι, ∑ j : ι, A i j ^ 2) - ∑ i : ι, (A i i) ^ 2) / 2 := by
      linarith [hQQ]
    rw [hQ]
    ring
  rw [hR, hc1, hc2]

end Commons.Analysis.Sigma2
