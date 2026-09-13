import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.trace_adjoint_comp_eq_coord_sq_sum
import Submission.Commons.Analysis.Sigma2.pairSum_sq
import Submission.Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues
import Submission.Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq

namespace Commons.Analysis.Sigma2

open scoped RealInnerProductSpace
open scoped BigOperators

/-! ## Elementary algebra of triangular pair sums

The two lemmas below are the combinatorial core of the identity
`σ₂(eigenvalues) = ∑_{i<j} (A_{ii}A_{jj} - A_{ij}²)` for a self-adjoint operator `T`
expressed in an arbitrary orthonormal basis.
-/

/-- Splitting a single contribution `x` according to the trichotomy of `i j`. -/
private lemma ite_lt_trichotomy_sum {n : ℕ} (i j : Fin n) (x : ℝ) :
    x = (if i = j then x else 0) + (if i < j then x else 0) + (if j < i then x else 0) := by
  rcases lt_trichotomy i j with h | h | h
  · have hji : ¬ j < i := lt_asymm h
    have hij : ¬ i = j := h.ne
    simp [h, hji, hij]
  · subst h; simp
  · have hij : ¬ i < j := lt_asymm h
    have hne : ¬ i = j := (ne_of_lt h).symm
    simp [h, hij, hne]

/-- Distributing a truncated difference over the triangular indexing. -/
private lemma ite_sub_real {p : Prop} [Decidable p] (x y : ℝ) :
    (if p then x - y else 0) = (if p then x else 0) - (if p then y else 0) := by
  by_cases h : p <;> simp [h]

/-- `(∑ a)² = ∑ a² + 2 ∑_{i<j} aᵢaⱼ`, solved for the pair sum. -/
lemma pairSum_eq {n : ℕ} (a : Fin n → ℝ) :
    (∑ j : Fin n, ∑ i : Fin n, if i < j then a i * a j else 0) =
      ((∑ i : Fin n, a i) ^ 2 - ∑ i : Fin n, (a i) ^ 2) / 2 := by
  have h := pairSum_sq (a := a)
  linarith

/-- For a symmetric two-index family `B`, the upper-triangular sum is half the total
off-diagonal mass: `2 ∑_{i<j} B_{ij} = ∑_{i,j} B_{ij} - ∑_i B_{ii}`. -/
lemma two_mul_sum_lt_sq {n : ℕ} (B : Fin n → Fin n → ℝ)
    (hB : ∀ i j, B i j = B j i) :
    2 * (∑ j : Fin n, ∑ i : Fin n, if i < j then B i j else 0)
      = (∑ i : Fin n, ∑ j : Fin n, B i j) - (∑ i : Fin n, B i i) := by
  let Q : ℝ := ∑ j : Fin n, ∑ i : Fin n, if i < j then B i j else 0
  let P : ℝ := ∑ i : Fin n, ∑ j : Fin n, if i < j then B i j else 0
  let R : ℝ := ∑ i : Fin n, ∑ j : Fin n, if j < i then B i j else 0
  let Diag : ℝ := ∑ i : Fin n, ∑ j : Fin n, if i = j then B i j else 0
  have hPQ : P = Q := by
    dsimp only [P, Q]; rw [Finset.sum_comm]
  have hRQ : R = Q := by
    dsimp only [R, Q]
    calc (∑ i : Fin n, ∑ j : Fin n, if j < i then B i j else 0)
        = (∑ j : Fin n, ∑ i : Fin n, if i < j then B j i else 0) := rfl
      _ = (∑ j : Fin n, ∑ i : Fin n, if i < j then B i j else 0) := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          rw [hB]
  have hDiag : Diag = ∑ i : Fin n, B i i := by
    dsimp only [Diag]
    apply Finset.sum_congr rfl; intro i _
    simp [Finset.sum_ite_eq]
  have hsplit : (∑ i : Fin n, ∑ j : Fin n, B i j) = Diag + P + R := by
    calc (∑ i : Fin n, ∑ j : Fin n, B i j)
        = ∑ i : Fin n, ((∑ j : Fin n, if i = j then B i j else 0)
            + (∑ j : Fin n, if i < j then B i j else 0)
            + (∑ j : Fin n, if j < i then B i j else 0)) := by
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _
          exact ite_lt_trichotomy_sum i j (B i j)
      _ = Diag + P + R := by
          dsimp only [Diag, P, R]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hDiag] at hsplit
  rw [hPQ, hRQ] at hsplit
  linarith

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem sigma2_sum_eq_coord_minor_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : T.IsSymmetric)
    (v : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) =
      ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then
          (⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ - ⟪T (v i), v j⟫ ^ 2)
        else 0 := by
  classical
  -- Both sides are `(tr T ^ 2 - tr (T ∘ T)) / 2`.
  have hL : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) =
      ((∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i) ^ 2
        - ∑ i : Fin (Module.finrank ℝ E), (hT.eigenvalues rfl i) ^ 2) / 2 :=
    pairSum_eq (a := hT.eigenvalues rfl)
  have htr1 : LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) =
      ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i :=
    trace_eq_sum_eigenvalues hT
  have htr2 : LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) =
      ∑ i : Fin (Module.finrank ℝ E), (hT.eigenvalues rfl i) ^ 2 :=
    trace_sq_eq_sum_eigenvalues_sq hT
  have hL' : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) =
      ((LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)) ^ 2
        - LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E))) / 2 := by
    rw [hL, ← htr1, ← htr2]
  -- Traces in the orthonormal basis `v`.
  have hc1 : (∑ i : Fin (Module.finrank ℝ E), ⟪T (v i), v i⟫) =
      LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) := by
    rw [LinearMap.trace_eq_sum_inner (T : E →ₗ[ℝ] E) v]
    apply Finset.sum_congr rfl; intro i _
    exact real_inner_comm _ _
  have hc2 : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (⟪T (v i), v j⟫) ^ 2) =
      LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E)) := by
    rw [← Commons.Analysis.Calculus.FDeriv.trace_adjoint_comp_eq_coord_sq_sum v,
      trace_adjoint_sq_eq_trace_sq hT]
  -- Symmetry of the coordinate matrix `⟪T vᵢ, vⱼ⟫`.
  have hAsym : ∀ i j : Fin (Module.finrank ℝ E), ⟪T (v i), v j⟫ = ⟪T (v j), v i⟫ := by
    intro i j
    rw [hT.apply_clm, real_inner_comm]
  have hPD : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then ⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ else 0) =
      ((∑ i : Fin (Module.finrank ℝ E), ⟪T (v i), v i⟫) ^ 2
        - ∑ i : Fin (Module.finrank ℝ E), (⟪T (v i), v i⟫) ^ 2) / 2 :=
    pairSum_eq (a := fun i => ⟪T (v i), v i⟫)
  have hQQ : 2 * (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then (⟪T (v i), v j⟫) ^ 2 else 0) =
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (⟪T (v i), v j⟫) ^ 2)
        - ∑ i : Fin (Module.finrank ℝ E), (⟪T (v i), v i⟫) ^ 2 :=
    two_mul_sum_lt_sq (B := fun i j => (⟪T (v i), v j⟫) ^ 2) (fun i j => by rw [hAsym])
  have hsub : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then
          (⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ - ⟪T (v i), v j⟫ ^ 2)
        else 0) =
      (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then ⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ else 0)
      - (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then (⟪T (v i), v j⟫) ^ 2 else 0) := by
    simp only [ite_sub_real, Finset.sum_sub_distrib]
  have hR : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then
          (⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ - ⟪T (v i), v j⟫ ^ 2)
        else 0) =
      ((∑ i : Fin (Module.finrank ℝ E), ⟪T (v i), v i⟫) ^ 2
        - ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (⟪T (v i), v j⟫) ^ 2) / 2 := by
    rw [hsub, hPD]
    have hQ : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then (⟪T (v i), v j⟫) ^ 2 else 0) =
      ((∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (⟪T (v i), v j⟫) ^ 2)
        - ∑ i : Fin (Module.finrank ℝ E), (⟪T (v i), v i⟫) ^ 2) / 2 := by
      linarith [hQQ]
    rw [hQ]
    ring
  have hR' : (∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        if i < j then
          (⟪T (v i), v i⟫ * ⟪T (v j), v j⟫ - ⟪T (v i), v j⟫ ^ 2)
        else 0) =
      ((LinearMap.trace ℝ E (T : E →ₗ[ℝ] E)) ^ 2
        - LinearMap.trace ℝ E ((T : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E))) / 2 := by
    rw [hR, ← hc1, ← hc2]
  rw [hL', hR']

end Commons.Analysis.Sigma2
