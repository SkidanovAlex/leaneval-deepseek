import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped BigOperators

/-- Each coordinate of a vector in `Fin n → ℝ` is bounded by its (sup) norm. -/
lemma sq_le_norm_sq_pi {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
  calc (v i) ^ 2 = ‖v i‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2

/-- The (sup) norm of a vector in `Fin n → ℝ` is bounded by the Euclidean norm. -/
lemma norm_sq_le_sum_sq_pi {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, (v i) ^ 2 := by
  have hS : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ i, (v i) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    calc |v i| = Real.sqrt ((v i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, (v j) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖v‖ ^ 2 = ‖v‖ * ‖v‖ := by ring
    _ ≤ Real.sqrt (∑ i, (v i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) :=
        mul_le_mul h h (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = (∑ i, (v i) ^ 2) := by rw [← sq, Real.sq_sqrt hS]

/-- The Euclidean norm of a vector in `Fin n → ℝ` is bounded by `√n` times its (sup) norm. -/
lemma sum_sq_le_card_mul_norm_sq_pi {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, (v i) ^ 2 ≤ n * ‖v‖ ^ 2 := by
  have h : ∀ i : Fin n, (v i) ^ 2 ≤ ‖v‖ ^ 2 := fun i => sq_le_norm_sq_pi v i
  calc ∑ i : Fin n, (v i) ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = n * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Coefficients of a basis are comparable to the vector norm.**
For a basis `bb` of a finite-dimensional real normed space there are positive constants `K1`, `K2`
with `∑ᵢ (vᵢ)² ≤ K1 * ‖∑ᵢ vᵢ • bbᵢ‖²` and `‖∑ᵢ vᵢ • bbᵢ‖² ≤ K2 * ∑ᵢ (vᵢ)²` for every family of
coefficients `v`. -/
lemma basis_coeff_norm_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (bb : Module.Basis (Fin n) ℝ E) :
    ∃ K1 K2 : ℝ, 0 < K1 ∧ 0 < K2 ∧ ∀ v : Fin n → ℝ,
      ∑ i, (v i) ^ 2 ≤ K1 * ‖∑ i, v i • bb i‖ ^ 2 ∧
      ‖∑ i, v i • bb i‖ ^ 2 ≤ K2 * ∑ i, (v i) ^ 2 := by
  classical
  set h : E ≃L[ℝ] (Fin n → ℝ) := bb.equivFun.toContinuousLinearEquiv with hh
  have hcoe : ∀ v : Fin n → ℝ, (h.symm : (Fin n → ℝ) → E) v = ∑ i, v i • bb i := by
    intro v
    have hfun : (h.symm : (Fin n → ℝ) → E) = (bb.equivFun.symm : (Fin n → ℝ) → E) := rfl
    rw [hfun]
    exact bb.equivFun_symm_apply v
  refine ⟨(n : ℝ) * ‖(h : E →L[ℝ] (Fin n → ℝ))‖ ^ 2 + 1, ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 + 1, by positivity, by positivity, fun v => ?_⟩
  rw [← hcoe v]
  constructor
  · have h1 : ‖v‖ ≤ ‖(h : E →L[ℝ] (Fin n → ℝ))‖ * ‖h.symm v‖ := by
      have hle := ContinuousLinearMap.le_opNorm (h : E →L[ℝ] (Fin n → ℝ)) (h.symm v)
      have hsym : (h : E →L[ℝ] (Fin n → ℝ)) (h.symm v) = v := by
        show h (h.symm v) = v
        rw [ContinuousLinearEquiv.apply_symm_apply]
      rwa [hsym] at hle
    have hS := sum_sq_le_card_mul_norm_sq_pi v
    have h2 : ‖v‖ ^ 2 ≤ ‖(h : E →L[ℝ] (Fin n → ℝ))‖ ^ 2 * ‖h.symm v‖ ^ 2 := by
      have hh1 := mul_self_le_mul_self (norm_nonneg v) h1
      calc ‖v‖ ^ 2 = ‖v‖ * ‖v‖ := by ring
        _ ≤ (‖(h : E →L[ℝ] (Fin n → ℝ))‖ * ‖h.symm v‖) * (‖(h : E →L[ℝ] (Fin n → ℝ))‖ * ‖h.symm v‖) := hh1
        _ = ‖(h : E →L[ℝ] (Fin n → ℝ))‖ ^ 2 * ‖h.symm v‖ ^ 2 := by ring
    have h3 : (n : ℝ) * ‖v‖ ^ 2 ≤ (n : ℝ) * (‖(h : E →L[ℝ] (Fin n → ℝ))‖ ^ 2 * ‖h.symm v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
    have h4 : (n : ℝ) * (‖(h : E →L[ℝ] (Fin n → ℝ))‖ ^ 2 * ‖h.symm v‖ ^ 2) ≤
        ((n : ℝ) * ‖(h : E →L[ℝ] (Fin n → ℝ))‖ ^ 2 + 1) * ‖h.symm v‖ ^ 2 := by
      nlinarith [sq_nonneg ‖h.symm v‖, sq_nonneg ‖(h : E →L[ℝ] (Fin n → ℝ))‖, norm_nonneg (h.symm v)]
    linarith [hS, h3, h4]
  · have h1 : ‖h.symm v‖ ≤ ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ * ‖v‖ := ContinuousLinearMap.le_opNorm ((h.symm : (Fin n → ℝ) →L[ℝ] E)) v
    have hS := norm_sq_le_sum_sq_pi v
    have h2 : ‖h.symm v‖ ^ 2 ≤ ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 * ‖v‖ ^ 2 := by
      have hh1 := mul_self_le_mul_self (norm_nonneg _) h1
      calc ‖h.symm v‖ ^ 2 = ‖h.symm v‖ * ‖h.symm v‖ := by ring
        _ ≤ (‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ * ‖v‖) * (‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ * ‖v‖) := hh1
        _ = ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 * ‖v‖ ^ 2 := by ring
    have h3 : ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 * ‖v‖ ^ 2 ≤ ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 * (∑ i, (v i) ^ 2) :=
      mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    have h4 : ‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 * (∑ i, (v i) ^ 2) ≤ (‖((h.symm : (Fin n → ℝ) →L[ℝ] E))‖ ^ 2 + 1) * ∑ i, (v i) ^ 2 := by
      nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (v i))]
    linarith [h2, h3, h4]

end Work.Diff.EXT
