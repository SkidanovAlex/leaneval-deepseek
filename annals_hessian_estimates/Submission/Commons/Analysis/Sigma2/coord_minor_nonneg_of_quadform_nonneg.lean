import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Sigma2

open scoped RealInnerProductSpace

/-! ## Nonnegativity of the sum of principal `2×2` coordinate minors of a positive
semi-definite self-adjoint operator

For a self-adjoint operator `N` with `⟪N v, v⟫ ≥ 0` for every `v`, the bilinear form
`(u, v) ↦ ⟪N u, v⟫` is a semi-inner product, so it satisfies the Cauchy--Schwarz
inequality `⟪N u, v⟫² ≤ ⟪N u, u⟫ · ⟪N v, v⟫`.  Consequently every summand
`⟪N(bᵢ), bᵢ⟫ · ⟪N(bⱼ), bⱼ⟫ - ⟪N(bᵢ), bⱼ⟫²` is nonnegative, and hence so is their
(triangular) sum. -/

/-- The bilinear form of a self-adjoint operator is symmetric. -/
lemma inner_selfAdjoint_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : E →L[ℝ] E) (hN : N.IsSymmetric) (u v : E) : ⟪N u, v⟫ = ⟪N v, u⟫ := by
  change ⟪(N : E →ₗ[ℝ] E) u, v⟫ = ⟪(N : E →ₗ[ℝ] E) v, u⟫
  rw [hN u v, real_inner_comm]

/-- Expansion of the quadratic form of a self-adjoint operator. -/
lemma quad_form_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : E →L[ℝ] E) (hN : N.IsSymmetric) (u v : E) (s t : ℝ) :
    ⟪N (s • u + t • v), s • u + t • v⟫
      = s ^ 2 * ⟪N u, u⟫ + 2 * s * t * ⟪N u, v⟫ + t ^ 2 * ⟪N v, v⟫ := by
  have hsym : ⟪N v, u⟫ = ⟪N u, v⟫ := inner_selfAdjoint_comm N hN v u
  simp only [map_add, ContinuousLinearMap.map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hsym]
  ring

/-- **Cauchy--Schwarz inequality** for the semi-inner product `(u, v) ↦ ⟪N u, v⟫` of a
positive semi-definite self-adjoint operator `N`. -/
lemma inner_sq_le_mul_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : E →L[ℝ] E) (hN : N.IsSymmetric) (h : ∀ v : E, 0 ≤ ⟪N v, v⟫) (u v : E) :
    ⟪N u, v⟫ ^ 2 ≤ ⟪N u, u⟫ * ⟪N v, v⟫ := by
  set a : ℝ := ⟪N u, u⟫ with haeq
  set b : ℝ := ⟪N u, v⟫ with hbeq
  set c : ℝ := ⟪N v, v⟫ with hceq
  have ha : 0 ≤ a := by rw [haeq]; exact h u
  have hc : 0 ≤ c := by rw [hceq]; exact h v
  -- The quadratic form `s² a + 2 s t b + t² c` is nonnegative for all `s, t`.
  have hP : ∀ s t : ℝ, 0 ≤ s ^ 2 * a + 2 * s * t * b + t ^ 2 * c := by
    intro s t
    have h1 := h (s • u + t • v)
    rwa [quad_form_expansion N hN u v s t] at h1
  -- Evaluating at `(c, -b)` and `(b, -a)` yields, respectively,
  -- `c · (ac - b²) ≥ 0` and `a · (ac - b²) ≥ 0`.
  have key1 : 0 ≤ c * (a * c - b ^ 2) := by
    have h1 := hP c (-b)
    nlinarith [h1]
  have key2 : 0 ≤ a * (a * c - b ^ 2) := by
    have h1 := hP b (-a)
    nlinarith [h1]
  have key : 0 ≤ (a + c) * (a * c - b ^ 2) := by nlinarith [key1, key2]
  by_cases hac : a + c = 0
  · -- Then `a = c = 0`, and the nonnegativity of `2 b` and `-2 b` forces `b = 0`.
    have ha0 : a = 0 := by nlinarith [ha, hc, hac]
    have hc0 : c = 0 := by nlinarith [ha, hc, hac]
    have hb0 : b = 0 := by
      have hp : 0 ≤ b := by have h1 := hP 1 1; rw [ha0, hc0] at h1; nlinarith [h1]
      have hn : b ≤ 0 := by have h1 := hP 1 (-1); rw [ha0, hc0] at h1; nlinarith [h1]
      linarith
    rw [ha0, hb0, hc0]; norm_num
  · have hpos : 0 < a + c := by
      rcases lt_or_eq_of_le (by linarith : (0 : ℝ) ≤ a + c) with hlt | heq
      · exact hlt
      · exact absurd heq.symm hac
    have h2 := (mul_nonneg_iff_of_pos_left hpos).mp key
    rw [haeq, hbeq, hceq] at h2
    linarith

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem coord_minor_nonneg_of_quadform_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (b : OrthonormalBasis (Fin 4) ℝ E)
    {N : E →L[ℝ] E} (hN : N.IsSymmetric) (h : ∀ v : E, 0 ≤ ⟪N v, v⟫) :
    0 ≤ ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪N (b i), b i⟫ * ⟪N (b j), b j⟫ - ⟪N (b i), b j⟫ ^ 2) else 0 := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  by_cases hij : i < j
  · rw [if_pos hij]
    exact sub_nonneg.mpr (inner_sq_le_mul_inner N hN h (b i) (b j))
  · rw [if_neg hij]

end Commons.Analysis.Sigma2