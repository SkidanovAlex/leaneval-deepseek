import Mathlib
import Submission.Work.LT.op_linear
import Submission.Work.LT.sum_quad_expand

namespace Work.LT

/-- Contraction for a self-adjoint, positive, mean-zero-preserving operator whose quadratic form is bounded by `θ` **on mean-zero functions only** (the needed form when the operator fixes constants): on mean-zero functions the `ℓ²` norm contracts by `θ²`. -/
theorem op_contract_meanzero {X : Type*} [Fintype X] (T : (X → ℝ) → (X → ℝ)) (θ : ℝ) (hθ : 0 ≤ θ)
    (hsym : ∀ u v : X → ℝ, (∑ x, T u x * v x) = ∑ x, T v x * u x)
    (hpos : ∀ u : X → ℝ, 0 ≤ ∑ x, T u x * u x)
    (hup : ∀ u : X → ℝ, (∑ x, u x = 0) → (∑ x, T u x * u x) ≤ θ * ∑ x, u x ^ 2)
    (hmean : ∀ u : X → ℝ, (∑ x, u x = 0) → ∑ x, T u x = 0)
    (u : X → ℝ) (hu : ∑ x, u x = 0) :
    ∑ x, T u x ^ 2 ≤ θ ^ 2 * ∑ x, u x ^ 2 := by
  classical
  -- Symmetry of the quadratic form forces `T` to be linear (`Work.LT.op_linear`).
  obtain ⟨T_add, T_smul⟩ := op_linear T hsym
  -- `T` maps mean-zero functions to mean-zero functions, so it applies to `T u` too.
  have hwu : ∑ x, T u x = 0 := hmean u hu
  have hpow : (∑ x, T u x * T u x) = (∑ x, T u x ^ 2) := by
    apply Finset.sum_congr rfl; intro x _; ring
  have hsym2 : (∑ x, T (T u) x * u x) = (∑ x, T u x ^ 2) := by
    rw [hsym (T u) u]
    apply Finset.sum_congr rfl; intro x _; ring
  -- Quadratic-form identity for the (mean-zero) test function `c • u - T u`.
  have hexp : ∀ c : ℝ,
      (∑ x, T (c • u - T u) x * (c • u - T u) x)
      = c ^ 2 * (∑ x, T u x * u x) - 2 * c * (∑ x, T u x ^ 2)
          + (∑ x, T (T u) x * T u x) := by
    intro c
    have hT : T (c • u - T u) = c • T u - T (T u) := by
      have h1 : c • u - T u = c • u + (-1 : ℝ) • T u := by
        rw [sub_eq_add_neg]; simp
      rw [h1, T_add, T_smul, T_smul]
      simp only [neg_one_smul, sub_eq_add_neg]
    rw [hT]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_quad_expand]
    rw [hpow, hsym2]
    ring
  rcases lt_or_eq_of_le hθ with hθpos | hθ0
  · -- Case `θ > 0`: test against `θ • u - T u`.
    have hP1 : (∑ x, T u x * u x) ≤ θ * (∑ x, u x ^ 2) := hup u hu
    have hP4 : (∑ x, T (T u) x * T u x) ≤ θ * (∑ x, T u x ^ 2) := hup (T u) hwu
    have hge := hpos (θ • u - T u)
    rw [hexp θ] at hge
    have hkey : θ * (∑ x, T u x ^ 2) ≤ θ ^ 3 * (∑ x, u x ^ 2) := by
      nlinarith [hge, hP1, hP4, sq_nonneg θ]
    have h6 : θ * (∑ x, T u x ^ 2) ≤ θ * (θ ^ 2 * (∑ x, u x ^ 2)) := by
      have h : θ ^ 3 * (∑ x, u x ^ 2) = θ * (θ ^ 2 * (∑ x, u x ^ 2)) := by ring
      linarith
    exact le_of_mul_le_mul_left h6 hθpos
  · -- Case `θ = 0`: test against `u - T u`; the quadratic form vanishes identically.
    have hθ0' : θ = 0 := hθ0.symm
    have hP1 : (∑ x, T u x * u x) = 0 := by
      have h := hup u hu
      rw [hθ0', zero_mul] at h
      exact le_antisymm h (hpos u)
    have hP4 : (∑ x, T (T u) x * T u x) = 0 := by
      have h := hup (T u) hwu
      rw [hθ0', zero_mul] at h
      exact le_antisymm h (hpos (T u))
    have hge := hpos ((1:ℝ) • u - T u)
    rw [hexp 1] at hge
    have ha : (∑ x, T u x ^ 2) ≤ 0 := by nlinarith [hge, hP1, hP4]
    calc ∑ x, T u x ^ 2 ≤ 0 := ha
      _ = θ ^ 2 * ∑ x, u x ^ 2 := by rw [hθ0']; ring

end Work.LT
