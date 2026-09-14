import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Geometry.Convex

open Finset

/-- John's frame bound: for a tight frame of unit vectors with positive weights
that is balanced (`∑ cᵢ uᵢ = 0`), the "polytope" `{x | ⟨uᵢ,x⟩ ≤ 1}` is contained
in the ball of radius `dim V`. -/
theorem john_frame {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] (u : ι → V) (c : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hframe : ∀ z : V, ∑ i, c i * inner ℝ (u i) z ^ 2 = ‖z‖ ^ 2)
    (hbal : ∑ i, c i • u i = 0) :
    ∀ x : V, (∀ i, inner ℝ (u i) x ≤ 1) → ‖x‖ ≤ (Module.finrank ℝ V : ℝ) := by
  -- Polarisation of the frame identity: the associated bilinear form is the inner product.
  have hbilin : ∀ z w : V, ∑ i, c i * inner ℝ (u i) z * inner ℝ (u i) w = inner ℝ z w := by
    intro z w
    have hexp : ∑ i, c i * inner ℝ (u i) (z + w) ^ 2
        = ∑ i, c i * inner ℝ (u i) z ^ 2
          + 2 * (∑ i, c i * inner ℝ (u i) z * inner ℝ (u i) w)
          + ∑ i, c i * inner ℝ (u i) w ^ 2 := by
      have hterm : ∀ i, c i * inner ℝ (u i) (z + w) ^ 2
          = c i * inner ℝ (u i) z ^ 2 + 2 * (c i * inner ℝ (u i) z * inner ℝ (u i) w)
            + c i * inner ℝ (u i) w ^ 2 := by
        intro i
        rw [inner_add_right]
        ring
      rw [sum_congr rfl (fun i _ => hterm i)]
      rw [sum_add_distrib, sum_add_distrib]
      rw [← mul_sum]
    have h1 := hframe (z + w)
    have hz := hframe z
    have hw := hframe w
    rw [hexp, hz, hw, norm_add_sq_real] at h1
    linarith
  -- Reconstruction identity `x = ∑ cᵢ ⟨uᵢ,x⟩ uᵢ` (i.e. the frame is a tight frame).
  have hrecon : ∀ z : V, ∑ i, (c i * inner ℝ (u i) z) • u i = z := by
    intro z
    apply ext_inner_right ℝ
    intro w
    rw [sum_inner]
    have hterm : ∀ i, inner ℝ ((c i * inner ℝ (u i) z) • u i) w
        = c i * inner ℝ (u i) z * inner ℝ (u i) w := by
      intro i
      rw [inner_smul_left]
      simp
    rw [sum_congr rfl (fun i _ => hterm i), hbilin z w]
  -- The total weight equals the dimension (trace of the frame identity).
  have hsumc : ∑ i, c i = (Module.finrank ℝ V : ℝ) := by
    let b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V
    have hparse : ∀ z : V, ‖z‖ ^ 2 = ∑ j, inner ℝ (b j) z ^ 2 := by
      intro z
      have h := OrthonormalBasis.sum_inner_mul_inner b z z
      rw [real_inner_self_eq_norm_sq] at h
      rw [← h]
      apply sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) z]
      ring
    calc ∑ i, c i = ∑ i, c i * ‖u i‖ ^ 2 := by
          apply sum_congr rfl; intro i _; rw [hu i]; ring
      _ = ∑ i, c i * (∑ j, inner ℝ (b j) (u i) ^ 2) := by
          apply sum_congr rfl; intro i _; rw [hparse (u i)]
      _ = ∑ i, ∑ j, c i * inner ℝ (b j) (u i) ^ 2 := by
          apply sum_congr rfl; intro i _; rw [mul_sum]
      _ = ∑ j, ∑ i, c i * inner ℝ (b j) (u i) ^ 2 := by rw [sum_comm]
      _ = ∑ j, ‖b j‖ ^ 2 := by
          apply sum_congr rfl; intro j _
          rw [show ∑ i, c i * inner ℝ (b j) (u i) ^ 2
                = ∑ i, c i * inner ℝ (u i) (b j) ^ 2 from by
                apply sum_congr rfl; intro i _; rw [← real_inner_comm (b j) (u i)]]
          exact hframe (b j)
      _ = ∑ j, (1 : ℝ) := by
          apply sum_congr rfl; intro j _; rw [OrthonormalBasis.norm_eq_one b j]; norm_num
      _ = (Module.finrank ℝ V : ℝ) := by simp
  intro x hx
  -- `x - 0 = ∑ cᵢ(⟨uᵢ,x⟩ - 1) uᵢ`, and all coefficients `cᵢ(⟨uᵢ,x⟩-1)` are `≤ 0`.
  have hx2 : x = ∑ i, (c i * (inner ℝ (u i) x - 1)) • u i := by
    have h1 : (∑ i, (c i * inner ℝ (u i) x) • u i) - (∑ i, c i • u i)
        = ∑ i, (c i * (inner ℝ (u i) x - 1)) • u i := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl; intro i _
      rw [mul_sub, sub_smul]
      simp
    rw [hrecon x, hbal, sub_zero] at h1
    exact h1
  have habs : ∀ i, |c i * (inner ℝ (u i) x - 1)| = c i * (1 - inner ℝ (u i) x) := by
    intro i
    have hle : inner ℝ (u i) x - 1 ≤ 0 := by linarith [hx i]
    have hneg : c i * (inner ℝ (u i) x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc i).le hle
    rw [abs_of_nonpos hneg]; ring
  have hsa : ∑ i, c i * inner ℝ (u i) x = 0 := by
    have hterm : ∀ i, c i * inner ℝ (u i) x = inner ℝ (c i • u i) x := by
      intro i; rw [inner_smul_left]; simp
    rw [sum_congr rfl (fun i _ => hterm i), ← sum_inner, hbal, inner_zero_left]
  rw [hx2]
  calc ‖∑ i, (c i * (inner ℝ (u i) x - 1)) • u i‖
      ≤ ∑ i, ‖(c i * (inner ℝ (u i) x - 1)) • u i‖ := norm_sum_le _ _
    _ = ∑ i, c i * (1 - inner ℝ (u i) x) := by
        apply sum_congr rfl; intro i _
        rw [norm_smul, Real.norm_eq_abs, hu i, mul_one, habs i]
    _ = (∑ i, c i) - ∑ i, c i * inner ℝ (u i) x := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl; intro i _; ring
    _ = (Module.finrank ℝ V : ℝ) := by
        rw [hsa, hsumc, sub_zero]

end Commons.Geometry.Convex