import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.invCos_jet_bound
import Submission.Work.FTS.EllipticEst.remov.iteratedDeriv_mul_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- **Jets of `u / cos` on a compact subinterval of `(0, π/2)`.**

For every `N` there is a positive constant `A` (depending only on `N`) such that, for every
`u : ℝ → ℝ` of class `C^N` on `(0, π/2)`, every `θ ∈ (0, 3π/8)` and every `m ≤ N`, the square of
the `m`-th derivative of `θ ↦ u θ / cos θ` at `θ` is bounded by `A` times the sum of the squares
of the derivatives of `u` up to order `m` at `θ`.

The proof is Leibniz' formula for the `m`-th derivative of a product, combined with
Cauchy–Schwarz and the fact that on `(0, 3π/8)` (whose closure is a compact subset of
`(-π/2, π/2)`) every jet of `1 / cos` is bounded. -/
theorem invCos_jets_le (N : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ N u (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8), ∀ m : ℕ, m ≤ N →
        (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          ≤ A * ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2 := by
  classical
  -- a bound for every jet of `1 / cos` on `(0, 3π/8)`
  obtain ⟨B, hB⟩ := invCos_jet_bound
  -- the constant `A = 1 + ∑_{m ≤ N} ∑_{j ≤ m} (C(m,j) B (m-j))²`
  set T : ℝ := ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (n + 1),
      (n.choose j * B (n - j)) ^ 2 with hT
  have hTnn : 0 ≤ T := by
    simp only [hT]
    exact Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  refine ⟨1 + T, by linarith, ?_⟩
  intro u hu θ hθ m hm
  -- `θ ∈ (0, π/2)`, so `cos θ > 0`
  have hθlt : θ < Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθlt⟩
  -- differentiability of the two factors at `θ`
  have hu_at : ContDiffAt ℝ m u θ :=
    (hu.contDiffAt (isOpen_Ioo.mem_nhds ⟨hθ.1, hθlt⟩)).of_le (by exact_mod_cast hm)
  have hsec_at : ContDiffAt ℝ m (fun t : ℝ => (Real.cos t)⁻¹) θ :=
    (Real.contDiff_cos.contDiffAt).inv (ne_of_gt hcos_pos)
  have hfun : (fun t : ℝ => u t / Real.cos t) = u * (fun t : ℝ => (Real.cos t)⁻¹) := by
    funext t; simp [div_eq_mul_inv]
  -- Leibniz + Cauchy–Schwarz
  have hcs := iteratedDeriv_mul_sq_le m u (fun t : ℝ => (Real.cos t)⁻¹) θ B hu_at hsec_at
      (fun k _ => hB k θ hθ)
  -- the coefficient sum is bounded by the constant
  have hcoef : (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) ≤ 1 + T := by
    have hstep : (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) ≤ T := by
      simp only [hT]
      exact Finset.single_le_sum
        (f := fun n => ∑ j ∈ Finset.range (n + 1), (n.choose j * B (n - j)) ^ 2)
        (fun n _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    linarith
  calc (iteratedDeriv m (fun t : ℝ => u t / Real.cos t) θ) ^ 2
      = (iteratedDeriv m (u * (fun t : ℝ => (Real.cos t)⁻¹)) θ) ^ 2 := by rw [hfun]
    _ ≤ (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) *
          ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2 := hcs
    _ ≤ (1 + T) * ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun j _ => sq_nonneg _))

end Work.FTS.EllipticEst.remov
