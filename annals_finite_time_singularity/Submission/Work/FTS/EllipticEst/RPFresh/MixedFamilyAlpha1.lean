import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.mixedFamily_le
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mixed-derivative family, uniform for `0 < α ≤ 1`

The sibling `Work.EllipticEst.Core.mixedFamily_le` proves the mixed-derivative family
estimate of the interpolation for `0 < α ≤ 1/4`.  Its whole proof, however, only ever uses
`α ≤ 1` (the `α² ≤ 1` that caps the prefactor, and the hypothesis `hα1 : α ≤ 1` of the
per-slot estimate `mixedIntS_integral_le`).  The present file re-runs that assembly with the
exact hypothesis `α ≤ 1` requested by the consumer, so that the estimate holds uniformly on
the full range `(0,1]` of the singular exponent.

Nothing new is proved: the mathematical content is `mixedIntS_integral_le` (the slot
estimate, whose only `α`-hypothesis is `α ≤ 1`), and the rest is the arithmetic of the
assembly.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-- **The mixed-derivative family of the interpolation estimate, for `0 < α ≤ 1`.**

There is a universal constant `C > 0` such that for every `0 < α ≤ 1`, every `V` smooth on
the open quadrant with vanishing angular boundary values and `V ∈ ℋ^k` in the three relevant
norms,

`α² ∑_{1 ≤ i, i+j ≤ k} ∫_z w² ∫_θ (D_z^{j+1}D_θ^i∂_θV)² sin(2θ)^{-γ}
   ≤ C (α⁴ HkSq(D_z²V) + HkSq(∂_θ²V) + α² HkSq(D_zV))`.

Each summand is estimated by the whole `ℋ^k`-integrand of `∂_θ²V`, so the right-hand side is
dominated by its second term; the finitely many slots and `α² ≤ 1` produce the stated
constant.  This is `Work.EllipticEst.Core.mixedFamily_le` with the range of `α` widened from
`(0,1/4]` to `(0,1]`. -/
theorem MixedFamilyAlpha1 (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
          else 0)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound k
  have hKnn : 0 ≤ K := hKpos.le
  refine ⟨1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k, ?_, ?_⟩
  · positivity
  · intro α V hα hα1 hV _ _ _ hPth2 _
    have hV' : ContDiffOn ℝ ∞ (Function.uncurry V) Work.EllipticEst.Core.sliceU := hV
    set B : ℝ := Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) with hB
    have hBnn : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkSq_nonneg _ _ _
    -- the per-slot estimate
    have hslot : ∀ i j, i ∈ Finset.range (k + 1) → j ∈ Finset.range (k + 1) →
        (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0)
          ≤ K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B := by
      intro i j hi hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        refine le_trans (Work.EllipticEst.Core.mixedIntS_integral_le hKnn hK hα hα1 hV' hPth2
          hc.1 hc.2) ?_
        have hi1 : (i : ℝ) ≤ (k : ℝ) + 1 := by
          exact_mod_cast (by omega : i ≤ k + 1)
        have hi2 : (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by
          exact_mod_cast (by omega : i + 1 ≤ k + 1)
        have hp : (4 : ℝ) ^ (i - 1) ≤ (4 : ℝ) ^ k :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hfirst : (i : ℝ) * 4 ^ (i - 1) * K ^ 2 ≤ ((k : ℝ) + 1) * (4 : ℝ) ^ k * K ^ 2 :=
          mul_le_mul (mul_le_mul hi1 hp (by positivity) (by positivity)) le_rfl
            (sq_nonneg K) (by positivity)
        have hle : (i : ℝ) * 4 ^ (i - 1) * K ^ 2 * ((i : ℝ) + 1)
            ≤ K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 := by
          calc (i : ℝ) * 4 ^ (i - 1) * K ^ 2 * ((i : ℝ) + 1)
              ≤ (((k : ℝ) + 1) * (4 : ℝ) ^ k * K ^ 2) * ((k : ℝ) + 1) :=
                mul_le_mul hfirst hi2 (by positivity) (by positivity)
            _ = K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 := by ring
        exact mul_le_mul_of_nonneg_right hle hBnn
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hBnn
    -- the full sum
    have hsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0))
        ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0))
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
              (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hslot i j hi hj
        _ = (((k : ℝ) + 1) * ((k : ℝ) + 1))
              * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hα2le : α ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α - 1)]
    have hcnn : 0 ≤ 1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k := by positivity
    calc α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0))
        ≤ α ^ 2 * ((((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B)) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg α)
      _ ≤ 1 * ((((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B)) :=
          mul_le_mul_of_nonneg_right hα2le (by positivity)
      _ = ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k * B := by ring
      _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B := by
          have h1 : ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k
              ≤ 1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k := by linarith
          calc ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k * B
              = (((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B := by ring
            _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B :=
                mul_le_mul_of_nonneg_right h1 hBnn
      _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k)
            * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
              + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
              + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcnn
          rw [hB]
          have hA : 0 ≤ α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
            mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
          have hD : 0 ≤ α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
            mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
          linarith

end Work.FTS.EllipticEst.RPFresh
