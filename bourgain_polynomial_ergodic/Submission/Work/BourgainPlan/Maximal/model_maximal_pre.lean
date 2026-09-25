import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_maximal_of_circle
import Submission.Commons.Analysis.ExponentialSums.pure_power_kernel_maximal_l2

/-!
# The `ℓ²` maximal inequality for the general-polynomial major-arc model

The model maximal inequality (Bourgain (1989), §6, (6.19)–(6.30)) is assembled here from
`poly_block_maximal_of_circle` (the per-dyadic-block estimate) by the block decomposition
`poly_model_maximal_of_block` of `poly_block_defs`.

The hypothesis `CircleNeighborhoodMaximal` (Bourgain's Lemma 4.1, the multi-frequency `log²`
maximal lemma) is discharged unconditionally by
`circleNeighborhoodMaximal_of_multiplierMaximal`, exactly as in
`Commons.Analysis.ExponentialSums.pow_model_maximal`.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-- The circle-form neighbourhood maximal (Bourgain's Lemma 4.1) unconditionally. -/
theorem circleNeighborhoodMaximal_univ : CircleNeighborhoodMaximal :=
  circleNeighborhoodMaximal_of_multiplierMaximal
    (LThOp.realLineMultiplierMaximal_of_sepWinTarget
      (Commons.Analysis.Fourier.SepWin.target_of_components
        (Commons.Analysis.Fourier.SepWin.smoothWindowMaximal_of_inline (by
          obtain ⟨C, hCpos, hC⟩ := FWPortBump.smooth_window_of_fixed_bump
            FWS.LastMile.bump_smoothOp_maximal_l2
          refine ⟨C, hCpos, fun K lam hlam φ hφ h1 h0 hbd f hf => ?_⟩
          have := hC K lam hlam φ hφ h1 h0 hbd f hf
          simpa only [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm] using this))))

/-- **The `ℓ²` maximal inequality for the general-polynomial major-arc model.**  For an integer
polynomial `P` of degree `d ≥ 2` with `c = P.leadingCoeff > 0` there is `A > 0` with

`∫⁻_{x∈ℤ} (sup_k |∫_0^1 conj(M_{2^k}(θ))·P_g(θ)·e(-2πi x θ) dθ|)² dcount ≤ A² ∫⁻ ‖g‖² dcount`

for every finitely supported `g : ℤ → ℂ`, where `M_N = polyMajorArcModelPre P (1/4) N` is the
major-arc model and `P_g(θ) = ∑_j g_j e(jθ)`.

This is Bourgain (1989), §6, (6.19)–(6.30): the model maximal function.  Template: mirror
`Commons.Analysis.ExponentialSums.pow_model_maximal` (and `pow_block_maximal_of_circle`), which
prove the same statement for `P = X^d` using the general multi-frequency lemma
`CircleNeighborhoodMaximal` (`Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2`,
Bourgain's Lemma 4.1, whose statement involves only an abstract set of frequencies and an `L²`
function, so it applies verbatim here) plus `weighted_core_maximal`.  General-polynomial
ingredients: the weight cap `‖W_{q·c}(a+lq)‖ ≤ C 2^{-mσ}` on the dyadic block `2^m ≤ q < 2^{m+1}`
(from `Commons.Analysis.ExponentialSums.integer_poly_complete_sum_bound`), the separation of the
`c`-scaled arcs (blockwise: distinct frequencies are `≥ 2^{-2(m+1)}/c` apart), the profile
replacement error (`polyProfile P N β` vs the sharp window `1_{|cβ| ≤ N^{-d}}`, whose `ℓ¹`-in-scale
sum reduces to the pure-power profile `powProfile` via `poly_major_arc_approx_coeff`), and the
frequency count `log|T| ≤ C(m+2)`. -/
theorem model_maximal_pre (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖Work.BourgainPlan.Maximal.polyTkMax P g s k x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  have hσ : 0 < polySig P := by rw [polySig, powSig]; positivity
  obtain ⟨C, hCpos, hblk⟩ := poly_block_maximal_of_circle circleNeighborhoodMaximal_univ P hc hd
  obtain ⟨A, hApos, hAb⟩ := poly_model_maximal_of_block P (polySig P) hσ ⟨C, hCpos, hblk⟩
  exact ⟨A, hApos, hAb⟩

end Work.BourgainPlan.Maximal
