import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.R4_polarize
import Submission.Work.Diff.Alg.PA.R4_bianchi
import Submission.Work.Diff.Alg.PA.Glue
import Submission.Work.Diff.Alg.PA.CS_bounds
import Submission.Work.Diff.Alg.PA.compact_scal
import Submission.Work.Diff.Alg.PA.compact_frob
import Submission.Work.Diff.Alg.PA.QPairBound
import Submission.Work.Diff.Alg.PA.pinch_basic
import Submission.Work.Diff.Alg.PA.scal_basis
import Submission.Work.Diff.Alg.PA.scal_sq_le_ricSq
import Submission.Work.Diff.GE.curv4_trace
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.PP.Q_Iso
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE (pure algebra on Curv4 n).
(1) Pinching-set consequences. IsPinchedAlg δ R with δ < 1 forces all sectional curvatures to be ≥ 0 (take the same plane twice).
   Nonnegative sectional curvature gives |R| ≤ c_n·scal: components are bounded by max K via polarization, and
   scal ≥ 2 max K. δ-pinched with δ near 1 gives |R − K̄·Iso| ≤ c_n(1−δ)|R|, and |R°| ≤ |R − λIso| for every λ.
   The non-pinched part of F is bounded, so it only contributes the constants.
(2) qPair − (4S/(n(n−1)))ricSq = ⟪R°, Q(R)⟫ with R° = R − (S/(n(n−1)))Iso.
   Use ⟪Iso, Q R⟫ = 2 scalAlg(Q R) = 4 ricSq R and ⟪R, Iso⟫ = 2S.
   Write Q(A+B) = Q(A) + Q(B) + 2𝔅(A,B) with 𝔅 the symmetric bilinear form. Then ⟪R°, Q(λIso)⟫ = 2(n−1)λ²⟪R°,Iso⟫ = 0, so
   ⟪R°,Q(R)⟫ = ⟪R°,Q(R°)⟫ + 2λ⟪R°,𝔅(Iso,R°)⟫ ≤ c|R°|²(|R°| + |λ|) ≤ c|R°|²|R|.
(3) Cauchy–Schwarz on the trace: S² ≤ n·ricSq. And frobSqTF R = |R − λIso|² ≥ 0 (|Iso|² = 2n(n−1)).
-/

namespace Work.Diff.Alg

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.Alg.PA

theorem pinching_algebra (n : ℕ) (hn : 3 ≤ n) : PinchingAlgebra n := by
  have hn2 : 2 ≤ n := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- ============ conjunct 1 ============
    intro F hF
    obtain ⟨hInv, hBdd⟩ := hF
    have halgF : ∀ R ∈ F, IsAlgCurv R := hInv.2.2.1
    obtain ⟨c₀, hc₀pos, hc₀⟩ := Work.Diff.Alg.PA.compact_scal n hn2
    refine ⟨?_, ?_⟩
    · -- the linear bound
      obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Curv4 n)).mp
        (hBdd (1 / 2) (by norm_num))
      refine ⟨max 1 c₀⁻¹,
        (n : ℝ) ^ 2 * max r 0 + max 1 c₀⁻¹ * ((n : ℝ) ^ 2 * max r 0) + 1, ?_, ?_⟩
      · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      · intro R hRF
        by_cases hpin : IsPinchedAlg (1 / 2) R
        · have hA : IsAlgCurv R := halgF R hRF
          have hsc : 0 ≤ scalAlg R :=
            (Work.Diff.Alg.PA.scal_basis n).2 R hA
              ((Work.Diff.Alg.PA.pinch_basic n).1 (1 / 2) R hpin (by norm_num))
          have h1 : c₀ * Real.sqrt (frobSq R) ≤ scalAlg R := hc₀ R hA hpin
          have hc₀ne : c₀ ≠ 0 := ne_of_gt hc₀pos
          have h2 : Real.sqrt (frobSq R) ≤ c₀⁻¹ * scalAlg R := by
            have h3 : c₀⁻¹ * (c₀ * Real.sqrt (frobSq R)) ≤ c₀⁻¹ * scalAlg R :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            rwa [← mul_assoc, inv_mul_cancel₀ hc₀ne, one_mul] at h3
          have h4 : c₀⁻¹ * scalAlg R ≤ max 1 c₀⁻¹ * scalAlg R :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hsc
          have h5 : 0 ≤ (n : ℝ) ^ 2 * max r 0 + max 1 c₀⁻¹ * ((n : ℝ) ^ 2 * max r 0) + 1 := by
            positivity
          linarith
        · have hRnorm : ‖R‖ ≤ max r 0 := by
            have h1 : ‖R‖ ≤ r := by
              have h2 : R ∈ Metric.closedBall (0 : Curv4 n) r := hr ⟨hRF, hpin⟩
              simpa [Metric.mem_closedBall, dist_eq_norm] using h2
            exact le_trans h1 (le_max_left _ _)
          have h1 : Real.sqrt (frobSq R) ≤ (n : ℝ) ^ 2 * max r 0 := by
            have h2 := Work.Diff.Alg.PA.sqrt_frobSq_le_norm R
            have h3 : (n : ℝ) ^ 2 * ‖R‖ ≤ (n : ℝ) ^ 2 * max r 0 :=
              mul_le_mul_of_nonneg_left hRnorm (by positivity)
            linarith
          have h2 : |scalAlg R| ≤ (n : ℝ) ^ 2 * max r 0 := by
            have h3 := Work.Diff.L.abs_scalAlg_le R
            have h4 : (n : ℝ) ^ 2 * ‖R‖ ≤ (n : ℝ) ^ 2 * max r 0 :=
              mul_le_mul_of_nonneg_left hRnorm (by positivity)
            linarith
          have h3 : -((n : ℝ) ^ 2 * max r 0) ≤ scalAlg R := neg_le_of_abs_le h2
          have h4 : (0 : ℝ) ≤ max 1 c₀⁻¹ := le_trans zero_le_one (le_max_left _ _)
          have h5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * max r 0 := by positivity
          nlinarith [h1, h3, h4, h5]
    · -- the trace-free bound
      intro δ hδ
      obtain ⟨δ₀, hδ₀lt, hδ₀⟩ := Work.Diff.Alg.PA.compact_frob n hn2 δ hδ
      obtain ⟨r₂, hr₂⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Curv4 n)).mp
        (hBdd δ₀ hδ₀lt)
      refine ⟨(n : ℝ) ^ 2 * max r₂ 0 * (1 + Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1)))) + 1, ?_⟩
      intro R hRF
      by_cases hpin : IsPinchedAlg δ₀ R
      · have h1 := hδ₀ R (halgF R hRF) hpin
        have h2 : 0 ≤ (n : ℝ) ^ 2 * max r₂ 0
            * (1 + Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1)))) + 1 := by positivity
        have h3 : 0 ≤ Real.sqrt (frobSq R) := Real.sqrt_nonneg _
        nlinarith
      · have hRnorm : ‖R‖ ≤ max r₂ 0 := by
          have h1 : ‖R‖ ≤ r₂ := by
            have h2 : R ∈ Metric.closedBall (0 : Curv4 n) r₂ := hr₂ ⟨hRF, hpin⟩
            simpa [Metric.mem_closedBall, dist_eq_norm] using h2
          exact le_trans h1 (le_max_left _ _)
        have h1 := Work.Diff.Alg.PA.sqrt_frobSqTF_le n hn2 R
        have h2 : Real.sqrt (frobSq R) ≤ (n : ℝ) ^ 2 * max r₂ 0 := by
          have h3 := Work.Diff.Alg.PA.sqrt_frobSq_le_norm R
          have h4 : (n : ℝ) ^ 2 * ‖R‖ ≤ (n : ℝ) ^ 2 * max r₂ 0 :=
            mul_le_mul_of_nonneg_left hRnorm (by positivity)
          linarith
        have h3 : Real.sqrt (2 * scalAlg R ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)))
            ≤ (n : ℝ) ^ 2 * max r₂ 0
              * Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
          have h4 := Work.Diff.Alg.PA.sqrt_scal_sq_div_le n hn2 R
          have h5 : (n : ℝ) ^ 2 * ‖R‖ ≤ (n : ℝ) ^ 2 * max r₂ 0 :=
            mul_le_mul_of_nonneg_left hRnorm (by positivity)
          have h6 : 0 ≤ Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) := Real.sqrt_nonneg _
          nlinarith [h4, h5, h6]
        have h7 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * max r₂ 0 := by positivity
        have h8 : 0 ≤ Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1))) := Real.sqrt_nonneg _
        have h9 : (n : ℝ) ^ 2 * max r₂ 0 + (n : ℝ) ^ 2 * max r₂ 0
              * Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1)))
            ≤ (n : ℝ) ^ 2 * max r₂ 0 * (1 + Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1)))) + 1 := by
          nlinarith [h7, h8]
        have h10 : 0 ≤ δ * Real.sqrt (frobSq R) := mul_nonneg (le_of_lt hδ) (Real.sqrt_nonneg _)
        linarith
  · -- ============ conjunct 2 ============
    obtain ⟨c, hc, hQb, hQbb⟩ := (Work.Diff.Alg.PA.CS_bounds n).1
    have htp : ∀ A B : Curv4 n, |tpair n A B| ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B) :=
      (Work.Diff.Alg.PA.CS_bounds n).2
    exact ⟨c * (1 + 2 * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1))) + 1,
      fun R hR => Work.Diff.Alg.PA.qPair_bound n hn2 c hc hQb hQbb htp R hR⟩
  · -- ============ conjunct 3 ============
    intro R hR
    exact ⟨Work.Diff.Alg.PA.scal_sq_le_ricSq n R hR, (Work.Diff.GE.curv4_trace R hR).2.2⟩

end Work.Diff.Alg
