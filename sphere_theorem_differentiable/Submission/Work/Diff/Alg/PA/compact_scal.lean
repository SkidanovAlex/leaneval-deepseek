import Mathlib
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.R4_polarize
import Submission.Work.Diff.Alg.PA.R4_bianchi
import Submission.Work.Diff.Alg.Pinch.eq_zero_of_secK_eq_zero
import Submission.Work.Diff.Alg.q2p_secK_Iso
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.L.pinchingSet_component_bound_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|R|` is controlled by the scalar curvature for `δ`-pinched algebraic curvature tensors

For `δ < 1` the pinching condition `IsPinchedAlg δ R` applied to the *same* plane twice gives
`δ · secK R u v ≤ secK R u v`, hence `0 ≤ secK R u v`: every sectional curvature of a pinched
tensor is nonnegative, so `scalAlg R = ∑ᵢⱼ Rᵢⱼᵢⱼ ≥ 0`.

The quantitative statement needed here is that the *whole* tensor is controlled by `scalAlg`:

  `∃ c > 0, c * √(|R|²) ≤ scalAlg R`

for every `IsAlgCurv R` with `IsPinchedAlg (1/2) R`.  It follows from the componentwise bound
`|Rᵢⱼₖₗ| ≤ K · scalAlg R` (`Work.Diff.L.pinched_component_le`, proved by the classical
polarization argument: the polarization identity expresses every component of an algebraic
curvature tensor through its sectional curvatures, and pinching bounds those by
`scalAlg R / (δ n (n-1))`).  Squaring and summing,

  `|R|² = ∑ᵢⱼₖₗ Rᵢⱼₖₗ² ≤ n⁴ (K scalAlg R)²`,

so `√(|R|²) ≤ n² K scalAlg R`, and `c = 1/(n² K) = (n-1)/(16 n)` works.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

theorem compact_scal (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : Curv4 n, IsAlgCurv R → IsPinchedAlg (1 / 2) R →
      c * Real.sqrt (frobSq R) ≤ scalAlg R := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine ⟨((n : ℝ) - 1) / (16 * (n : ℝ)), by positivity, ?_⟩
  intro R hAlg hpin
  -- the componentwise bound of a `1/2`-pinched algebraic curvature tensor
  obtain ⟨hscal, hcomp⟩ :=
    Work.Diff.L.pinched_component_le hn hAlg (δ := 1 / 2) (by norm_num) (by norm_num) hpin
  set K : ℝ := 8 / ((1 / 2) * ((n : ℝ) * ((n : ℝ) - 1))) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hcompK : ∀ i j k l : Fin n, |R i j k l| ≤ K * scalAlg R := by
    intro i j k l
    rw [hK]
    exact hcomp i j k l
  -- square and sum the componentwise bound
  have hfrob : frobSq R ≤ ((n : ℝ) ^ 2 * (K * scalAlg R)) ^ 2 := by
    have hstep : ∀ i j k l : Fin n, R i j k l ^ 2 ≤ (K * scalAlg R) ^ 2 := by
      intro i j k l
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcompK i j k l) 2
    calc frobSq R = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2 := rfl
      _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, (K * scalAlg R) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine Finset.sum_le_sum fun j _ => ?_
          refine Finset.sum_le_sum fun k _ => ?_
          exact Finset.sum_le_sum fun l _ => hstep i j k l
      _ = ((n : ℝ) ^ 2 * (K * scalAlg R)) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hs : Real.sqrt (frobSq R) ≤ (n : ℝ) ^ 2 * (K * scalAlg R) := by
    have h1 : Real.sqrt (frobSq R) ≤ Real.sqrt (((n : ℝ) ^ 2 * (K * scalAlg R)) ^ 2) :=
      Real.sqrt_le_sqrt hfrob
    rwa [Real.sqrt_sq (mul_nonneg (sq_nonneg _) (mul_nonneg hKnn hscal))] at h1
  have hc0 : 0 ≤ ((n : ℝ) - 1) / (16 * (n : ℝ)) := by positivity
  calc ((n : ℝ) - 1) / (16 * (n : ℝ)) * Real.sqrt (frobSq R)
      ≤ ((n : ℝ) - 1) / (16 * (n : ℝ)) * ((n : ℝ) ^ 2 * (K * scalAlg R)) :=
        mul_le_mul_of_nonneg_left hs hc0
    _ = scalAlg R := by
        rw [hK]
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
        have hnm1ne : (n : ℝ) - 1 ≠ 0 := ne_of_gt hnm1
        field_simp
        ring

end Work.Diff.Alg.PA
