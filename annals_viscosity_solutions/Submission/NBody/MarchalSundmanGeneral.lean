import Submission.NBody.MarchalClusterAsymptotic

/-!
# Sundman's asymptotic law from the abstract hypotheses

The asymptotic law `f(t) = κ t^{4/3} + o(t^{4/3})` of a colliding cluster
(`MarchalClusterAsymptotic.clusterInertia_asymptotic`) is proved from four inputs about the function
`f = I_k ∘ x`:

* differentiability of `f` and of `f'` on `(0, ε)`, positivity of `f` there, `f → 0` at `0⁺`;
* the Ostrogradsky inequality `f'² ≤ 4 f f'' + 16 C f`;
* the lower bound `f'' f^{1/2} ≥ d`.

The present module isolates that computation, so that it can be applied not only to a single
cluster but also, in the multi-cluster analysis, to the sum `∑_l I_{C_l}` of the moments of inertia
of all the simultaneously colliding clusters.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Sundman's asymptotic law, from the abstract hypotheses.** -/
theorem rpow_asymptotic_of_hineq_hbound {f : ℝ → ℝ} {C d ε : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hd : 0 < d)
    (hf1 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt f (deriv f t) t)
    (hf2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) ε, 0 < f t)
    (hineq : ∀ t ∈ Ioo (0:ℝ) ε,
      (deriv f t) ^ (2:ℕ) ≤ 4 * f t * deriv (deriv f) t + 16 * C * f t)
    (hbound : ∀ t ∈ Ioo (0:ℝ) ε, d / 2 ≤ deriv (deriv f) t * (f t) ^ ((1:ℝ)/2))
    (hlim : Tendsto f (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun t : ℝ => f t / t ^ ((4:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ) := by
  have hmono : ∀ t ∈ Ioo (0:ℝ) ε, 0 ≤ deriv f t :=
    deriv_nonneg_of_second_deriv_mul_sqrt_ge (d := d / 2) hε (by linarith) hf1 hf2 hfpos
      hbound hlim
  obtain ⟨η, hηpos, hη⟩ := Commons.Analysis.Calculus.sundman_asymptotic_ratio (f := f)
    (b := 4) (c := 16 * C) (d := d / 2) hε (by norm_num) (by linarith) hf1 hf2 hfpos
    hineq hmono hlim (fun t ht => by
      rw [show ((4:ℝ) - 2)/4 = (1:ℝ)/2 by norm_num]
      exact hbound t ht)
  have hfint : ∀ a u : ℝ, 0 < a → a ≤ u → u < ε →
      IntervalIntegrable (deriv f) MeasureTheory.volume a u := by
    intro a u ha hau hu
    refine ContinuousOn.intervalIntegrable fun s hs => ?_
    rw [uIcc_of_le hau] at hs
    exact ((hf2 s ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hu⟩).differentiableAt).continuousAt.continuousWithinAt
  have hfinal := Commons.Analysis.Calculus.rpow_asymptotic_of_deriv_sq_div_asymptotic
    (f := f) (b := 4) (η := η) hε (by norm_num) hηpos hf1 hfint hfpos hmono hlim hη
  refine ⟨((3:ℝ)/4 * Real.sqrt η) ^ ((4:ℝ)/3), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  have hb11 : (4:ℝ) / (4 - 1) = 4 / 3 := by norm_num
  have hb12 : (4 - 1) / 4 = (3:ℝ) / 4 := by norm_num
  rw [hb11, hb12] at hfinal
  exact hfinal

end Submission.NBody
