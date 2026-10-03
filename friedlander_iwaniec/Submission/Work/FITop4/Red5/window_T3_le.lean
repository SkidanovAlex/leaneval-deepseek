import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.sum_Zint_annM_prim_le
import Submission.Work.FITop4.Red5.window_sharp_count_sqfree
import Submission.Work.FITop4.Red5.window_T3_weight_sum
import Submission.Work.FITop4.Red5.window_T3_assembly

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem window_T3_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (x N Mn Pz : ℕ) (τ θ : ℝ) (K : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (Pa : Fin K → Work.FITop.Params),
      (2 ≤ x) → (1 ≤ Mn) → (1 ≤ N) → (2 ≤ Pz) → (0 < θ) → (θ ≤ 1 / 4) →
      (∀ i, (Pa i).M = (Mn : ℝ)) → (∀ i, (Pa i).N = a i) → (∀ i, (N : ℝ) ≤ a i) →
      (∀ i, (N : ℝ) ≤ (Pa i).N) →
      (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≤ 1) →
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
      (∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ)) →
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
      (∀ u, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) - 2 * θ * (N : ℝ) →
          (∑ i, p i u) = 1) →
      (1 ≤ θ * (N : ℝ) ^ ((1 : ℝ) / 2)) → ((N : ℝ) ≤ (Mn : ℝ)) →
      (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
          cGInd m N x Pz τ (Work.FIPlan.gnorm z) * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ c * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
  obtain ⟨c1, hc1pos, hsharp⟩ := window_sharp_count_sqfree
  obtain ⟨C2, hC2pos, hwei⟩ := window_T3_weight_sum
  obtain ⟨c, hcpos, hmain⟩ := window_T3_assembly c1 C2 hc1pos hC2pos hsharp hwei
  exact ⟨c, hcpos, hmain⟩

end

end Work.FITop4.Red5
