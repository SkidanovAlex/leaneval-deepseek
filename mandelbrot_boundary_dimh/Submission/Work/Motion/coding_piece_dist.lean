import Mathlib
import Submission.Work.Motion.Coding
import Submission.Work.Motion.Basic

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary

/-- The coding point of a code lies in its level-`k` piece, which has diameter `2 s θ^(k-1)`;
hence it is within `2 s θ^(k-1)` of the `p`-value of the level-`k` composite. -/
theorem coding_piece_dist {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (D : PertData c₀ N τ n p r K) (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) {k : ℕ}
    (hk : 1 ≤ k) :
    ‖D.coding c ω - pComp (D.τc c) ω k p‖ ≤ 2 * D.s * D.θ ^ (k - 1) := by
  obtain ⟨x, hx, hxeq⟩ := PertData.coding_mem_piece D c hc ω k
  rw [← hxeq]
  have h := PertData.pComp_dist_le D c hc ω (k - 1) x hx p (PertData.half_mem D p)
  have hk' : k - 1 + 1 = k := by omega
  rwa [hk'] at h

end Work.Motion

