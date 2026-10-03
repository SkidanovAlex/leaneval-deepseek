import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Basic
import Submission.Work.Repel.Spec
import Submission.Work.Repel.returns_to_ifs

/-!
# REPEL / §6, the final glue

From the `ReturnData` of the §6 return and the logarithmic estimate `dim_arith`, produce the
`HypIFS` of `RepelStatement` and the dimension inequality.  Small context on purpose: this file
is one of the staged lemmas replacing the single 1000-line assembly.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- **Glue.**  `RD : ReturnData (fam α) p r Kc` gives, via `returns_to_ifs`, a conformal IFS with
`RD.N ≥ 2` and `K' = max Kc 2 > 1`, hence `HypIFS (cOfAlpha α) RD.N K'`; the dimension bound
`2 - ε ≤ log RD.N / log K'` is the caller's `dim_arith` estimate. -/
theorem r3_glue (α : ℂ) (ε γ C : ℝ) (hε : 0 < ε)
    (Γ : ℝ)
    (hΓ : ∀ η N K : ℝ, Γ ≤ η →
      γ * η * (Real.exp (2 * Real.pi * η)) ^ 2 ≤ N →
      K ≤ C * η ^ 2 * Real.exp (2 * Real.pi * η) → 1 < K →
      2 - ε ≤ Real.log N / Real.log K)
    (η : ℝ) (hηΓ : Γ ≤ η)
    {p : ℂ} {r Kc : ℝ} (RD : ReturnData (fam α) p r Kc) (hr : 0 < r)
    (hN : γ * η * (Real.exp (2 * Real.pi * η)) ^ 2 ≤ (RD.N : ℝ))
    (hK : max Kc 2 ≤ C * η ^ 2 * Real.exp (2 * Real.pi * η)) :
    ∃ N : ℕ, ∃ K' : ℝ, 2 ≤ N ∧ 1 < K' ∧ 2 - ε ≤ Real.log N / Real.log K' ∧
      HypIFS (cOfAlpha α) N K' := by
  refine ⟨RD.N, max Kc 2, RD.hN, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · exact hΓ η _ _ hηΓ hN hK (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  · obtain ⟨τ, hifs, hdyn⟩ :=
      returns_to_ifs (f := fam α) (K := Kc) (K' := max Kc 2) hr (le_max_left _ _)
        (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) RD
    exact hypIFS_of_fam α RD.N (max Kc 2)
      ⟨τ, RD.n, p, r, hifs, fun i => ⟨RD.hn i, hdyn i⟩⟩

end

end Work.Repel
