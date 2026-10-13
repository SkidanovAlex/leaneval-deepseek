import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

theorem sup_mixed_diff {k : ℕ} {δ : ℝ} {V : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hle : k ≤ 6)
    (hsmV : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (V s))
    (hsmW : Work.FTS.EllipticEst.SmoothOpen W)
    (hsupV : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (V s) q.1 q.2| ≤ C)
    (hsupW : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i W q.1 q.2| ≤ C) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (fun z θ => V s z θ - W z θ) q.1 q.2| ≤ C := by
  intro K hKc hKQ
  obtain ⟨CV, hCV0, hCV⟩ := hsupV K hKc hKQ
  obtain ⟨CW, hCW0, hCW⟩ := hsupW K hKc hKQ
  refine ⟨CV + CW, add_nonneg hCV0 hCW0, ?_⟩
  intro s hs q hqK j i hji
  have hqQ : q ∈ Work.FTS.EllipticEst.Q0 := hKQ hqK
  rw [Work.FTS.EllipticEst.mem_Q0] at hqQ
  obtain ⟨hz, hθ0, hθπ⟩ := hqQ
  have hji6 : j + i ≤ 6 := le_trans hji hle
  rw [Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six hji6 hz ⟨hθ0, hθπ⟩
      (Work.FTS.EllipticEst.SmoothOpen.forall (hsmV s hs) 6)
      (Work.FTS.EllipticEst.SmoothOpen.forall hsmW 6)]
  have htri : |Work.Spaces.mixed j i (V s) q.1 q.2 - Work.Spaces.mixed j i W q.1 q.2|
      ≤ |Work.Spaces.mixed j i (V s) q.1 q.2| + |Work.Spaces.mixed j i W q.1 q.2| := by
    simpa [sub_eq_add_neg] using abs_add_le (Work.Spaces.mixed j i (V s) q.1 q.2)
      (-(Work.Spaces.mixed j i W q.1 q.2))
  exact le_trans htri (add_le_add (hCV s hs q hqK j i hji) (hCW q hqK j i hji))

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
