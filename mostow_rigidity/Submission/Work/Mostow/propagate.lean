import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.oneSidedLipschitz

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- `hdist` vanishes on the diagonal (from the explicit `arcosh` model). -/
theorem hdist_self_aux {n : ℕ} (u : E n) : hdist u u = 0 := by
  rw [hdist, real_inner_self_eq_norm_sq, ← sq, tpart_sq]
  norm_num

/-- The hyperbolic distance between the endpoints of a continuously parametrised arc
`γ : ℝ → ℍⁿ` is at most the length of the parameter interval, provided the arc grows at
unit speed in a one-sided (right) sense on `[a, b)`.

The proof reduces the assertion to the one-dimensional one-sided Gronwall estimate
`oneSidedLipschitz` applied to the continuous function `t ↦ hdist (γ a) (γ t)`: the local
hypothesis for that function follows from `hloc` and the triangle inequality `htri`, and
its value at `a` is `0`. -/
theorem propagate {n : ℕ} (a b : ℝ) (hab : a ≤ b) (γ : ℝ → E n)
    (hcont : ContinuousOn (fun t => hdist (γ a) (γ t)) (Set.Icc a b))
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z)
    (hloc : ∀ t ∈ Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Set.Ioo 0 δ,
      hdist (γ t) (γ (t + h)) ≤ h * (1 + ε)) :
    hdist (γ a) (γ b) ≤ b - a := by
  -- The local one-sided estimate transfers from `γ` to the distance-to-`γ a` function.
  have hfloc : ∀ t ∈ Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Set.Ioo 0 δ,
      hdist (γ a) (γ (t + h)) ≤ hdist (γ a) (γ t) + h * (1 + ε) := by
    intro t ht ε hε
    obtain ⟨δ, hδ, H⟩ := hloc t ht ε hε
    exact ⟨δ, hδ, fun h hh => by
      have h1 := H h hh
      have h2 := htri (γ a) (γ t) (γ (t + h))
      linarith⟩
  have hmain := oneSidedLipschitz hab hcont hfloc
  have hzero : hdist (γ a) (γ a) = 0 := hdist_self_aux (γ a)
  linarith

end Work.Mostow
