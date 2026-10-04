import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Q2PM.onpair_compact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict pinching: `min K > c` when `K > c` on every orthonormal pair

The strictness step of `Work.Diff.Alg.quarter_to_pic2` (Brendle–Schoen, Cor. 22 / Step 4 of the
route): if every sectional curvature of an algebraic curvature tensor lies strictly above `c`,
then the *infimum* over the orthonormal pairs is itself strictly above `c`. This is a compactness
statement: the set of orthonormal pairs is compact (`Work.Diff.Alg.Q2PM.onpair_compact`) and
`(u,v) ↦ secK R u v` is a continuous (in fact polynomial) function, so its minimum is attained.

The degenerate cases `n ≤ 1` are handled by the empty-set branch: in dimension `≤ 1` two unit
vectors cannot be orthogonal, so there is no orthonormal pair and any `a > c` satisfies the
(empty) lower bound.
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg

/-! ## Reusable pieces of the compactness/strictness argument -/

namespace MinSec

/-- `(u,v) ↦ secK R u v` is continuous (it is the quartic polynomial `∑ Rᵢⱼₖₗ uᵢ vⱼ uₖ vₗ`). -/
theorem continuous_secK_pair {n : ℕ} (R : Curv4 n) :
    Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => secK R p.1 p.2 := by
  simp only [secK, R4]
  fun_prop

/-- A continuous function attains its minimum on the (nonempty) set of orthonormal pairs.
The compactness of that set is `Work.Diff.Alg.Q2PM.onpair_compact`. -/
theorem exists_isONPair_min {n : ℕ} (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hf : Continuous f)
    (hne : ∃ u v : Fin n → ℝ, IsONPair u v) :
    ∃ u v : Fin n → ℝ, IsONPair u v ∧
      ∀ u' v' : Fin n → ℝ, IsONPair u' v' → f (u, v) ≤ f (u', v') := by
  obtain ⟨u₀, v₀, h₀⟩ := hne
  obtain ⟨p, hpS, hpmin⟩ :=
    (Work.Diff.Alg.Q2PM.onpair_compact n).exists_isMinOn ⟨(u₀, v₀), h₀⟩ hf.continuousOn
  exact ⟨p.1, p.2, hpS, fun u' v' h' => hpmin h'⟩

end MinSec

theorem q2p_minsec {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (c : ℝ)
    (h : ∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v → c < Submission.Diff.Alg.secK R u v) :
    ∃ a : ℝ, c < a ∧ ∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v →
      a ≤ Submission.Diff.Alg.secK R u v := by
  by_cases hne : ∃ u v : Fin n → ℝ, IsONPair u v
  · -- The sectional curvature attains its minimum `a = min K` on the compact set of ON pairs.
    obtain ⟨u₀, v₀, h₀⟩ := hne
    obtain ⟨u, v, huv, hmin⟩ :=
      MinSec.exists_isONPair_min (fun p : (Fin n → ℝ) × (Fin n → ℝ) => secK R p.1 p.2)
        (MinSec.continuous_secK_pair R) ⟨u₀, v₀, h₀⟩
    exact ⟨secK R u v, h u v huv, fun u' v' h' => hmin u' v' h'⟩
  · -- No orthonormal pair: the second requirement is vacuous.
    simp only [not_exists] at hne
    exact ⟨c + 1, by linarith, fun u v huv => absurd huv (hne u v)⟩

end Work.Diff.Alg
