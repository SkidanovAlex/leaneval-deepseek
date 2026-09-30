import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.arc_count_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem adjQ_sum_lower {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (hc : 0 < c) (hP₁ : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L) (hP₂ : 2 ≤ P₂)
    (hEdges : c * Work.BMF.pi0 P₁ ^ 2 * (X / L) ≤ (D.edges.card : ℝ)) :
    c ^ 2 * Work.BMF.pi0 P₂ * Work.BMF.pi0 P₁ ^ 2 * (X / L) ≤
      ∑ q ∈ Work.BMF.primesIn (P₂ / 2) P₂, ∑ i : Work.BMF.GVert D, ∑ j : Work.BMF.GVert D,
        (if Work.BMF.GAdjQ D q i j then (1 : ℝ) else 0) := by
  classical
  -- `c · π₀(P₂) ≥ 0`, so we may multiply the edge bound `hEdges` by it.
  have hAc : 0 ≤ c * pi0 P₂ := by
    have hlog : 0 ≤ Real.log P₂ := Real.log_nonneg (by linarith)
    have hpi : 0 ≤ pi0 P₂ := by rw [pi0]; exact div_nonneg (by linarith) hlog
    exact mul_nonneg hc.le hpi
  have hP₂pos : 0 < P₂ := by linarith
  -- `edges.card` gives `c π₀(P₂)` primes each, double counted over `q` (`edgeS_sum_le`);
  -- each `q` supports at least as many ordered adjacent pairs as it has witness edges
  -- (`arc_count_ge`).
  calc c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)
      = (c * pi0 P₂) * (c * pi0 P₁ ^ 2 * (X / L)) := by ring
    _ ≤ (c * pi0 P₂) * (D.edges.card : ℝ) := mul_le_mul_of_nonneg_left hEdges hAc
    _ ≤ ∑ q ∈ primesIn (P₂ / 2) P₂,
          ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) := edgeS_sum_le D hP₂pos
    _ ≤ ∑ q ∈ primesIn (P₂ / 2) P₂, ∑ i : GVert D, ∑ j : GVert D,
          (if GAdjQ D q i j then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun q _ => arc_count_ge D q hP₁ hL hbig)

end Work.BMF
