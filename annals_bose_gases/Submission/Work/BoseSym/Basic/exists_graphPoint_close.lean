import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Basic.graphPoint_add
import Submission.Work.BoseSym.Basic.graphPoint_smul
import Submission.Work.BoseSym.Basic.graphPoint_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Density of the graph of the gradient in the energy space

`Hsub N L` is by definition the closure, in the ambient space
`Amb N = L²(Conf N) × ∏_j L²(Conf N)`, of the linear span of the range of the
graph point map `F ↦ (F, ∇F)` on the test functions `F : testSub N L`.

Using the linearity of `graphPoint` (`graphPoint_add`, `graphPoint_smul`,
`graphPoint_zero`, proved in the sibling modules), the span of its range is
*equal* to its range, so `Hsub N L` is exactly the closure of the range
(`Hsub_eq_closure`).  Hence every `p : Hsub N L` is approximated, in the
ambient norm, by graph points of test functions.

The last ingredient (`hSq_le_norm_sq`) is that the graph-norm-squared
`hSq q = ‖q.1‖² + ∑_j ‖q.2 j‖²` is controlled by the ambient norm:
`hSq q ≤ (1 + #(GIdx N)) · ‖q‖²` (the ambient norm on the product is the
maximum of the two norms, so both the function part and each gradient
component are bounded by `‖q‖`).

Putting these together gives the theorem: for every `ε > 0` there is a test
function `F` with `hSq (graphPoint N L F - p) ≤ ε`.  This is the statement
that the test functions are dense in the energy space.
-/

namespace Work.BoseSym.Basic

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real

/-- The range of the graph point map, as a submodule of the ambient space.
This is used only to identify the linear span of the range with the range. -/
noncomputable def graphRange (N : ℕ) (L : ℝ) : Submodule ℝ (Amb N) where
  carrier := Set.range (graphPoint N L)
  add_mem' := by
    rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨F + G, graphPoint_add F G⟩
  zero_mem' := ⟨0, graphPoint_zero⟩
  smul_mem' := by
    rintro c _ ⟨F, rfl⟩
    exact ⟨c • F, graphPoint_smul c F⟩

/-- The energy space is the closure of the range of the graph point map: the
linear span of a linear image of a submodule is the image itself. -/
lemma Hsub_eq_closure (N : ℕ) (L : ℝ) :
    ((Hsub N L : Submodule ℝ (Amb N)) : Set (Amb N)) =
      closure (Set.range (graphPoint N L)) := by
  have hcoe : ((graphRange N L : Submodule ℝ (Amb N)) : Set (Amb N)) =
      Set.range (graphPoint N L) := rfl
  rw [Hsub, Submodule.topologicalClosure_coe, ← hcoe, Submodule.span_eq]

/-- The squared graph norm is bounded by the ambient norm squared: every
component is a contraction of the ambient product norm. -/
lemma hSq_le_norm_sq (N : ℕ) (q : Amb N) :
    hSq q ≤ (1 + (Fintype.card (GIdx N) : ℝ)) * ‖q‖ ^ 2 := by
  have h1 : ‖q.1‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    have := norm_fst_le q
    nlinarith [norm_nonneg q.1, norm_nonneg q]
  have h2 : gSq q ≤ (Fintype.card (GIdx N) : ℝ) * ‖q‖ ^ 2 := by
    simp only [gSq]
    calc ∑ j : GIdx N, ‖q.2 j‖ ^ 2
        ≤ ∑ _j : GIdx N, ‖q‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := norm_le_pi_norm q.2 j
          have h' := norm_snd_le q
          nlinarith [norm_nonneg (q.2 j), norm_nonneg q]
        _ = (Fintype.card (GIdx N) : ℝ) * ‖q‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [hSq, l2Sq]
  nlinarith [h1, h2]

/-- The graph points of test functions are dense in the energy space, in the
graph norm `hSq`: for every `p : Hsub N L` and every `ε > 0` there is a test
function `F` with `hSq (graphPoint N L F - p) ≤ ε`. -/
theorem exists_graphPoint_close {N : ℕ} {L : ℝ} (p : Hsub N L) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : testSub N L, hSq (graphPoint N L F - (p : Amb N)) ≤ ε := by
  have hc0 : (0 : ℝ) ≤ (Fintype.card (GIdx N) : ℝ) := by positivity
  have h1c : 0 < 1 + (Fintype.card (GIdx N) : ℝ) := by linarith
  have hp : (p : Amb N) ∈ closure (Set.range (graphPoint N L)) := by
    rw [← Hsub_eq_closure N L]
    exact p.2
  obtain ⟨y, hy, hdist⟩ :=
    Metric.mem_closure_iff.1 hp (Real.sqrt (ε / (1 + (Fintype.card (GIdx N) : ℝ))))
      (Real.sqrt_pos.2 (div_pos hε h1c))
  obtain ⟨F, rfl⟩ := hy
  refine ⟨F, le_of_lt ?_⟩
  have hδ2 : (Real.sqrt (ε / (1 + (Fintype.card (GIdx N) : ℝ)))) ^ 2
      = ε / (1 + (Fintype.card (GIdx N) : ℝ)) :=
    Real.sq_sqrt (le_of_lt (div_pos hε h1c))
  have hnorm : ‖(p : Amb N) - graphPoint N L F‖
      < Real.sqrt (ε / (1 + (Fintype.card (GIdx N) : ℝ))) := by
    rw [← dist_eq_norm]
    exact hdist
  have hsq : ‖graphPoint N L F - (p : Amb N)‖ ^ 2
      < (Real.sqrt (ε / (1 + (Fintype.card (GIdx N) : ℝ)))) ^ 2 := by
    rw [norm_sub_rev]
    exact pow_lt_pow_left₀ hnorm (norm_nonneg _) (by norm_num)
  calc hSq (graphPoint N L F - (p : Amb N))
      ≤ (1 + (Fintype.card (GIdx N) : ℝ)) * ‖graphPoint N L F - (p : Amb N)‖ ^ 2 :=
        hSq_le_norm_sq N _
    _ < (1 + (Fintype.card (GIdx N) : ℝ))
          * (Real.sqrt (ε / (1 + (Fintype.card (GIdx N) : ℝ)))) ^ 2 :=
        mul_lt_mul_of_pos_left hsq h1c
    _ = (1 + (Fintype.card (GIdx N) : ℝ))
          * (ε / (1 + (Fintype.card (GIdx N) : ℝ))) := by rw [hδ2]
    _ = ε := by field_simp

end Work.BoseSym.Basic
