import Mathlib
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4a.affine_comb_graph_mem

namespace Work.WilkG4c

/-- **The graph of a difference is `Ω`-definable.**

If the graphs of `f` and `h` are `Ω`-definable with formats `F₁`, `F₂` and degrees `D₁`, `D₂`,
then the graph of `f - h` is `Ω`-definable.

Proof: `f - h = 0 + 1 * f + (-1) * h` is an affine combination of `f` and `h`, so this is the
affine-combination lemma `Work.WilG4a.affine_comb_graph_mem` (applied at the common format
`max F₁ F₂` and the common degree `max D₁ D₂`, which the two hypothesis `Ω`-memberships are
promoted to by monotonicity). -/
theorem GraphOfSubMem (S : WilkiesDesign.SOMin) {n F₁ D₁ F₂ D₂ : ℕ}
    {f h : (Fin n → ℝ) → ℝ}
    (hf : WilkiesDesign.graphOf f ∈ S.Ω F₁ D₁ (n + 1))
    (hh : WilkiesDesign.graphOf h ∈ S.Ω F₂ D₂ (n + 1)) :
    ∃ F D : ℕ, WilkiesDesign.graphOf (fun z : Fin n → ℝ => f z - h z) ∈ S.Ω F D (n + 1) := by
  obtain ⟨a, b, hb⟩ := Work.WilG4a.affine_comb_graph_mem S n (max F₁ F₂)
  refine ⟨a, MvPolynomial.eval ![(max D₁ D₂), (1 : ℕ)] b, ?_⟩
  have hf' : WilkiesDesign.graphOf f ∈ S.Ω (max F₁ F₂) (max D₁ D₂) (n + 1) :=
    Work.WilG5.mem_mono hf (max F₁ F₂) (max D₁ D₂) (le_max_left _ _) (le_max_left _ _)
  have hh' : WilkiesDesign.graphOf h ∈ S.Ω (max F₁ F₂) (max D₁ D₂) (n + 1) :=
    Work.WilG5.mem_mono hh (max F₁ F₂) (max D₁ D₂) (le_max_right _ _) (le_max_right _ _)
  have hres := hb (max D₁ D₂) 1 (lo := f) (hi := h) hf' hh' (0 : ℝ) 1 (-1)
  have hfun : (fun z : Fin n → ℝ => (0 : ℝ) + 1 * f z + (-1) * h z) =
      (fun z : Fin n → ℝ => f z - h z) := by
    funext z; ring
  rw [hfun] at hres
  exact hres

end Work.WilkG4c
