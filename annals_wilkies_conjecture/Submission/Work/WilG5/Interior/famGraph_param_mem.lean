import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Reindex3

/-!
  WilG5 — `Interior.famGraph_param_mem`.

  A function `g : ℝⁿ → ℝ` whose graph is `Ω`-definable is also `Ω`-definable as a *family*
  over one (ignored) parameter: the family graph `famGraph (fun l u => g u) ⊆ ℝ^{1+n+1}` is
  the preimage of `graphOf g` under the coordinate shift `Fin.natAdd 1`, so the general
  coordinate-preimage lemma `Work.WilG5.coordPre_mem` applies, at the cost of additive
  constants in format and degree only.

  This is the bridge that turns a `graphOf`-membership into the hypothesis shape consumed by
  the family lemma `WilkiesDesign.CG.FLem S 1 n` (whose families live on
  `Fin (1 + n + 1)`), as needed by `Work.WilG5.Interior.cell_charts`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Work.WilG5.Interior

open WilkiesDesign WilkiesConjecture

/-- The graph of `g : ℝⁿ → ℝ`, viewed as a family that ignores its one-dimensional parameter
block, is the coordinate preimage of `graphOf g` along `Fin.natAdd 1`.

Concretely: reading a point `x : Fin (1 + n + 1) → ℝ` as `(l, u, y)` with `l = x 0`,
`u = (x 1, …, x n)` and `y = x (1 + n)`, the family graph requires `y = g u`, while the
preimage of `graphOf g` requires the same equation on the shifted tuple
`x ∘ Fin.natAdd 1 = (x 1, …, x n, x (1 + n))`. -/
theorem famGraph_const_eq (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    WilkiesDesign.CG.famGraph (fun (_ : Fin 1 → ℝ) (u : Fin n → ℝ) => g u) =
      coordPre (Fin.natAdd 1 : Fin (n + 1) → Fin (1 + n + 1)) (graphOf g) := by
  ext x
  simp only [WilkiesDesign.CG.famGraph, graphOf, coordPre, Fin.init]
  constructor <;> intro h <;> exact h

theorem famGraph_param_mem (S : WilkiesDesign.SOMin) (n : ℕ) (g : (Fin n → ℝ) → ℝ)
    {F D : ℕ} (h : WilkiesDesign.graphOf g ∈ S.Ω F D (n + 1)) :
    ∃ A L : ℕ, WilkiesDesign.CG.famGraph (fun (l : Fin 1 → ℝ) (u : Fin n → ℝ) => g u) ∈
      S.Ω (A + F) (D + L) (1 + n + 1) := by
  refine ⟨64 * ((1 + n + 1) + (n + 1)) + 64, 32 * ((1 + n + 1) + (n + 1)) + 32, ?_⟩
  rw [famGraph_const_eq n g]
  have hcp := Work.WilG5.coordPre_mem (S := S) (m := n + 1) (N := 1 + n + 1)
    (ι := (Fin.natAdd 1 : Fin (n + 1) → Fin (1 + n + 1))) h
  have h1 : (64 * ((1 + n + 1) + (n + 1)) + 64) + F =
      F + 64 * ((1 + n + 1) + (n + 1)) + 64 := by omega
  have h2 : D + (32 * ((1 + n + 1) + (n + 1)) + 32) =
      D + 32 * ((1 + n + 1) + (n + 1)) + 32 := by omega
  rw [h1, h2]
  exact hcp

end Work.WilG5.Interior
