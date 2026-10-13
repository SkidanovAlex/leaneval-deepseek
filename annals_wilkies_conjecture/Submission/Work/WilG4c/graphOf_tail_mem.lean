import Mathlib
import Submission.Work.WilG4a.subst_mem

/-!
# Shifting a definable graph by a fresh leading coordinate

Let `g : ℝ^q → ℝ` have `Ω`-definable graph `graphOf g ⊆ ℝ^{q+1}` with format `A` and
degree `D`.  Then the graph of the function `μ ↦ g (Fin.tail μ)` on `ℝ^{q+1}` is again
`Ω`-definable, of dimension `q+2`, degree `D + 2` and format
`A + 2 * ((q + 2) + (q + 1)) + 1`.

Geometrically this is the graph of `g` with one fresh free coordinate prepended
(`graphOf (μ ↦ g (tail μ)) = {x ∈ ℝ^{q+2} | x (last) = g (x_1, …, x_q)}`), which is the
pullback of `graphOf g` along the coordinate substitution
`σ = Fin.succ : Fin (q+1) → Fin (q+2)`.  The bookkeeping is therefore exactly the
substitution atom `Work.WilG4a.subst_mem` with source dimension `q+1` and target
dimension `q+2`:

`A + 2 * ((q + 2) + (q + 1)) + 1 = A + 2 * (N + n) + 1` for `N = q + 2`, `n = q + 1`,
and the degree grows by the usual `+2` paid for the diagonal hypersurface.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- Unfolding both `graphOf`s: prepending a free coordinate to `g` is the same thing as
pulling `graphOf g` back along the coordinate map `Fin.succ`.  The two sides differ only in
the way the last coordinate and the initial block are written:
`(Fin.last q).succ = Fin.last (q+1)` and `Fin.tail (Fin.init x) = Fin.init (x ∘ Fin.succ)`. -/
theorem graphOf_tail_eq_pullback (q : ℕ) (g : (Fin q → ℝ) → ℝ) :
    graphOf (fun μ : Fin (q + 1) → ℝ => g (Fin.tail μ)) =
      {x : Fin (q + 2) → ℝ | x ∘ (Fin.succ : Fin (q + 1) → Fin (q + 2)) ∈ graphOf g} := by
  ext x
  have hlast : (Fin.last q).succ = Fin.last (q + 1) := by ext; simp [Fin.succ]
  have hinit : Fin.tail (Fin.init x) =
      Fin.init (x ∘ (Fin.succ : Fin (q + 1) → Fin (q + 2))) := by
    funext i
    simp only [Fin.tail, Fin.init, Function.comp_apply]
    congr 1
  simp only [graphOf, Set.mem_ofPred_eq, Function.comp_apply]
  rw [← hlast, ← hinit]

/-- **Prepending a fresh leading coordinate to a definable graph.**  If `graphOf g` is
`S.Ω A D (q+1)` then the graph of `μ ↦ g (Fin.tail μ)` is
`S.Ω (A + 2 * ((q + 2) + (q + 1)) + 1) (D + 2) (q + 2)`.

This is the substitution atom `Work.WilG4a.subst_mem` applied to the coordinate map
`Fin.succ : Fin (q+1) → Fin (q+2)` (source dimension `q+1`, target dimension `q+2`),
together with the set identity `graphOf_tail_eq_pullback`. -/
theorem graphOf_tail_mem (S : WilkiesDesign.SOMin) {q A D : ℕ} {g : (Fin q → ℝ) → ℝ}
    (hg : WilkiesDesign.graphOf g ∈ S.Ω A D (q + 1)) :
    WilkiesDesign.graphOf (fun μ : Fin (q + 1) → ℝ => g (Fin.tail μ)) ∈
      S.Ω (A + 2 * ((q + 2) + (q + 1)) + 1) (D + 2) (q + 2) := by
  have h := Work.WilG4a.subst_mem S (Fin.succ : Fin (q + 1) → Fin (q + 2)) hg
  rw [graphOf_tail_eq_pullback]
  exact h

end Work.WilG4c
