import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilkG4c.GraphOfSubMem
import Submission.Work.WilkG4c.FamGraphConstPtMem

/-!
## `Work.WilCrux.Clean.SheetHatGraphMem`

*Shearing a family by its value on the zero fibre is `Ω`-definable.*

Let `G : ℝ^a × ℝ^b → ℝ` be a family with:

* `famGraph G` (the graph of `z ↦ G (z ∘ castAdd b) (z ∘ natAdd a)`, living in `ℝ^{a+b+1}`)
  in `S.Ω F D (a+b+1)`;
* the graph of the "zero-fibre" function `w ↦ G w 0` (living in `ℝ^{a+1}`) in
  `S.Ω F₁ D₁ (a+1)`.

Then the graph of the sheared (or "hatted") family `(w, z) ↦ G w z - G w 0` is again in `S.Ω`,
at the price of constants in format and degree only.

### Proof

Write `n := a + b` and let
`P u = G (u ∘ Fin.castAdd b) (u ∘ Fin.natAdd a)`, `Q u = G (u ∘ Fin.castAdd b) 0`
for `u : ℝ^{a+b}`.  Then `famGraph G = graphOf P` (definitionally) and
`famGraph (fun w z => G w z - G w 0) = graphOf (P - Q)`, so it suffices to show that
`graphOf Q` is an `Ω`-set in `ℝ^{a+b+1}`; the difference is then handled by
`Work.WilkG4c.GraphOfSubMem`.

For `graphOf Q`: putting `pt w = G w 0`, we have `Q u = pt (u ∘ Fin.castAdd b)`, i.e. `Q` is
`pt` composed with the projection `ℝ^{a+b} → ℝ^a` onto the *parameter* block.  The graph of
such a fibre-constant function is the preimage of `graphOf pt` under the coordinate selection
`ι : Fin (a+1) → Fin (a+b+1)` that keeps the first `a` coordinates and appends the value
coordinate (`graphOf_constFibre_eq`), and `Work.WilG5.coordPre_mem` turns that into an
`Ω`-membership.
-/

namespace Work.WilCrux.Clean

open WilkiesDesign

/-- The coordinate selection `Fin (a+1) → Fin (a+b+1)` that keeps the `a` parameter
coordinates and the last (value) coordinate, and forgets the `b` fibre coordinates. -/
private def iota (a b : ℕ) : Fin (a + 1) → Fin (a + b + 1) :=
  Fin.lastCases (Fin.last (a + b)) (fun i : Fin a => Fin.castAdd (b + 1) i)

/-- **The graph of a family constant in the fibre coordinates is a coordinate preimage.**

For `pt : ℝ^a → ℝ`, the graph of `u ↦ pt (u ∘ Fin.castAdd b)` (a subset of `ℝ^{a+b+1}`)
is the preimage of `graphOf pt` under `x ↦ x ∘ iota a b`. -/
theorem graphOf_constFibre_eq (a b : ℕ) (pt : (Fin a → ℝ) → ℝ) :
    WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ => pt (u ∘ Fin.castAdd b))
      = Work.WilG5.coordPre (iota a b) (WilkiesDesign.graphOf pt) := by
  ext x
  simp only [WilkiesDesign.graphOf, Work.WilG5.coordPre, Set.mem_ofPred_eq,
    Function.comp_apply]
  have hlast : iota a b (Fin.last a) = Fin.last (a + b) := Fin.lastCases_last ..
  have hinit : Fin.init (x ∘ iota a b) = Fin.init x ∘ Fin.castAdd b := by
    funext i
    show x (iota a b i.castSucc) = x ((Fin.castAdd b i).castSucc)
    simp only [iota, Fin.lastCases_castSucc]
    congr 1
  rw [hlast, hinit]

/-- **Shearing a family by its value on the zero fibre preserves `Ω`-definability.** -/
theorem SheetHatGraphMem (S : WilkiesDesign.SOMin) {a b F D F₁ D₁ : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (ha : WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) ∈ S.Ω F₁ D₁ (a + 1)) :
    ∃ F₂ D₂ : ℕ, WilkiesDesign.CG.famGraph
      (fun (w : Fin a → ℝ) (z : Fin b → ℝ) => G w z - G w 0)
        ∈ S.Ω F₂ D₂ (a + b + 1) := by
  set pt : (Fin a → ℝ) → ℝ := fun w => G w 0 with hpt
  -- the zero-fibre function, viewed as a family in `ℝ^{a+b+1}`, is `Ω`-definable
  have hQ : WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ => pt (u ∘ Fin.castAdd b))
      ∈ S.Ω (F₁ + 64 * ((a + b + 1) + (a + 1)) + 64)
          (D₁ + 32 * ((a + b + 1) + (a + 1)) + 32) (a + b + 1) := by
    rw [graphOf_constFibre_eq]
    exact Work.WilG5.coordPre_mem (S := S) (m := a + 1) (N := a + b + 1)
      (ι := iota a b) (A := WilkiesDesign.graphOf pt) ha
  -- `famGraph G` is the graph of `P`, and the sheared family is the graph of `P - Q`
  have hsub := Work.WilkG4c.GraphOfSubMem (S := S) (n := a + b)
    (f := fun u : Fin (a + b) → ℝ => G (u ∘ Fin.castAdd b) (u ∘ Fin.natAdd a))
    (h := fun u : Fin (a + b) → ℝ => pt (u ∘ Fin.castAdd b)) hG hQ
  obtain ⟨F₂, D₂, hF⟩ := hsub
  exact ⟨F₂, D₂, hF⟩

end Work.WilCrux.Clean
