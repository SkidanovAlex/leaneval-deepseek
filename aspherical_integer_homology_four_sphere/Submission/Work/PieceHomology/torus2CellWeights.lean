/-
# The barycentric weights of a point of the torus, in the coordinates `[0,1)`

For each of the six cells of the `Δ`-structure of the `2`-torus
(`Torus2Chi.lean`), the coordinates `ux`, `uy ∈ [0,1)` of a point `x = χ w` in the
*interior* of the cell are the barycentric weights of `w`, as prescribed by the
characteristic map:

* `T₀ : (w₀,w₁,w₂) ↦ (w₁+w₂, w₂)` (the triangle `0 < y < x < 1`),
* `T₁ : (w₀,w₁,w₂) ↦ (w₂, w₁+w₂)` (the triangle `0 < x < y < 1`),
* `a : (w₀,w₁) ↦ (w₁, 0)`, `b : (w₀,w₁) ↦ (0, w₁)`, `c : (w₀,w₁) ↦ (w₁, w₁)`,
* the vertex maps to `(0,0)`.

The point of the strict positivity hypothesis `IsOpenSimplexPoint` is exactly that all the
weights appearing below lie in `[0,1)`: a coordinate is the *representative in `[0,1)`*
of its class in `ℝ/ℤ` (`coord`), and the weight `w.weights i` is recovered from the class
`(w.weights i : ℝ/ℤ)` because `0 ≤ w.weights i < 1`.
-/
import Mathlib
import Submission.Work.PieceHomology.Torus2Chi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Convexity

namespace Work.PieceHomology

noncomputable section

/-! ## §1  Two elementary facts about the coordinates -/

/-- The representative in `[0,1)` of the class of a real number of `[0,1)` is that number. -/
private lemma coord_coe_Ico {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) :
    coord ((a : ℝ) : AddCircle (1 : ℝ)) = a :=
  coord_coe ⟨h0, h1⟩

/-- A barycentric weight of the standard `n`-simplex which is not the only positive weight is
strictly smaller than `1` (the weights are non-negative and sum to `1`). -/
private lemma weights_lt_one {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1))) {i j : Fin (n + 1)}
    (hij : j ≠ i) (hj : 0 < w.weights j) : w.weights i < 1 := by
  have h := Finset.single_lt_sum (f := fun k : Fin (n + 1) => w.weights k) (s := Finset.univ)
    hij (Finset.mem_univ i) (Finset.mem_univ j) hj
    (fun k _ _ => StdSimplex.weights_nonneg (w := w) k)
  rwa [StdSimplex.total_of_fintype w] at h

/-- The sum of the last two weights of a point of `Δ²` whose first weight is positive. -/
private lemma sum_lt_one_fin3 (w : StdSimplex ℝ (Fin 3)) (h : 0 < w.weights 0) :
    w.weights 1 + w.weights 2 < 1 := by
  have hs := StdSimplex.total_of_fintype w
  rw [Fin.sum_univ_three] at hs
  linarith

/-! ## §2  The weights of the six cells -/

theorem torus2CellWeights :
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (w : Convexity.StdSimplex ℝ (Fin 3)),
        Work.DeltaHomology.IsOpenSimplexPoint 2 w → Work.PieceHomology.chiT0 w = x →
        Work.PieceHomology.uy x = w.weights 2 ∧
          Work.PieceHomology.ux x = w.weights 1 + w.weights 2) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (w : Convexity.StdSimplex ℝ (Fin 3)),
        Work.DeltaHomology.IsOpenSimplexPoint 2 w → Work.PieceHomology.chiT1 w = x →
        Work.PieceHomology.ux x = w.weights 2 ∧
          Work.PieceHomology.uy x = w.weights 1 + w.weights 2) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (w : Convexity.StdSimplex ℝ (Fin 2)),
        Work.DeltaHomology.IsOpenSimplexPoint 1 w → Work.PieceHomology.chiA w = x →
        Work.PieceHomology.ux x = w.weights 1 ∧ Work.PieceHomology.uy x = 0) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (w : Convexity.StdSimplex ℝ (Fin 2)),
        Work.DeltaHomology.IsOpenSimplexPoint 1 w → Work.PieceHomology.chiB w = x →
        Work.PieceHomology.uy x = w.weights 1 ∧ Work.PieceHomology.ux x = 0) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (w : Convexity.StdSimplex ℝ (Fin 2)),
        Work.DeltaHomology.IsOpenSimplexPoint 1 w → Work.PieceHomology.chiC w = x →
        Work.PieceHomology.ux x = w.weights 1 ∧ Work.PieceHomology.uy x = w.weights 1) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (w : Convexity.StdSimplex ℝ (Fin 1)),
        Work.PieceHomology.chiV w = x → Work.PieceHomology.ux x = 0 ∧
          Work.PieceHomology.uy x = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the lower triangle `T₀ : (w₀,w₁,w₂) ↦ (w₁+w₂, w₂)`
    intro x w hw hx
    rw [← hx]
    refine ⟨?_, ?_⟩
    · show coord ((chiT0 w) 1) = w.weights 2
      rw [show (chiT0 w) 1 = ((w.weights 2 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiT0, tpt]]
      exact coord_coe_Ico (StdSimplex.weights_nonneg (w := w) 2)
        (weights_lt_one w (i := 2) (j := 0) (by decide) (hw 0))
    · show coord ((chiT0 w) 0) = w.weights 1 + w.weights 2
      rw [show (chiT0 w) 0 = ((w.weights 1 + w.weights 2 : ℝ) : AddCircle (1 : ℝ)) from by
        simp [chiT0, tpt]]
      exact coord_coe_Ico (by linarith [StdSimplex.weights_nonneg (w := w) 1,
        StdSimplex.weights_nonneg (w := w) 2]) (sum_lt_one_fin3 w (hw 0))
  · -- the upper triangle `T₁ : (w₀,w₁,w₂) ↦ (w₂, w₁+w₂)`
    intro x w hw hx
    rw [← hx]
    refine ⟨?_, ?_⟩
    · show coord ((chiT1 w) 0) = w.weights 2
      rw [show (chiT1 w) 0 = ((w.weights 2 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiT1, tpt]]
      exact coord_coe_Ico (StdSimplex.weights_nonneg (w := w) 2)
        (weights_lt_one w (i := 2) (j := 0) (by decide) (hw 0))
    · show coord ((chiT1 w) 1) = w.weights 1 + w.weights 2
      rw [show (chiT1 w) 1 = ((w.weights 1 + w.weights 2 : ℝ) : AddCircle (1 : ℝ)) from by
        simp [chiT1, tpt]]
      exact coord_coe_Ico (by linarith [StdSimplex.weights_nonneg (w := w) 1,
        StdSimplex.weights_nonneg (w := w) 2]) (sum_lt_one_fin3 w (hw 0))
  · -- the edge `a : (w₀,w₁) ↦ (w₁, 0)`
    intro x w hw hx
    rw [← hx]
    refine ⟨?_, ?_⟩
    · show coord ((chiA w) 0) = w.weights 1
      rw [show (chiA w) 0 = ((w.weights 1 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiA, tpt]]
      exact coord_coe_Ico (StdSimplex.weights_nonneg (w := w) 1)
        (weights_lt_one w (i := 1) (j := 0) (by decide) (hw 0))
    · show coord ((chiA w) 1) = 0
      rw [show (chiA w) 1 = ((0 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiA, tpt]]
      exact coord_coe_Ico le_rfl zero_lt_one
  · -- the edge `b : (w₀,w₁) ↦ (0, w₁)`
    intro x w hw hx
    rw [← hx]
    refine ⟨?_, ?_⟩
    · show coord ((chiB w) 1) = w.weights 1
      rw [show (chiB w) 1 = ((w.weights 1 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiB, tpt]]
      exact coord_coe_Ico (StdSimplex.weights_nonneg (w := w) 1)
        (weights_lt_one w (i := 1) (j := 0) (by decide) (hw 0))
    · show coord ((chiB w) 0) = 0
      rw [show (chiB w) 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiB, tpt]]
      exact coord_coe_Ico le_rfl zero_lt_one
  · -- the diagonal edge `c : (w₀,w₁) ↦ (w₁, w₁)`
    intro x w hw hx
    rw [← hx]
    refine ⟨?_, ?_⟩
    · show coord ((chiC w) 0) = w.weights 1
      rw [show (chiC w) 0 = ((w.weights 1 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiC, tpt]]
      exact coord_coe_Ico (StdSimplex.weights_nonneg (w := w) 1)
        (weights_lt_one w (i := 1) (j := 0) (by decide) (hw 0))
    · show coord ((chiC w) 1) = w.weights 1
      rw [show (chiC w) 1 = ((w.weights 1 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiC, tpt]]
      exact coord_coe_Ico (StdSimplex.weights_nonneg (w := w) 1)
        (weights_lt_one w (i := 1) (j := 0) (by decide) (hw 0))
  · -- the vertex `(0,0)`
    intro x w hx
    rw [← hx]
    refine ⟨?_, ?_⟩
    · show coord ((chiV w) 0) = 0
      rw [show (chiV w) 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiV, tpt]]
      exact coord_coe_Ico le_rfl zero_lt_one
    · show coord ((chiV w) 1) = 0
      rw [show (chiV w) 1 = ((0 : ℝ) : AddCircle (1 : ℝ)) from by simp [chiV, tpt]]
      exact coord_coe_Ico le_rfl zero_lt_one

end

end Work.PieceHomology
