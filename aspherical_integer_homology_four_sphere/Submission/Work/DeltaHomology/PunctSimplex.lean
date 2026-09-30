import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The punctured standard simplex

The standard `k`-simplex `StdSimplex ℝ (Fin (k+1))` with its barycentre removed.  This is
the space on which the radial collar of the boundary is constructed: the barycentre is the
only point removed, so the complement of the barycentre is exactly the set of points from
which the radial projection to the boundary is defined.

The file `Submission/Work/DeltaHomology/exists_collar_deformationRetract.lean` proves the
existence of such a collar for a (private) neighbourhood, and the file
`Submission/Work/DeltaHomology/collarPunctSimplex.lean` re-proves it for the punctured
simplex `punctStdSimplex` defined here.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

/-- The punctured standard `k`-simplex: the standard `k`-simplex with its barycentre
removed. -/
def punctStdSimplex (k : ℕ) : Set (StdSimplex ℝ (Fin (k + 1))) :=
  {w | w ≠ simplexBarycenter k}

@[simp]
theorem mem_punctStdSimplex_iff {k : ℕ} {w : StdSimplex ℝ (Fin (k + 1))} :
    w ∈ punctStdSimplex k ↔ w ≠ simplexBarycenter k := Iff.rfl

theorem simplexBarycenter_not_mem_punctStdSimplex (k : ℕ) :
    simplexBarycenter k ∉ punctStdSimplex k := by
  simp

/-- The barycentre is the only point of the standard simplex at which all barycentric
coordinates take their barycentric value `1/(k+1)`. -/
theorem eq_simplexBarycenter_iff_weights {k : ℕ} {w : StdSimplex ℝ (Fin (k + 1))} :
    w = simplexBarycenter k ↔ ∀ i, w.weights i = ((k + 1 : ℕ) : ℝ)⁻¹ := by
  constructor
  · intro h i
    rw [h, simplexBarycenter_weights]
  · intro h
    refine StdSimplex.ext (Finsupp.ext fun i => ?_)
    rw [h i, simplexBarycenter_weights]

/-- A point of the standard simplex is off the barycentre exactly when one of its
barycentric coordinates differs from `1/(k+1)`. -/
theorem mem_punctStdSimplex_iff_exists_ne {k : ℕ} {w : StdSimplex ℝ (Fin (k + 1))} :
    w ∈ punctStdSimplex k ↔ ∃ i, w.weights i ≠ ((k + 1 : ℕ) : ℝ)⁻¹ := by
  constructor
  · intro hw
    by_contra h
    simp only [not_exists, not_not] at h
    exact hw (eq_simplexBarycenter_iff_weights.mpr h)
  · rintro ⟨i, hi⟩ hb
    exact hi (by rw [eq_simplexBarycenter_iff_weights.mp hb i])

variable {K : DeltaCx} {X : TopCat}

/-- The punctured closed simplex of the simplex `σ`: the image of the characteristic map of
`σ` with the barycentre of `σ` removed.  This is the piece of the collar `χ.punctSkel n`
carried by `σ`. -/
def DeltaSimplexMap.punctCell (χ : DeltaSimplexMap K X) (n : ℕ) (σ : Fin (K.card n)) : Set X :=
  χ.punctSkel n ∩ Set.range (χ.cls n σ)

theorem DeltaSimplexMap.mem_punctCell_iff (χ : DeltaSimplexMap K X) (n : ℕ)
    (σ : Fin (K.card n)) (x : X) :
    x ∈ χ.punctCell n σ ↔ x ∈ χ.punctSkel n ∧ ∃ y, χ.cls n σ y = x := Iff.rfl

theorem DeltaSimplexMap.punctCell_subset_punctSkel (χ : DeltaSimplexMap K X) (n : ℕ)
    (σ : Fin (K.card n)) : χ.punctCell n σ ⊆ χ.punctSkel n :=
  Set.inter_subset_left

/-- The collar of the `(k+1)`-skeleton is covered by the `k`-skeleton together with the images
of the closed `(k+1)`-simplices.  (Only the purely combinatorial structure of `K` is used; no
realization is needed.) -/
theorem DeltaSimplexMap.punctSkel_succ_subset (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.punctSkel (k + 1) ⊆
      χ.skelSet k ∪ ⋃ τ : Fin (K.card (k + 1)), Set.range (χ.cls (k + 1) τ) := by
  intro x hx
  have hx' : x ∈ χ.skelSet (k + 1) := hx.1
  rw [DeltaSimplexMap.skelSet] at hx'
  simp only [Set.mem_iUnion, Set.mem_range] at hx'
  obtain ⟨⟨j, hj⟩, σ, y, rfl⟩ := hx'
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact Or.inl (χ.cls_mem_skelSet (Nat.lt_succ_iff.mp hlt) σ y)
  · subst heq
    exact Or.inr (Set.mem_iUnion.mpr ⟨σ, y, rfl⟩)

end

end Work.DeltaHomology
