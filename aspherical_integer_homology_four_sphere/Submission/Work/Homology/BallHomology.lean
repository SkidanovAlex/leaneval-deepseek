import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Point

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The vanishing of the reduced homology of a ball

The open unit ball `B^n ⊂ ℝ^n` is convex, hence contractible, hence homotopy
equivalent to a point.  Since singular homology is homotopy invariant and the
higher singular homology of a point vanishes, `H_k(B^n; R) = 0` for `k ≥ 1`.

The main ingredient is the general lemma
`isZero_singHomology_succ_of_contractibleSpace`: a contractible space has
trivial singular homology in positive degrees with arbitrary coefficients.
-/

namespace Work.Homology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-- A contractible topological space has trivial reduced singular homology: its
`k`-th singular homology vanishes for every `k ≥ 1`, with coefficients in any
`R : ModuleCat ℤ`.

The proof is the standard one: the identity of `X` is homotopic to a constant
map, so by homotopy invariance of singular homology `𝟙` and the map induced by
the constant map agree.  The constant map factors through a point, whose
positive-degree homology is zero, so `𝟙 = 0` on `H_k(X;R)` and the module is
trivial. -/
theorem isZero_singHomology_succ_of_contractibleSpace (R : ModuleCat ℤ) (X : TopCat)
    [ContractibleSpace X] (k : ℕ) : IsZero (singHomology R (k + 1) X) := by
  -- a point `p` together with a homotopy from the identity to the constant map
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic X
  let q : X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let i : TopCat.of PUnit ⟶ X := TopCat.ofHom ⟨fun _ => p, continuous_const⟩
  let c : X ⟶ X := TopCat.ofHom ⟨fun _ => p, continuous_const⟩
  -- the constant map factors through the point
  have hc : c = q ≫ i := by ext x; rfl
  have hH : TopCat.Homotopy (𝟙 X) c := H
  -- homotopy invariance of singular homology
  have key : singHomologyMap R (k + 1) (𝟙 X) = singHomologyMap R (k + 1) c :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor hH R (k + 1)
  -- the map induced by the constant map is zero, as it factors through `H_{k+1}(pt) = 0`
  have h1 : singHomologyMap R (k + 1) c = 0 := by
    rw [hc, singHomologyMap_comp]
    have hz : singHomologyMap R (k + 1) i = 0 :=
      IsZero.eq_zero_of_src (isZero_singHomology_point R k) _
    rw [hz, comp_zero]
  -- hence the identity of `H_{k+1}(X;R)` is zero, so the module is trivial
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  rw [← singHomologyMap_id R (k + 1) X]
  exact key.trans h1

/-- The unit ball of `EuclideanSpace ℝ (Fin n)` is contractible. -/
instance (n : ℕ) : ContractibleSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  Metric.contractibleSpace_ball one_pos

/-- The `(k+1)`-st singular homology of the open unit ball of `ℝ^n` vanishes,
with coefficients in any `R : ModuleCat ℤ`. -/
theorem BallHomology (R : ModuleCat ℤ) (n : ℕ) (k : ℕ) :
    CategoryTheory.Limits.IsZero (singHomology R (k + 1)
      (TopCat.of (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))) :=
  isZero_singHomology_succ_of_contractibleSpace R _ k

end

end Work.Homology
