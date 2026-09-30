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
# Homology of the standard simplex

The standard simplex `Convexity.StdSimplex ℝ (Fin (n+1))` is convex, hence
contractible, and a contractible space has vanishing reduced singular homology.
This file proves that `H_{k+1}` of the standard `n`-simplex vanishes.
-/

namespace Work.Homology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- A contractible space has vanishing reduced singular homology:
`H_{k+1}(X; R) = 0`. -/
theorem isZero_singHomology_succ_of_contractible (R : ModuleCat ℤ) (X : TopCat)
    [ContractibleSpace X] (k : ℕ) : IsZero (singHomology R (k + 1) X) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic X
  have hH : singHomologyMap R (k + 1) (𝟙 X) =
      singHomologyMap R (k + 1) (TopCat.const (X := X) (Y := X) y) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R (k + 1)
  have hconst : singHomologyMap R (k + 1) (TopCat.const (X := X) (Y := X) y) = 0 := by
    have hp : TopCat.const (X := X) (Y := X) y =
        (TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩ : X ⟶ TopCat.of PUnit) ≫
        (TopCat.ofHom ⟨fun _ => y, continuous_const⟩ : TopCat.of PUnit ⟶ X) := by
      ext x
      rfl
    rw [hp, singHomologyMap_comp]
    have hq : singHomologyMap R (k + 1)
        (TopCat.ofHom ⟨fun _ => y, continuous_const⟩ : TopCat.of PUnit ⟶ X) = 0 :=
      (isZero_singHomology_point R k).eq_of_src _ _
    rw [hq, comp_zero]
  rw [IsZero.iff_id_eq_zero, ← singHomologyMap_id R (k + 1) X]
  exact hH.trans hconst

/-- The standard simplex `StdSimplex ℝ (Fin (n+1))` is contractible. -/
theorem contractibleSpace_stdSimplex (n : ℕ) :
    ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) := by
  have hf := Convexity.StdSimplex.isEmbedding_toFun_comp_weights (R := ℝ) (Fin (n + 1))
  have hne : (Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (t.weights : Fin (n + 1) → ℝ))).Nonempty :=
    ⟨(Convexity.StdSimplex.single (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))).weights,
      Set.mem_range_self _⟩
  have hconv : Convex ℝ (Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (t.weights : Fin (n + 1) → ℝ))) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    rw [convex_iff_forall_pos]
    intro x hx y hy a b ha hb hab
    rw [Set.mem_inter_iff, Set.mem_iInter] at hx hy ⊢
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      nlinarith [hx.1 i, hy.1 i]
    · simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
      linarith
  have : ContractibleSpace (Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (t.weights : Fin (n + 1) → ℝ))) := Convex.contractibleSpace hconv hne
  exact hf.toHomeomorph.contractibleSpace_iff.mpr inferInstance

theorem StdSimplexHomology (R : ModuleCat ℤ) (n : ℕ) (k : ℕ) :
    CategoryTheory.Limits.IsZero (singHomology R (k + 1)
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))))) := by
  have := contractibleSpace_stdSimplex n
  exact isZero_singHomology_succ_of_contractible R (TopCat.of _) k

end

end Work.Homology
