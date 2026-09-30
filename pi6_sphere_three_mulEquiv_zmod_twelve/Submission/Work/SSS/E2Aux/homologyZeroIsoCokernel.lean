import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.E2Aux

open CategoryTheory CategoryTheory.Limits

theorem homologyZeroIsoCokernel (K : ChainComplex (ModuleCat ℤ) ℕ) :
    Nonempty (CategoryTheory.Iso (K.homology 0)
      (CategoryTheory.Limits.cokernel (K.d 1 0))) := by
  -- In degree `0` for a `ℕ`-indexed chain complex, the incoming differential is
  -- `K.d 1 0` and the outgoing one is `K.d 0 0 = 0`, so `H₀` is the cokernel of `K.d 1 0`.
  have hprev : (ComplexShape.down ℕ).prev 0 = 1 :=
    ComplexShape.prev_eq' (ComplexShape.down ℕ) (i := 0) (j := 1) (by simp [ComplexShape.down])
  have hnext : (ComplexShape.down ℕ).next 0 = 0 := by
    rw [ComplexShape.next_eq_self']; intro k; simp [ComplexShape.down]
  -- The short complex `K.sc' 1 0 0` has `f = K.d 1 0` and `g = K.d 0 0 = 0`.
  have hg : (K.sc' 1 0 0).g = 0 := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_g]
    exact K.shape 0 0 (by simp [ComplexShape.down])
  refine ⟨(HomologicalComplex.homologyIsoSc' K 1 0 0 hprev hnext).trans ?_⟩
  -- Since the second differential of this short complex is zero, its homology is
  -- the cokernel of its first differential `K.d 1 0`.
  exact ShortComplex.RightHomologyData.homologyIso
    (ShortComplex.RightHomologyData.ofHasCokernel (K.sc' 1 0 0) hg)

end Work.SSS.E2Aux
