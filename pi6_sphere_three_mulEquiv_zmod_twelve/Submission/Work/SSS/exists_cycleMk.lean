import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- Every homology class of a chain complex of `ℤ`-modules has a cycle representative: it is the
class of `Work.SSS`-style `cyclesMk z` for some cycle `z`. -/
theorem exists_cycleMk (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) (y : K.homology i) :
    ∃ (z : K.X i) (hz : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) z = 0),
      y = K.homologyπ i (K.cyclesMk z ((ComplexShape.down ℕ).next i) rfl hz) := by
  -- `homologyπ i` is surjective in the concrete category of `ℤ`-modules.
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance y
  -- The underlying cycle of `c` is the inclusion of `c` under `iCycles`.
  have hz : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) ((K.iCycles i) c) = 0 := by
    have h0 : K.iCycles i ≫ K.d i ((ComplexShape.down ℕ).next i) = 0 :=
      HomologicalComplex.iCycles_d K i _
    have h1 : (ConcreteCategory.hom (K.iCycles i ≫ K.d i ((ComplexShape.down ℕ).next i))) c = 0 := by
      rw [h0]; rfl
    rwa [ConcreteCategory.comp_apply] at h1
  refine ⟨(K.iCycles i) c, hz, ?_⟩
  rw [← hc]; congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  exact (HomologicalComplex.i_cyclesMk (K := K) ((ConcreteCategory.hom (K.iCycles i)) c)
    ((ComplexShape.down ℕ).next i) rfl hz).symm

end Work.SSS
