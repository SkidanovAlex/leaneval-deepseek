import Mathlib
import Submission.Work.SSS.gfDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.GradedKer

open CategoryTheory CategoryTheory.Limits

/-- The kernel of the canonical map `H_{k+1+t}(F_{k+1}) → E²_{k+1,t}` (`e2MapG ξ k t`) is contained
in the sum of `im(H_{k+1+t}(F_k) → H_{k+1+t}(F_{k+1}))` (the image of the inclusion of the previous
filtration step) and the kernel of `H_{k+1+t}(F_{k+1}) → H_{k+1+t}(C)`. -/
theorem ker_e2MapG_le (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Work.SSS.Filtration C) (k t : ℕ) :
    (Work.SSS.e2MapG ξ k t).hom.ker ≤
      (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F k) ((k+1)+t)).hom.range ⊔
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.ker := by
  intro x hx
  let S : ShortComplex (ModuleCat ℤ) := (E1Complex ξ t).sc' (k+2) (k+1) k
  let φ : (ξ.F.obj (k+1)).homology ((k+1)+t) ⟶ S.X₂ := jF ξ (k+1) t
  let κ : S.X₁ ⟶ (ξ.F.obj (k+1)).homology ((k+1)+t) := kF ξ (k+1) t
  have hφg : φ ≫ S.g = 0 := by
    show jF ξ (k+1) t ≫ ((E1Complex ξ t).sc' (k+2) (k+1) k).g = 0
    rw [scg]
    exact jFd1 ξ k t
  have hx' : ((S.liftCycles φ hφg ≫ S.homologyπ).hom) x = 0 := by
    show (ModuleCat.Hom.hom (e2MapG ξ k t)) x = 0
    exact hx
  have hmem : (φ.hom) x ∈ (S.f).hom.range := ker_sc_le S φ hφg x hx'
  have hSf : S.f = κ ≫ φ := by
    show ((E1Complex ξ t).sc' (k+2) (k+1) k).f = kF ξ (k+1) t ≫ jF ξ (k+1) t
    rw [scf]
    rfl
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  have hy' : (φ.hom) (κ.hom y) = (φ.hom) x := by
    rw [← hy, hSf, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hmem2 : x ∈ φ.hom.ker ⊔ κ.hom.range := by
    refine Submodule.mem_sup.mpr ⟨x - κ.hom y, ?_, κ.hom y, ?_, sub_add_cancel x (κ.hom y)⟩
    · rw [LinearMap.mem_ker, map_sub, hy', sub_self]
    · exact LinearMap.mem_range.mpr ⟨y, rfl⟩
  have hrange_le : (kF ξ (k+1) t).hom.range ≤
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.ker := by
    rw [LinearMap.range_le_ker_iff, ← ModuleCat.hom_comp, kFincl, ModuleCat.hom_zero]
  have hsub : φ.hom.ker ⊔ κ.hom.range ≤
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range ⊔
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.ker := by
    refine sup_le ?_ ?_
    · dsimp only [φ]
      exact le_trans (le_of_eq (kerjF ξ k t)) le_sup_left
    · dsimp only [κ]
      exact le_trans hrange_le le_sup_right
  exact hsub hmem2

end Work.SSS.GradedKer
