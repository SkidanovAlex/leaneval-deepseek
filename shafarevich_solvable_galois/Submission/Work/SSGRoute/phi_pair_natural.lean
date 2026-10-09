import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phiPushClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the level pairing under inflation

This is a piece of node `E4` (`Work.SSGRoute.phi0_trivial_epi`, `DESIGN_EXT.md`): the Yoneda
pairing with a coefficient class commutes with inflation.

With `f = galRes k L L' : Gal(L'/k) →* Gal(L/k)`, `c : 𝔽_p ⟶ C_L` a coefficient class at the level
`L` and `h ∈ H²(Gal(L/k), 𝔽_p)`, both sides of the statement are `Ext²_Gal(L'/k)(ℤ, C_{L'})`; after
unfolding, the left side is
`mk₀ (unitRes f) ∘ (extRes f h ∘ mk₀ (res c ≫ classIncl k L L'))` and the right side is the same
with `mk₀ (trivResInv f) ∘ mk₀ (trivRes f)` inserted in the middle; these cancel because
`trivResInv f V ≫ trivRes f V = 𝟙`.  The statement and proof are independent of any canonicity
property of `classIncl` (both sides use the *same* morphism `classIncl k L L'`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1000000

/-- The canonical isomorphism `Rep.res f (Rep.trivial Coeff G V) ≅ Rep.trivial Coeff H V` is
inverse to the companion map. -/
theorem trivResInv_comp_trivRes {G H : Type} [Group G] [Group H] (f : H →* G)
    (V : Type) [AddCommGroup V] [Module Coeff V] :
    trivResInv f V ≫ trivRes f V = 𝟙 _ := by
  ext x
  rfl

/-- **Naturality of the level pairing under inflation.**  Inflating the value of the level-`L`
Yoneda pairing of a coefficient class `c` with `h` to the level `L' ⊇ L` equals the level-`L'`
pairing of the pushed-forward class `pushClass k L L' 𝔽_p c` with the inflated class
`inflTriv h`. -/
theorem phi_pair_natural (p : ℕ) [Fact p.Prime] (k L L' : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Field L'] [NumberField L']
    [Algebra k L] [Algebra k L'] [Algebra L L'] [IsScalarTower k L L']
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (c : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ classesK k L)
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2) :
    inflC (k := k) (K := L) (L := L') (pairK (k := k) (K := L) (Abelian.Ext.mk₀ c) h)
      = pairK (k := k) (K := L') (Abelian.Ext.mk₀ (pushClass k L L' (ZMod p) c))
          (inflTriv (k := k) (K := L) (L := L') (ZMod p) h) := by
  have hmorph :
      (trivResInv (galRes k L L') (ZMod p) ≫ trivRes (galRes k L L') (ZMod p)
        ≫ Rep.resMap (galRes k L L') c ≫ classIncl k L L')
        = (Rep.resMap (galRes k L L') c ≫ classIncl k L L') := by
    rw [← Category.assoc, trivResInv_comp_trivRes, Category.id_comp]
  simp only [pairK, yonedaPair, inflC, inflTriv, extHMap, pushClass, extRes,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [show Abelian.Ext.mk₀ (trivResInv (galRes k L L') (ZMod p) ≫ trivRes (galRes k L L') (ZMod p)
        ≫ Rep.resMap (galRes k L L') c ≫ classIncl k L L')
      = Abelian.Ext.mk₀ (Rep.resMap (galRes k L L') c ≫ classIncl k L L')
      from congrArg Abelian.Ext.mk₀ hmorph]

end Work.SSGRoute
