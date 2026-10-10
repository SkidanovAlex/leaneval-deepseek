import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.naturalAlpha.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.naturalAlpha

open Work.Shrinking
open Work.CohomologicalShrinking
open scoped TensorProduct
open CategoryTheory

/-- **Naturality of the corestriction of the Hochschild–Serre sequence.**

Given a commuting square of groups

`G --fm--> H`, `G' --fn--> H'`, `g : G →* G'`, `h : H →* H'` with `h ∘ fm = fn ∘ g`,
a coefficient morphism `ψ : X ⟶ Res(h)(Y)` and a morphism `φ : Res(fm)(X) ⟶ Res(g)(Res(fn)(Y))`
whose underlying linear map agrees with that of `ψ`, the corestrictions commute:
`H₁(G, Res(fm)(X)) → H₁(H, X) → H₁(H', Y)` equals
`H₁(G, Res(fm)(X)) → H₁(G', Res(fn)(Y)) → H₁(H', Y)`. -/
theorem corestriction_natural {k : Type} [CommRing k]
    {G G' H H' : Type} [Group G] [Group G'] [Group H] [Group H']
    (fm : G →* H) (fn : G' →* H') (g : G →* G') (h : H →* H')
    (hfg : h.comp fm = fn.comp g)
    {X : Rep k H} {Y : Rep k H'} (ψ : X ⟶ Rep.res h Y)
    (φ : Rep.res fm X ⟶ Rep.res g (Rep.res fn Y))
    (hφ : (Rep.Hom.hom φ).toLinearMap = (Rep.Hom.hom ψ).toLinearMap) :
    (groupHomology.map fm (𝟙 (Rep.res fm X)) 1) ≫ (groupHomology.map h ψ 1)
      = (groupHomology.map g φ 1) ≫ (groupHomology.map fn (𝟙 (Rep.res fn Y)) 1) := by
  rw [← groupHomology.map_comp fm h (𝟙 (Rep.res fm X)) ψ 1,
      ← groupHomology.map_comp g fn φ (𝟙 (Rep.res fn Y)) 1]
  refine groupHomology.map_congr hfg ?_ 1
  simp only [CategoryTheory.Category.id_comp]
  rw [show Rep.resMap g (𝟙 (Rep.res fn Y)) = 𝟙 (Rep.res g (Rep.res fn Y)) from rfl,
      CategoryTheory.Category.comp_id, Rep.resMap_hom_toLinearMap]
  exact hφ.symm

theorem cores_natural (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    {m n : ℕ} (Φ : OperatorMap G m n) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    (flowZMap (p := p) G i j Φ T).comp (coresH p G i j T m)
      = (coresH p G i j T n).comp (mapNormal p G i j Φ T) := by
  have hfg : (flowGroupMap p G i j Φ).comp ((flowNormal p G m i j).subtype)
      = ((flowNormal p G n i j).subtype).comp (flowNormalSubMap p G i j Φ) :=
    MonoidHom.ext (fun x => flowGroupMap_subtype p G i j Φ x)
  have hkey := corestriction_natural (k := ZMod p)
    (fm := (flowNormal p G m i j).subtype) (fn := (flowNormal p G n i j).subtype)
    (g := flowNormalSubMap p G i j Φ) (h := flowGroupMap p G i j Φ) hfg
    (X := flowRep p G m i j T) (Y := flowRep p G n i j T)
    (ψ := flowRepMap (p := p) G i j Φ T)
    (φ := flowRepMapN (p := p) G i j Φ T)
    (hφ := rfl)
  apply AddMonoidHom.ext
  intro x
  show ((groupHomology.map ((flowNormal p G m i j).subtype)
          (𝟙 (Rep.res ((flowNormal p G m i j).subtype) (flowRep p G m i j T))) 1) ≫
        (groupHomology.map (flowGroupMap p G i j Φ) (flowRepMap (p := p) G i j Φ T) 1)).hom x
      = ((groupHomology.map (flowNormalSubMap p G i j Φ) (flowRepMapN (p := p) G i j Φ T) 1) ≫
        (groupHomology.map ((flowNormal p G n i j).subtype)
          (𝟙 (Rep.res ((flowNormal p G n i j).subtype) (flowRep p G n i j T))) 1)).hom x
  rw [hkey]

end Work.CohomologicalShrinking.naturalAlpha
