import Mathlib
import Submission.Work.SSS.vertRestrEZDefs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- **The vertex restriction of the prism map at the vertex `0` of `Δ[1]` is the source
inclusion of the fibre.**

Proof route: `e.hom` is a split mono (`e.hom ≫ e.inv = 𝟙`, `Iso.hom_inv_id`), so it suffices to
compare the two maps into the pullback `pullback (sSingP p) (sSingP γ.toContinuousMap)`, which is
done with `pullback.hom_ext` on the two projections:
* first projection: rewrite with `he₁`, then `Work.SSS.vertZ_fst`, then
  `CategoryTheory.CartesianMonoidalCategory.lift_map` and
  `Work.SSS.vertEdge_vtx0` + `SSet.const_comp` to obtain `vertIncl p b (s+1) ≫ liftFam ...`,
  which is `sSingP (fibreIncl p b)` by `Work.SSS.liftFam_vert`; on the other side use
  `Work.SSS.inclSource_comp_pullbackFst` and functoriality of `sSingP`;
* second projection: `Work.SSS.vertZI`, `CategoryTheory.CartesianMonoidalCategory.lift_fst`
  (giving `SSet.const ν ≫ vertLiftI`), `SSet.const_comp` and
  `Work.SSS.toSSetObj₀Equiv_vertLiftI_vtx0` (which says that `vertLiftI.app ν` is the point `0`);
  on the other side `Work.SSS.inclSource_comp_pullbackSnd` and `TopCat.toSSet_map_const`. -/
theorem vertZvtx_vtx0 {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (γ : Path b (Work.SSS.sigmaVert (CategoryTheory.CategoryStruct.comp
        (SSet.stdSimplex.δ (n := s) 0) σ)))
    (hγ : (Work.SSS.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSS.lambda1 = Work.SSS.vertEdgeSimplex s σ)
    (e : CategoryTheory.Iso (Work.SSS.sSing (Work.StemsB.Pullback p γ.toContinuousMap))
        (CategoryTheory.Limits.pullback (Work.SSS.sSingP p) (Work.SSS.sSingP γ.toContinuousMap)))
    (he₁ : CategoryTheory.CategoryStruct.comp e.hom
        (CategoryTheory.Limits.pullback.fst (Work.SSS.sSingP p) (Work.SSS.sSingP γ.toContinuousMap))
        = Work.SSS.sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap))
    (he₂ : CategoryTheory.CategoryStruct.comp e.hom
        (CategoryTheory.Limits.pullback.snd (Work.SSS.sSingP p) (Work.SSS.sSingP γ.toContinuousMap))
        = Work.SSS.sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap)) :
    Work.SSS.vertZvtx p hfib s b σ h γ hγ e Work.SSS.vtx0S1
      = Work.SSS.sSingP (Work.SSS.inclSource p γ) := by
  -- The `E`-component of the vertex-`0` restriction of the prism map is the fibre inclusion.
  have hfst : vertInclS1 p b vtx0S1 ≫ vertZE p hfib s b σ h
      = sSingP (Work.StemsB.fibreIncl p b) := by
    rw [vertInclS1, vertZE, ← Category.assoc, CartesianMonoidalCategory.lift_map]
    rw [SSet.const_comp]
    rw [vertEdge_vtx0]
    simp only [Category.id_comp]
    exact liftFam_vert p hfib (s+1) b σ h
  -- The `I`-component of the vertex-`0` restriction is the constant map at the point `0`.
  have hsnd : vertInclS1 p b vtx0S1 ≫ vertZI p b
      = SSet.const (vertLiftI.app (op ⦋0⦌) vtx0S1) := by
    rw [vertZI, vertInclS1, ← Category.assoc, CartesianMonoidalCategory.lift_fst, SSet.const_comp]
  -- The same two components for the source inclusion of the pullback.
  have h1 : sSingP (inclSource p γ)
      ≫ (e.hom ≫ pullback.fst (sSingP p) (sSingP γ.toContinuousMap))
      = sSingP (Work.StemsB.fibreIncl p b) := by
    rw [he₁]
    simp only [sSingP]
    rw [← Functor.map_comp, inclSource_comp_pullbackFst]
  have h2 : sSingP (inclSource p γ)
      ≫ (e.hom ≫ pullback.snd (sSingP p) (sSingP γ.toContinuousMap))
      = SSet.const (vertLiftI.app (op ⦋0⦌) vtx0S1) := by
    rw [he₂]
    simp only [sSingP]
    rw [← Functor.map_comp, inclSource_comp_pullbackSnd, TopCat.toSSet_map_const]
    rw [show TopCat.toSSetObj₀Equiv.symm (0 : unitInterval)
        = vertLiftI.app (op ⦋0⦌) vtx0S1 from by
      rw [← toSSetObj₀Equiv_vertLiftI_vtx0, Equiv.symm_apply_apply]]
  -- Both sides become the same map into the pullback after composing with `e.hom`.
  have key : vertInclS1 p b vtx0S1
      ≫ pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
          (vertZcompat p hfib s b σ h γ hγ)
      = sSingP (inclSource p γ) ≫ e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hfst, Category.assoc, h1]
    · rw [Category.assoc, pullback.lift_snd, hsnd, Category.assoc, h2]
  show vertInclS1 p b vtx0S1
      ≫ (pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
          (vertZcompat p hfib s b σ h γ hγ) ≫ e.inv) = sSingP (inclSource p γ)
  rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Work.SSS
