import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.sdLC_boundary
import Submission.Work.Cohomology.toChain_boundaryLC
import Submission.Work.Cohomology.affineSimplex_map_target
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
namespace Work.SSSR.Cohomology

noncomputable section


/-- Naturality of `TopCat.toSSetObjEquivT` in the space: precomposition with `g` corresponds to
composition of the underlying continuous maps with `g`. -/
lemma toSSetObjEquiv_map_apply {X Y : TopCat} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) (z : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquivT Y n ((TopCat.toSSet.map f).app n x) z
      = f (TopCat.toSSetObjEquivT X n x z) := rfl

/-- The chain map induced by a simplicial map, on a generator `a • x`. -/
lemma chainComplexMap_ι_apply (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet} (f : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) (a : R) :
    (SSet.chainComplexMap f (ModuleCat.of R R)).f n
        ((X.ιChainComplex (R := ModuleCat.of R R) x).hom a)
      = (Y.ιChainComplex (R := ModuleCat.of R R) (f.app (Opposite.op ⦋n⦌) x)).hom a := by
  have h := SSet.ι_chainComplexMap_f X Y f (ModuleCat.of R R) x
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X n) =>
    g.hom a) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The generator `1 • σ` of the singular chains of `X`, in the `singularChains` guise. -/
def gen (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) : (singularChains R X).X n :=
  ModuleCat.Hom.hom ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ) (1 : R)

end

end Work.SSSR.Cohomology
