import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.CupRing
import Submission.Work.SSSR.Cohomology.Pullback
import Submission.Work.Cohomology.Singular
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
namespace Work.SSSR.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## The inclusion of a subspace and its effect on singular simplicial sets -/

/-- The inclusion `A ⊆ X` of a subset, as a morphism of topological spaces. -/
def subtypeIncl (X : TopCat) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The `n`-simplices of the singular simplicial set are continuous maps out of the standard
simplex; the identification `TopCat.toSSetObjEquivT` is natural in the space. -/
lemma toSSetObjEquiv_naturality_space {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSetObjEquivT Y (Opposite.op (SimplexCategory.mk n)))
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ)
      = (ConcreteCategory.hom f).comp
          ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n))) σ) := rfl

/-- A degreewise injective continuous map induces a degreewise injective map of singular
simplicial sets. -/
lemma injective_toSSet_map {X Y : TopCat} (f : X ⟶ Y)
    (hf : Function.Injective (ConcreteCategory.hom f)) (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))) := by
  intro σ τ h
  apply (TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro z
  apply hf
  have h2 := congrArg (fun g : C(stdSimplex ℝ (Fin (n+1)), Y) => g z)
    (congrArg (TopCat.toSSetObjEquivT Y (Opposite.op (SimplexCategory.mk n))) h)
  rw [toSSetObjEquiv_naturality_space, toSSetObjEquiv_naturality_space] at h2
  simpa only [ContinuousMap.comp_apply] using h2

/-- The underlying map of the subspace inclusion is injective. -/
lemma subtypeIncl_injective (X : TopCat) (A : Set X) :
    Function.Injective (ConcreteCategory.hom (subtypeIncl X A)) :=
  fun _ _ h => Subtype.ext h

/-! ## A splitting of the chain map `C_*(A) ⟶ C_*(X)`

Singular `n`-chains are the coproduct of one copy of `R` per singular `n`-simplex
(`SSet.isColimitChainComplexXCofan`), and the inclusion `A ⊆ X` is injective on simplices.  Hence
the induced map on chains sends the coproduct inclusion to a coproduct inclusion and admits a
retraction: a singular simplex of `X` that comes from `A` is sent back to (the unique) simplex it
comes from, and every other simplex is sent to `0`. -/

/-- The retraction of the chain map induced by the inclusion `A ⊆ X`: on the summand of a singular
simplex `y` of `X` lying in the image of `A`'s simplices, it is the (unique) simplex of `A` mapping
to `y`; on all other summands it is zero. -/
def chainRetract (X : TopCat) (A : Set X) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶
    ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of R R)).X n := by
  classical
  exact ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk (((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of R R)).X n)
      (fun y => if hy : ∃ x, (TopCat.toSSet.map (subtypeIncl X A)).app
              (Opposite.op (SimplexCategory.mk n)) x = y
                then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy)
                else 0))

/-- `chainRetract` is a retraction of the chain map induced by the inclusion `A ⊆ X`. -/
theorem chainRetract_spec (X : TopCat) (A : Set X) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R)).f n
      ≫ chainRetract R X A n = 𝟙 _ := by
  classical
  apply SSet.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, Category.comp_id]
  rw [chainRetract]
  refine (Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
      (fun y => if hy : ∃ x', (TopCat.toSSet.map (subtypeIncl X A)).app
              (Opposite.op (SimplexCategory.mk n)) x' = y
                then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy)
                else 0)
      ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x)).trans ?_
  have hy : ∃ x', (TopCat.toSSet.map (subtypeIncl X A)).app
        (Opposite.op (SimplexCategory.mk n)) x' =
      (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x := ⟨x, rfl⟩
  rw [dif_pos hy]
  congr 1
  exact (injective_toSSet_map (subtypeIncl X A) (subtypeIncl_injective X A) n)
    (Classical.choose_spec hy)

end

end Work.SSSR.Cohomology
