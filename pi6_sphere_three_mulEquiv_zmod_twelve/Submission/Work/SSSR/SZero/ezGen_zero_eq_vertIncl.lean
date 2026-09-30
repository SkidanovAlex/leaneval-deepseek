import Mathlib
import Submission.Work.SSSR.SZero.Defs
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.KunnethEZ.EZGenX
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR.SZero

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-- **`Δ[0]` has at most one simplex in each degree.**  The simplices of `Δ[0]` in degree `m` are
the morphisms `⦋m⦌ ⟶ ⦋0⦌`, all of which are the constant one. -/
instance instSubsingletonStdSimplexZeroObj (m : ℕ) :
    Subsingleton ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).obj
      (Opposite.op (SimplexCategory.mk m))) :=
  ⟨fun a b => SSet.stdSimplex.objEquiv.injective (by
    rw [SimplexCategory.eq_const_to_zero (SSet.stdSimplex.objEquiv a),
      SimplexCategory.eq_const_to_zero (SSet.stdSimplex.objEquiv b)])⟩

/-- **The vertical inclusion on `(0,q)`-simplices.**  The value of
`vertIncl p b 0 : Sing F_b ⟶ Δ[0] ⊗ Sing F_b` on the `(0,q)`-shuffle reindexing
`Y.map (bHom zSh).op τ` of `τ` is the pair consisting of the `(0,q)`-shuffle reindexing of the
fundamental `0`-simplex `[id₀]` of `Δ[0]` and of `Y.map (bHom zSh).op τ` itself.  The first
coordinate is forced by `instSubsingletonStdSimplexZeroObj`, the second by
`Work.SSSR.vertIncl_snd`. -/
lemma vertIncl_app_bHom {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (b : B) (q : ℕ)
    (τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q))) :
    (Work.SSSR.vertIncl p b 0).app (Opposite.op (SimplexCategory.mk (0 + q)))
        ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
          (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
            (Work.SSSR.KunnethEZ.zSh q).2)) τ)
      = ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).map
            (Work.SSSR.Cohomology.Crux33.aHom (Work.SSSR.KunnethEZ.zSh q).1
              (Work.SSSR.KunnethEZ.zSh q).2).op
            (Work.SSSR.stdIdSimplex 0),
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
              (Work.SSSR.KunnethEZ.zSh q).2)) τ) := by
  refine Prod.ext ?_ ?_
  · exact Subsingleton.elim _ _
  · have hh := congrArg (fun (g : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) ⟶
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) =>
        (g.app (Opposite.op (SimplexCategory.mk (0 + q))))
          ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
              (Work.SSSR.KunnethEZ.zSh q).2)) τ)) (Work.SSSR.vertIncl_snd p b 0)
    exact hh

/-- **The induced chain map on a generator.**  The `(0 + q)`-th component of the chain map induced
by `vertIncl p b 0`, evaluated on the generator attached to `Y.map (bHom zSh).op τ`, is the
generator attached to the image simplex `(vertIncl p b 0).app _ τ`. -/
lemma sCCMap_vertIncl_ιChainComplex {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (q : ℕ)
    (τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q))) :
    (Work.SSSR.sCCMap R (Work.SSSR.vertIncl p b 0)).f (0 + q)
        (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R)
          ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
              (Work.SSSR.KunnethEZ.zSh q).2)) τ)).hom 1)
      = (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R)
        ((Work.SSSR.vertIncl p b 0).app (Opposite.op (SimplexCategory.mk (0 + q)))
          ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
              (Work.SSSR.KunnethEZ.zSh q).2)) τ))).hom 1 :=
  congrArg (fun (g : ModuleCat.of R R ⟶
      (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).chainComplex (ModuleCat.of R R)).X (0 + q)) =>
      g.hom (1 : R))
    (SSet.ι_chainComplexMap_f (X := Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      (Y := ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))
      (f := Work.SSSR.vertIncl p b 0) (R := ModuleCat.of R R)
      ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
        (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
          (Work.SSSR.KunnethEZ.zSh q).2)) τ))

/-- The Eilenberg–Zilber shuffle chain, in degree `0 + q`, of the fundamental `0`-simplex of `Δ[0]` and a `q`-simplex `τ` of the fibre `F_b` is the image of the chain `τ` under the inclusion `Sing F_b ⟶ Δ[0] ⊗ Sing F_b` at the vertex `v₀`; the `(0+q)`-simplex indexing `ιChainComplex` on the right is the `(0,q)`-shuffle reindexing of `τ`. -/
theorem ezGen_zero_eq_vertIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (b : B) (q : ℕ)
    (τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q))) :
    Work.SSSR.Cohomology.Crux33.ezGen 0 q
        (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) τ
      = (Work.SSSR.sCCMap R (Work.SSSR.vertIncl p b 0)).f (0 + q)
          (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R)
            ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
              (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
                (Work.SSSR.KunnethEZ.zSh q).2)) τ)).hom 1) := by
  rw [Work.SSSR.KunnethEZ.ezGen_zero_single, sCCMap_vertIncl_ιChainComplex,
    vertIncl_app_bHom]
  rfl

end

end Work.SSSR.SZero
