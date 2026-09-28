import Mathlib
import Submission.Work.SSS.SZero.Defs
import Submission.Work.SSS.serreE1EZ
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.KunnethEZ.EZGenX

/-!
# The `(0,q)`-shuffle chain of the fundamental `0`-simplex

The Eilenberg–Zilber shuffle chain of the fundamental `0`-simplex `[id_0]` of `Δ[0]` and a
`q`-simplex `τ` of a simplicial set `Y` consists of a single shuffle summand (`(0,q)`-shuffles are
unique, `Work.KunnethEZ.ezGen_zero_single`), namely the generator of `Δ[0] ⊗ Y` attached to the pair

  `(Δ[0].map (aHom zSh).op [id₀], Y.map (bHom zSh).op τ)`.

That pair is exactly the value of the vertical inclusion
`Work.SSS.vertIncl p b 0 : Sing F_b ⟶ Δ[0] ⊗ Sing F_b`, `τ ↦ (v₀, τ)`, on `Y.map (bHom zSh).op τ`:
the first coordinate of a simplex of `Δ[0]` in degree `0 + q` is forced by `Δ[0]` being the
terminal simplicial set, and the second coordinate is read off from `Work.SSS.vertIncl_snd`.
The main theorem `Work.SSS.SZero.ezGen_zero_eq_vertIncl` is the resulting evaluation identity.
-/

set_option autoImplicit false

namespace Work.SSS.SZero

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
`Work.SSS.vertIncl_snd`. -/
lemma vertIncl_app_bHom {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (b : B) (q : ℕ)
    (τ : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q))) :
    (Work.SSS.vertIncl p b 0).app (Opposite.op (SimplexCategory.mk (0 + q)))
        ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
          (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
            (Work.KunnethEZ.zSh q).2)) τ)
      = ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).map
            (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh q).1
              (Work.KunnethEZ.zSh q).2).op
            (Work.SSS.stdIdSimplex 0),
          (Work.SSS.sSing (Work.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
              (Work.KunnethEZ.zSh q).2)) τ) := by
  refine Prod.ext ?_ ?_
  · exact Subsingleton.elim _ _
  · have hh := congrArg (fun (g : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
        Work.SSS.sSing (Work.StemsB.fibre p b)) =>
        (g.app (Opposite.op (SimplexCategory.mk (0 + q))))
          ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
              (Work.KunnethEZ.zSh q).2)) τ)) (Work.SSS.vertIncl_snd p b 0)
    exact hh

/-- **The induced chain map on a generator.**  The `(0 + q)`-th component of the chain map induced
by `vertIncl p b 0`, evaluated on the generator attached to `Y.map (bHom zSh).op τ`, is the
generator attached to the image simplex `(vertIncl p b 0).app _ τ`. -/
lemma sCCMap_vertIncl_ιChainComplex {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (q : ℕ)
    (τ : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q))) :
    (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f (0 + q)
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
              (Work.KunnethEZ.zSh q).2)) τ)).hom 1)
      = (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
          Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((Work.SSS.vertIncl p b 0).app (Opposite.op (SimplexCategory.mk (0 + q)))
          ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
            (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
              (Work.KunnethEZ.zSh q).2)) τ))).hom 1 :=
  congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      (((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex (ModuleCat.of ℤ ℤ)).X (0 + q)) =>
      g.hom (1 : ℤ))
    (SSet.ι_chainComplexMap_f (X := Work.SSS.sSing (Work.StemsB.fibre p b))
      (Y := ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)))
      (f := Work.SSS.vertIncl p b 0) (R := ModuleCat.of ℤ ℤ)
      ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
        (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
          (Work.KunnethEZ.zSh q).2)) τ))

/-- The Eilenberg–Zilber shuffle chain, in degree `0 + q`, of the fundamental `0`-simplex of `Δ[0]` and a `q`-simplex `τ` of the fibre `F_b` is the image of the chain `τ` under the inclusion `Sing F_b ⟶ Δ[0] ⊗ Sing F_b` at the vertex `v₀`; the `(0+q)`-simplex indexing `ιChainComplex` on the right is the `(0,q)`-shuffle reindexing of `τ`. -/
theorem ezGen_zero_eq_vertIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (b : B) (q : ℕ)
    (τ : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q))) :
    Work.Cohomology.Crux33.ezGen 0 q
        (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex 0) τ
      = (Work.SSS.sCCMap (Work.SSS.vertIncl p b 0)).f (0 + q)
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
              (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
                (Work.KunnethEZ.zSh q).2)) τ)).hom 1) := by
  rw [Work.KunnethEZ.ezGen_zero_single, sCCMap_vertIncl_ιChainComplex,
    vertIncl_app_bHom]
  rfl

end

end Work.SSS.SZero
