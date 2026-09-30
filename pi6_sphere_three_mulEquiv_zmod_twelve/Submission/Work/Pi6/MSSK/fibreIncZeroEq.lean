import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.SSSR.iotaStatement_zero_c_one
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- **Canonical transports of pullbacks are compatible with `eqToHom`.**  If `h : g = g'` are two
morphisms `Y ⟶ Z` with the same target as `f : X ⟶ Z`, then the canonical isomorphism
`pullback g f ⟶ pullback g' f` induced by `h` (whose two components are the two projections of
`pullback g f`) is exactly the morphism `eqToHom (congrArg (fun t => pullback t f) h)` obtained by
transporting objects along `h`.  Both sides are proved to be the identity after `cases h`, using the
universal property of the pullback (`pullback.hom_ext`). -/
lemma pullback_lift_eqToHom_congrArg {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) {g g' : Y ⟶ Z} (h : g = g') :
    pullback.lift (pullback.fst g f) (pullback.snd g f)
        (by rw [← h]; exact pullback.condition)
      = eqToHom (congrArg (fun t => pullback t f) h) := by
  cases h
  rw [eqToHom_refl]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.id_comp]
  · rw [pullback.lift_snd, Category.id_comp]

/-- **In degree `0` the fibre inclusion is the identity**, i.e. `fibreInc p σ : T_{σ(0)} ⟶ T_σ` is
the canonical identification of the two `pullAlong` objects along the equality `lastV 0 ≫ σ = σ`.

Indeed `fibreInc` is the lift of the two projections of `T_{lastV 0 ≫ σ}` into `T_σ`, and for `s = 0`
the first projection may be composed with the endomorphism `lastV 0` of `Δ[0]`: since `Δ[0]` is a
terminal object of `SSet` (`SSet.stdSimplex.ext₀`), any two maps into it agree.  So `fibreInc` is the
*lift of the two projections themselves*, which the previous lemma identifies with the `eqToHom`
induced by `hσ`. -/
theorem fibreIncZeroEq {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (hσ : CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 0) σ = σ) :
    Work.Pi6.MSSK.fibreInc p σ
      = CategoryTheory.eqToHom (congrArg (fun τ => Work.SSSR.pullAlong (Work.SSSR.sSingP p) τ) hσ) := by
  have h1 : Work.Pi6.MSSK.fibreInc p σ
      = pullback.lift (pullback.fst (Work.Pi6.MSSK.lastV 0 ≫ σ) (Work.SSSR.sSingP p))
          (pullback.snd (Work.Pi6.MSSK.lastV 0 ≫ σ) (Work.SSSR.sSingP p))
          (by rw [← hσ]; exact pullback.condition) := by
    apply pullback.hom_ext
    · rw [Work.Pi6.MSSK.fibreInc, pullback.lift_fst, pullback.lift_fst]
      exact SSet.stdSimplex.ext₀
    · rw [Work.Pi6.MSSK.fibreInc, pullback.lift_snd, pullback.lift_snd]
  rw [h1]
  exact pullback_lift_eqToHom_congrArg (Work.SSSR.sSingP p) hσ

end

end Work.Pi6.MSSK
