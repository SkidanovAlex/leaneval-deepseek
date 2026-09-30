import Mathlib
import Submission.Work.Pi6.MSSK.Defs
import Submission.Work.Pi6.MSSK.altFacesSum
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `genEval` of `thetaTop` on an `s`-simplex of `T_σ` is its value `thetaVal`. -/
lemma thetaTop_genEval (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    Work.Cohomology.genEval R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (thetaTop R p σ) w = thetaVal R p σ w := by
  have key : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w
      ≫ ModuleCat.ofHom (thetaTop R p σ)
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R R (thetaVal R p σ w)) := by
    rw [thetaTop]
    exact Cofan.IsColimit.fac _ _ _
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom (1 : R)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2
  rw [Work.Cohomology.genEval]
  exact h2.trans (by simp)

theorem thetaTop_cocycle (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Cohomology.cochainDiff R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (Work.Pi6.MSSK.thetaTop R p σ) = 0 := by
  apply Work.Cohomology.genEval_ext
  intro w
  rw [Work.Cohomology.genEval_cochainDiff]
  have hzero : Work.Cohomology.genEval R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (0 : ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).chainComplex
        (ModuleCat.of R R)).X (s + 1) →ₗ[R] R) w = 0 := by
    simp [Work.Cohomology.genEval]
  rw [hzero]
  -- Each term of the alternating sum is the pull-back of the indicator of the top simplex.
  have hterm : ∀ i : Fin (s + 2),
      ((-1 : R) ^ (i : ℕ)) *
        Work.Cohomology.genEval R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ)
          ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w)
      = ((-1 : R) ^ (i : ℕ)) *
          (if CategoryTheory.SimplicialObject.δ
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i
                ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s + 1⦌) w)
              = Work.Pi6.MSSK.topS s then (1 : R) else 0) := by
    intro i
    have hnat : (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s⦌)
        ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w)
        = CategoryTheory.SimplicialObject.δ
            (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i
            ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s + 1⦌) w) :=
      SSet.δ_naturality_apply (pullback.fst σ (Work.SSSR.sSingP p)) i w
    rw [thetaTop_genEval]
    rw [thetaVal, hnat]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact altFacesSum R ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s + 1⦌) w)

end

end Work.Pi6.MSSK
