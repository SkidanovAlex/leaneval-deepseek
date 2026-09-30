import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.backFace_mem_fibre
import Submission.Work.Pi6.MSSK.mono_fibreInc
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The lift of a top-front simplex to the fibre over the last vertex** (chosen through the
child lemma `backFace_mem_fibre`). -/
def backLift' {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s + K⦌)
    (hα : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)) :
    (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ)) _⦋K⦌ :=
  Classical.choose (backFace_mem_fibre p σ w hα)

lemma backLift'_spec {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s + K⦌)
    (hα : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)) :
    (fibreInc p σ).app (op ⦋K⦌) (backLift' p σ w hα)
      = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w :=
  Classical.choose_spec (backFace_mem_fibre p σ w hα)

/-- **The chain-level lift of the cap product with `thetaTop`** (sorry-free version, built on
`backLift'`). -/
def capThetaLift' (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) (K : ℕ) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + K) ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ))).X K := by
  classical
  exact ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan
      (ModuleCat.of R R) (s + K)).desc
    (Cofan.mk ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ))).X K)
      (fun w => if h : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)
        then (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ)).ιChainComplex
          (R := ModuleCat.of R R) (backLift' p σ w h)
        else 0))


end

end Work.Pi6.MSSK
