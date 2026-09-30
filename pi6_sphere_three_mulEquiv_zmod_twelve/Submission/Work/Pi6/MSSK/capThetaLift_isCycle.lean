import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaLift
import Submission.Work.Pi6.MSSK.fibreIncCapThetaLift
import Submission.Work.Pi6.MSSK.capThetaIsCycle
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

/-!
# `capThetaLift_isCycle`

The chain-level lift `capThetaLift'` of the cap product with `thetaTop` kills boundaries: if
`c` is a chain of `T_σ = Δ[s] ×_{Sing B} Sing E` whose boundary `dc` is the image of a chain `y`
of the boundary subcomplex `∂T_σ`, then `∂(capThetaLift' R p σ (m+1) c) = 0` in the chains of
`T_{σ(s)} = Δ[0] ×_{Sing B} Sing E`.

The proof is a cancellation: `fibreInc p σ : T_{σ(s)} ⟶ T_σ` is a monomorphism of simplicial
sets (`mono_fibreInc`), hence the induced map on chains is injective in every degree. Under it the
lift `capThetaLift' R p σ K c` goes to the cap product `thetaTop ⌢ c`
(`fibreIncCapThetaLift`), which is a cycle by `capThetaIsCycle`; naturality of the differential in
the induced chain map transports this back.
-/

/-- The differential of an induced chain map, elementwise: `d ((sCCMap R g).f i x) =
(sCCMap R g).f j (d x)`. -/
lemma sCCMap_d_apply (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (g : X ⟶ Y)
    (i j : ℕ) (x : (Work.SSSR.sCC R X).X i) :
    (Work.SSSR.sCC R Y).d i j ((Work.SSSR.sCCMap R g).f i x)
      = (Work.SSSR.sCCMap R g).f j ((Work.SSSR.sCC R X).d i j x) := by
  have h := congrArg (fun (g : (Work.SSSR.sCC R X).X i ⟶ (Work.SSSR.sCC R Y).X j) =>
      (ModuleCat.Hom.hom g) x) (HomologicalComplex.Hom.comm (Work.SSSR.sCCMap R g) i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The chain map induced by a monomorphism of simplicial sets is levelwise injective. -/
lemma sCCMap_injective (R : Type) [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : Mono f) (n : ℕ) : Function.Injective ⇑((Work.SSSR.sCCMap R f).f n) := by
  have h : Mono ((Work.SSSR.sCCMap R f).f n) := by
    rw [show (Work.SSSR.sCCMap R f).f n = (Work.SSSR.sChainMap R f).f n from rfl]
    rw [Work.SSSR.sChainMap_f R f n]
    exact Work.SSSR.mono_sigma_map'_of_injective R _ (Work.SSSR.injective_app_of_mono f hf n)
  exact (ModuleCat.mono_iff_injective ((Work.SSSR.sCCMap R f).f n)).mp h

theorem capThetaLift_isCycle (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s m : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + (m+1)))
    (y : (Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).X (s + m))
    (hy : (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (s + m) y
        = ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s + (m+1)) (s + m)).hom c) :
    ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).d (m+1) m).hom
      (Work.Pi6.MSSK.capThetaLift' R p σ (m+1) c) = 0 := by
  -- `fibreInc` is a mono, so the induced chain map is injective in degree `m`; it suffices to
  -- check the vanishing after applying it.
  have hinj : Function.Injective ⇑((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f m) :=
    sCCMap_injective R (Work.Pi6.MSSK.fibreInc p σ) (Work.Pi6.MSSK.mono_fibreInc p σ) m
  refine hinj (show (Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f m
      ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (Work.Pi6.MSSK.lastV s ≫ σ))).d (m+1) m
        (Work.Pi6.MSSK.capThetaLift' R p σ (m+1) c))
    = (Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f m 0 from ?_)
  -- naturality of the differential, then `fibreIncCapThetaLift` and `capThetaIsCycle`.
  rw [← sCCMap_d_apply R (Work.Pi6.MSSK.fibreInc p σ) (m+1) m
    (Work.Pi6.MSSK.capThetaLift' R p σ (m+1) c)]
  rw [Work.Pi6.MSSK.fibreIncCapThetaLift R p σ (m+1) c]
  rw [Work.Pi6.MSSK.capThetaIsCycle R p σ c y hy, map_zero]

end

end Work.Pi6.MSSK
