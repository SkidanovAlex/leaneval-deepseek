import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaLift
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-- **The value of the chain-level lift on a generator.**  Precomposing the lift `capThetaLift'`
with the inclusion of the generator `w` of the `(s+K)`-chains of `T_σ` gives the inclusion of the
chosen lift `backLift' p σ w h` in the top-front case. -/
lemma fibreIncCapThetaLift_iota_top (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) (K : ℕ)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s+K⦌)
    (h : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)) :
    (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w ≫
        (Work.Pi6.MSSK.capThetaLift' R p σ K)
      = (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ)).ιChainComplex
            (R := ModuleCat.of R R) (backLift' p σ w h) := by
  classical
  rw [Work.Pi6.MSSK.capThetaLift']
  exact (Cofan.IsColimit.fac
    ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan
      (ModuleCat.of R R) (s+K))
    (fun w => if h : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)
      then (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ)).ιChainComplex
        (R := ModuleCat.of R R) (backLift' p σ w h)
      else 0) w).trans (dif_pos h)

/-- **The value of the chain-level lift on a generator, non-top-front case**: the lift kills every
simplex which is not top-front. -/
lemma fibreIncCapThetaLift_iota_bot (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) (K : ℕ)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s+K⦌)
    (h : ¬ IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)) :
    (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w ≫
        (Work.Pi6.MSSK.capThetaLift' R p σ K) = 0 := by
  classical
  rw [Work.Pi6.MSSK.capThetaLift']
  refine (Cofan.IsColimit.fac
    ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan
      (ModuleCat.of R R) (s+K))
    (fun w => if h : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)
      then (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (lastV s ≫ σ)).ιChainComplex
        (R := ModuleCat.of R R) (backLift' p σ w h)
      else 0) w).trans ?_
  exact dif_neg h

/-- `thetaVal` takes only the values `1` and `0`. -/
lemma fibreIncCapThetaLift_thetaVal_dichotomy (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (y : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    thetaVal R p σ y = 1 ∨ thetaVal R p σ y = 0 := by
  classical
  rw [Work.Pi6.MSSK.thetaVal]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fibreIncCapThetaLift (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) (K : ℕ)
    (x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + K)) :
    (Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f K
        (Work.Pi6.MSSK.capThetaLift' R p σ K x)
      = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) K x := by
  classical
  have hmain : Work.Pi6.MSSK.capThetaLift' R p σ K ≫
      (Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f K
      = Work.Cohomology.capHom R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) K := by
    apply SSet.chainComplex_hom_ext
    intro w
    by_cases h : IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)
    · -- top-front simplex: the lift lands on the back face
      rw [← Category.assoc, fibreIncCapThetaLift_iota_top R p σ K w h]
      rw [show (Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f K
          = (SSet.chainComplexMap (Work.Pi6.MSSK.fibreInc p σ) (ModuleCat.of R R)).f K
          from rfl]
      rw [SSet.ι_chainComplexMap_f, Work.Pi6.MSSK.backLift'_spec p σ w h,
        Work.Cohomology.ιChainComplex_capHom, Work.Pi6.MSSK.genEval_thetaTop]
      rw [(Work.Pi6.MSSK.thetaVal_frontFace_eq_one_iff R p σ (Nat.le_add_right s K) w).2 h]
      rw [show LinearMap.toSpanSingleton R R (1:R) = LinearMap.id by ext; simp,
        ModuleCat.ofHom_id, Category.id_comp]
    · -- non-top-front simplex: both sides vanish
      rw [← Category.assoc, fibreIncCapThetaLift_iota_bot R p σ K w h, zero_comp]
      rw [Work.Cohomology.ιChainComplex_capHom, Work.Pi6.MSSK.genEval_thetaTop]
      have hne : thetaVal R p σ (Work.Cohomology.frontFace
          (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s (s+K) (Nat.le_add_right s K) w) ≠ 1 :=
        fun hc => h ((Work.Pi6.MSSK.thetaVal_frontFace_eq_one_iff R p σ
          (Nat.le_add_right s K) w).mp hc)
      have h0 : thetaVal R p σ (Work.Cohomology.frontFace
          (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s (s+K) (Nat.le_add_right s K) w) = 0 :=
        (fibreIncCapThetaLift_thetaVal_dichotomy R p σ _).resolve_left hne
      rw [h0, show LinearMap.toSpanSingleton R R (0:R) = 0 by ext; simp, ModuleCat.ofHom_zero,
        zero_comp]
  have h2 := congrArg (fun g => (ConcreteCategory.hom g) x) hmain
  simpa only [Work.Cohomology.cap, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

end

end Work.Pi6.MSSK
