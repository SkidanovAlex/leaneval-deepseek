import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

namespace Work.OROneRel

universe u

/-! ## Values of `wThetaFun`

The weighted Magnus map `wThetaFun` is defined by a case split on whether the letter is `t`.  The
two lemmas below expose its two branches, exactly as `mmThetaFun_t` / `mmThetaFun_ne` do in the
classical (exponent-sum-zero) Magnus rewriting. -/

theorem wThetaFun_t {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) :
    wThetaFun c t u hFw hc hA hB t = (HNNExtension.t : wK c t u hFw hc hA hB) := by
  rw [wThetaFun]
  rw [dif_pos rfl]

theorem wThetaFun_ne {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) {y : α} (hy : y ≠ t) :
    wThetaFun c t u hFw hc hA hB y =
      (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(wLo c t u ⟨y, hy⟩)) *
      HNNExtension.of (PresentedGroup.of
        (wBetaOf c t u ((⟨y, hy⟩, wLo c t u ⟨y, hy⟩) : WgtBeta t))) *
      (HNNExtension.t : wK c t u hFw hc hA hB) ^ (wLo c t u ⟨y, hy⟩ + c y) := by
  rw [wThetaFun]
  rw [dif_neg hy]

/-! ## The key computation

The image under `FreeGroup.lift wThetaFun` of the conjugate `t ^ k * x * t ^ (-k - c x)` attached to
a symbol `(x,k)` of the decorated alphabet (for `(x,k)` in the interval closure of the occurring
weights) is the corresponding generator of the base group.  This is the weighted counterpart of the
verification of `mmThetaFun` on the rewritten generators; the iterated conjugation is supplied by
`wChainHyp`. -/

theorem wTheta_lift_wrho_of {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hchain : wChainHyp c t u hFw hc hA hB)
    (p : WgtBeta t) (hp : p ∈ wDecSet c t u) :
    (FreeGroup.lift (wThetaFun c t u hFw hc hA hB)) ((wrho t c) (FreeGroup.of p))
      = HNNExtension.of (PresentedGroup.of (wBetaOf c t u p)) := by
  classical
  have hkx : wLo c t u p.1 ≤ p.2 := hp.1
  have hkx2 : p.2 ≤ wHi c t u p.1 := hp.2
  have hstep : ∀ s : ℕ, s < (p.2 - wLo c t u p.1).toNat →
      ((p.1, wLo c t u p.1 + (s : ℤ) + 1) : WgtBeta t) ∈ wDecSet c t u := by
    intro s hs
    have h2 : ((s : ℤ)) < (((p.2 - wLo c t u p.1).toNat : ℕ) : ℤ) := by exact_mod_cast hs
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ p.2 - wLo c t u p.1)] at h2
    show wLo c t u p.1 ≤ wLo c t u p.1 + (s : ℤ) + 1 ∧
      wLo c t u p.1 + (s : ℤ) + 1 ≤ wHi c t u p.1
    constructor <;> omega
  have hchain' := hchain p.1 (wLo c t u p.1) (wLo_mem_decSet c t u p.1)
      ((p.2 - wLo c t u p.1).toNat) hstep
  have hsum : wLo c t u p.1 + ((((p.2 - wLo c t u p.1).toNat : ℕ) : ℤ)) = p.2 := by
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ p.2 - wLo c t u p.1)]
    ring
  rw [hsum] at hchain'
  rw [wrho_of, map_mul, map_mul, map_zpow, map_zpow]
  simp only [FreeGroup.lift_apply_of]
  rw [wThetaFun_t c t u hFw hc hA hB, wThetaFun_ne c t u hFw hc hA hB p.1.2]
  rw [show (HNNExtension.t : wK c t u hFw hc hA hB) ^ p.2 *
        ((HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(wLo c t u p.1)) *
          HNNExtension.of (PresentedGroup.of
            (wBetaOf c t u ((p.1, wLo c t u p.1) : WgtBeta t))) *
          (HNNExtension.t : wK c t u hFw hc hA hB) ^ (wLo c t u p.1 + c (p.1 : α))) *
        (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-p.2 - c (p.1 : α))
      = (HNNExtension.t : wK c t u hFw hc hA hB) ^ ((((p.2 - wLo c t u p.1).toNat : ℕ) : ℤ)) *
          HNNExtension.of (PresentedGroup.of
            (wBetaOf c t u ((p.1, wLo c t u p.1) : WgtBeta t))) *
          (HNNExtension.t : wK c t u hFw hc hA hB) ^
            (-((((p.2 - wLo c t u p.1).toNat : ℕ) : ℤ))) from by
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ p.2 - wLo c t u p.1)]
    group]
  rw [hchain']

/-! ## The two facts -/

/-- **The iterated conjugation along the `wTheta` image.**  The class of the expansion of any word
`v` over the base alphabet is the base class of `v` itself. -/
theorem wTheta_lift_wrho_map {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hchain : wChainHyp c t u hFw hc hA hB) (v : FreeGroup (wBeta c t u)) :
    (FreeGroup.lift (wThetaFun c t u hFw hc hA hB))
        ((wrho t c) (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) v))
      = HNNExtension.of (PresentedGroup.mk ({wW c t u} : Set (FreeGroup (wBeta c t u))) v) := by
  have hcomp : (FreeGroup.lift (wThetaFun c t u hFw hc hA hB)).comp
        ((wrho t c).comp (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t))))
      = (HNNExtension.of).comp
          (PresentedGroup.mk ({wW c t u} : Set (FreeGroup (wBeta c t u)))) := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, FreeGroup.map.of]
    have hbe : (PresentedGroup.of (wBetaOf c t u (e.1 : WgtBeta t)) : wH c t u)
        = (PresentedGroup.mk ({wW c t u} : Set (FreeGroup (wBeta c t u)))) (FreeGroup.of e) := by
      rw [show wBetaOf c t u (e.1 : WgtBeta t) = e from
        Subtype.ext (wBetaOf_val c t u e.2)]
      rfl
    exact (wTheta_lift_wrho_of c t u hFw hc hA hB hchain (e.1 : WgtBeta t) e.2).trans
      (congrArg HNNExtension.of hbe)
  exact congrArg (fun f : FreeGroup (wBeta c t u) →* wK c t u hFw hc hA hB => f v) hcomp

/-- **The relator is killed.**  The `wThetaFun`-image of the defining relator `u` is trivial in the
HNN extension, so that `wThetaFun` factors through `⟨α | u⟩`. -/
theorem wThetaFun_relator {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hchain : wChainHyp c t u hFw hc hA hB) (hct : c t = 1) (hcu : cohom c u = 1) :
    FreeGroup.lift (wThetaFun c t u hFw hc hA hB) u = 1 := by
  classical
  set Θ : FreeGroup (WgtBeta t) →* wK c t u hFw hc hA hB :=
    (FreeGroup.lift (wThetaFun c t u hFw hc hA hB)).comp (wrho t c) with hΘ
  have hΘlift : Θ = FreeGroup.lift (fun p : WgtBeta t => Θ (FreeGroup.of p)) := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    rw [FreeGroup.lift_apply_of]
  have hval : ∀ p : WgtBeta t × Bool, p ∈ wvListAux c t 0 (wordOf u) →
      Θ (FreeGroup.of p.1) = HNNExtension.of (PresentedGroup.of (wBetaOf c t u p.1)) := by
    intro p hp
    exact wTheta_lift_wrho_of c t u hFw hc hA hB hchain p.1 (wList_mem_decSet c t u hp)
  have hL : Θ (FreeGroup.mk (wvListAux c t 0 (wordOf u)))
      = FreeGroup.lift (fun p : WgtBeta t =>
          HNNExtension.of (PresentedGroup.of (wBetaOf c t u p)))
          (FreeGroup.mk (wvListAux c t 0 (wordOf u))) := by
    rw [hΘlift, FreeGroup.lift_mk, FreeGroup.lift_mk]
    refine congrArg List.prod (List.map_congr_left ?_)
    intro x hx
    rw [hval x hx]
  have hG0 : FreeGroup.lift (fun p : WgtBeta t =>
        HNNExtension.of (PresentedGroup.of (wBetaOf c t u p)))
      = (HNNExtension.of : wH c t u →* wK c t u hFw hc hA hB).comp
          ((PresentedGroup.mk ({wW c t u} : Set (FreeGroup (wBeta c t u)))).comp
            (FreeGroup.map (wBetaOf c t u))) := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.map.of]
    rfl
  have hmain : Θ (FreeGroup.mk (wvListAux c t 0 (wordOf u))) = 1 := by
    rw [hL, hG0, MonoidHom.comp_apply, MonoidHom.comp_apply, FreeGroup.map.mk]
    rw [show (wvListAux c t 0 (wordOf u)).map
          (fun p => (wBetaOf c t u p.1, p.2)) = wWL c t u from rfl]
    rw [show FreeGroup.mk (wWL c t u) = wW c t u from rfl]
    rw [PresentedGroup.one_of_mem (Set.mem_singleton _), map_one]
  calc (FreeGroup.lift (wThetaFun c t u hFw hc hA hB)) u
      = (FreeGroup.lift (wThetaFun c t u hFw hc hA hB))
          ((wrho t c) (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (wW c t u))) := by
        rw [wrho_wW c t u hct hcu]
    _ = Θ (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (wW c t u)) := rfl
    _ = Θ (FreeGroup.mk (wvListAux c t 0 (wordOf u))) := by rw [wW_map_val]
    _ = 1 := hmain

theorem wgtThetaFacts {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hct : c t = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hFw : Work.OROneRel.FreiheitssatzAt (Work.OROneRel.wW c t u))
    (hc : Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.wW c t u))
    (hA : Work.OROneRel.wW c t u ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTA c t u))
    (hB : Work.OROneRel.wW c t u ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTB c t u))
    (hchain : Work.OROneRel.wChainHyp c t u hFw hc hA hB) :
    (FreeGroup.lift (Work.OROneRel.wThetaFun c t u hFw hc hA hB) u = 1) ∧
      (∀ v : FreeGroup (Work.OROneRel.wBeta c t u),
        (FreeGroup.lift (Work.OROneRel.wThetaFun c t u hFw hc hA hB))
            (Work.OROneRel.wrho t c (FreeGroup.map (fun p : Work.OROneRel.wBeta c t u =>
              (p.1 : Work.OROneRel.WgtBeta t)) v))
          = HNNExtension.of (PresentedGroup.mk
              ({Work.OROneRel.wW c t u} : Set (FreeGroup (Work.OROneRel.wBeta c t u))) v)) :=
  ⟨wThetaFun_relator c t u hFw hc hA hB hchain hct hcu,
   fun v => wTheta_lift_wrho_map c t u hFw hc hA hB hchain v⟩

end Work.OROneRel
