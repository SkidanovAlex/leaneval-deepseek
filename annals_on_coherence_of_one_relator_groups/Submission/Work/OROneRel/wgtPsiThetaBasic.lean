import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

/-!
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The weighted maps `wTheta` and `wPsi`: basic computation rules

Elementary computation rules for the weighted Magnus--Moldavanskii maps
`Work.OROneRel.wTheta` and `Work.OROneRel.wPsi` defined in `wgtMMDefs`, together with the two
composition identities showing that `wTheta` and `wPsi` are mutually inverse for *any* choice of
the compatibility hypothesis `hcompat`.  (The existence of a compatible `hcompat` is the content of
`Work.OROneRel.wgtBaseHomCompat`.)

* `wgc_wA_eq_closure`, `wgc_wB_eq_closure` -- the associated subgroups are the closures of the
  images of `wTA`, resp. `wTB`;
* `wgc_wPsi_of`, `wgc_wPsi_t` -- the values of `wPsi` on the HNN generators
  (`HNNExtension.lift_of`, `HNNExtension.lift_t`);
* `wgc_wTheta_of` -- the values of `wTheta` on the generators of `⟨α | u⟩`
  (`PresentedGroup.toGroup.of`);
* `wgc_wThetaFun_t`, `wgc_wThetaFun_ne` -- the two cases of the auxiliary function `wThetaFun`;
* `wgc_wPsi_comp_wTheta`, `wgc_wTheta_comp_wPsi` -- the two compositions.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

section Basic

variable {c : α → ℤ} {t : α} {u : FreeGroup α}

theorem wgc_wA_eq_closure [DecidableEq α] :
    wA c t u =
      Subgroup.closure (Set.range fun e : wTA c t u => PresentedGroup.of (e : wBeta c t u)) :=
  rfl

theorem wgc_wB_eq_closure [DecidableEq α] :
    wB c t u =
      Subgroup.closure (Set.range fun e : wTB c t u => PresentedGroup.of (e : wBeta c t u)) :=
  rfl

theorem wgc_wPsi_of [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hcompat : wCompatHyp c t u hct hu hFw hc hA hB) (g : wH c t u) :
    wPsi c t u hct hu hFw hc hA hB hcompat (HNNExtension.of g) = wBaseHom hct hu g :=
  HNNExtension.lift_of _ _ _ g

theorem wgc_wPsi_t [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hcompat : wCompatHyp c t u hct hu hFw hc hA hB) :
    wPsi c t u hct hu hFw hc hA hB hcompat (HNNExtension.t : wK c t u hFw hc hA hB) =
      (PresentedGroup.of t : wG u) :=
  HNNExtension.lift_t _ _ _

theorem wgc_wTheta_of [DecidableEq α]
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hrel : FreeGroup.lift (wThetaFun c t u hFw hc hA hB) u = 1) (y : α) :
    wTheta c t u hFw hc hA hB hrel (PresentedGroup.of y) =
      wThetaFun c t u hFw hc hA hB y := by
  rw [wTheta, PresentedGroup.toGroup.of]

theorem wgc_wThetaFun_t [DecidableEq α]
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u)) :
    wThetaFun c t u hFw hc hA hB t = (HNNExtension.t : wK c t u hFw hc hA hB) := by
  rw [wThetaFun, dif_pos rfl]

theorem wgc_wThetaFun_ne [DecidableEq α]
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    {y : α} (hy : y ≠ t) :
    wThetaFun c t u hFw hc hA hB y =
      (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(wLo c t u ⟨y, hy⟩)) *
        HNNExtension.of (PresentedGroup.of
          (wBetaOf c t u ((⟨y, hy⟩, wLo c t u ⟨y, hy⟩) : WgtBeta t))) *
        (HNNExtension.t : wK c t u hFw hc hA hB) ^ (wLo c t u ⟨y, hy⟩ + c y) := by
  rw [wThetaFun, dif_neg hy]

/-- `wPsi` followed by `wTheta` is the identity, for any compatible `hcompat`. -/
theorem wgc_wPsi_comp_wTheta [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hcompat : wCompatHyp c t u hct hu hFw hc hA hB)
    (hrel : FreeGroup.lift (wThetaFun c t u hFw hc hA hB) u = 1) :
    (wPsi c t u hct hu hFw hc hA hB hcompat).comp (wTheta c t u hFw hc hA hB hrel) =
      MonoidHom.id (wG u) := by
  refine PresentedGroup.ext fun y => ?_
  show wPsi c t u hct hu hFw hc hA hB hcompat
      (wTheta c t u hFw hc hA hB hrel (PresentedGroup.of y)) = PresentedGroup.of y
  rw [wgc_wTheta_of]
  by_cases hy : y = t
  · subst hy
    rw [wgc_wThetaFun_t, wgc_wPsi_t]
  · rw [wgc_wThetaFun_ne hFw hc hA hB hy, map_mul, map_mul, map_zpow, map_zpow, wgc_wPsi_of,
      wgc_wPsi_t, wBaseHom_gen]
    rw [wBetaOf_val c t u (wLo_mem_decSet c t u ⟨y, hy⟩)]
    group

/-- `wTheta` followed by `wPsi` is the identity, for any compatible `hcompat` and any chain
hypothesis. -/
theorem wgc_wTheta_comp_wPsi [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hcompat : wCompatHyp c t u hct hu hFw hc hA hB)
    (hrel : FreeGroup.lift (wThetaFun c t u hFw hc hA hB) u = 1)
    (hchain : wChainHyp c t u hFw hc hA hB) :
    (wTheta c t u hFw hc hA hB hrel).comp (wPsi c t u hct hu hFw hc hA hB hcompat) =
      MonoidHom.id (wK c t u hFw hc hA hB) := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine PresentedGroup.ext fun p => ?_
    show wTheta c t u hFw hc hA hB hrel (wPsi c t u hct hu hFw hc hA hB hcompat
        (HNNExtension.of (PresentedGroup.of p))) = HNNExtension.of (PresentedGroup.of p)
    rw [wgc_wPsi_of, wBaseHom_gen, map_mul, map_mul, map_zpow, map_zpow, wgc_wTheta_of,
      wgc_wTheta_of]
    rw [wgc_wThetaFun_ne hFw hc hA hB p.1.1.2, wgc_wThetaFun_t]
    rw [show (⟨(p.1.1 : α), p.1.1.2⟩ : {x : α // x ≠ t}) = p.1.1 from Subtype.ext rfl]
    set lo := wLo c t u p.1.1 with hlo
    have hlo_le : lo ≤ p.1.2 := by rw [hlo]; exact p.2.1
    have hle_hi : p.1.2 ≤ wHi c t u p.1.1 := p.2.2
    have hm : 0 ≤ p.1.2 - lo := by linarith
    have hm' : (((p.1.2 - lo).toNat : ℕ) : ℤ) = p.1.2 - lo := Int.toNat_of_nonneg hm
    have hchain' := hchain p.1.1 lo (by rw [hlo]; exact wLo_mem_decSet c t u p.1.1)
      ((p.1.2 - lo).toNat) (fun s hs => by
        have hs' : (s : ℤ) < p.1.2 - lo := by
          have h2 : (s : ℤ) < ((((p.1.2 - lo).toNat : ℕ)) : ℤ) := by
            rw [Nat.cast_lt]; exact hs
          rwa [hm'] at h2
        refine ⟨?_, ?_⟩
        · show wLo c t u p.1.1 ≤ lo + (s : ℤ) + 1
          omega
        · show lo + (s : ℤ) + 1 ≤ wHi c t u p.1.1
          omega)
    have hL : (HNNExtension.t : wK c t u hFw hc hA hB) ^ (p.1.2) *
        ((HNNExtension.t : wK c t u hFw hc hA hB) ^ (-lo) *
          HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((p.1.1, lo) : WgtBeta t))) *
          (HNNExtension.t : wK c t u hFw hc hA hB) ^ (lo + c (p.1.1 : α))) *
        (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(p.1.2) - c (p.1.1 : α)) =
        (HNNExtension.t : wK c t u hFw hc hA hB) ^ (((p.1.2 - lo).toNat : ℕ) : ℤ) *
          HNNExtension.of (PresentedGroup.of (wBetaOf c t u ((p.1.1, lo) : WgtBeta t))) *
          (HNNExtension.t : wK c t u hFw hc hA hB) ^ (-(((p.1.2 - lo).toNat : ℕ) : ℤ)) := by
      rw [hm']
      group
    rw [hL, hchain']
    refine congrArg HNNExtension.of (congrArg PresentedGroup.of ?_)
    have hpt : ((p.1.1, lo + ((p.1.2 - lo).toNat : ℕ)) : WgtBeta t) = p.1 := by
      refine Prod.ext rfl ?_
      rw [hm']
      ring
    rw [hpt]
    exact Subtype.ext (wBetaOf_val c t u p.2)
  · rw [MonoidHom.comp_apply, MonoidHom.id_apply, wgc_wPsi_t, wgc_wTheta_of, wgc_wThetaFun_t]

end Basic

section Compat

variable {c : α → ℤ} {t : α} {u : FreeGroup α}

/-- The value of `wBaseHom` on the image under `wPhi` of the generator of `wA` attached to a symbol
of `wTA`: the conjugate of the shifted symbol. -/
theorem wgc_wBaseHom_wPhiGA [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hphi : wPhiOfHyp c t u hFw hc hA hB) (e : wTA c t u) :
    wBaseHom hct hu ((wPhi hFw hc hA hB (wGA e) : wB c t u) : wH c t u)
      = (PresentedGroup.of t : wG u) ^ ((e : wBeta c t u).1.2 + 1) *
        PresentedGroup.of (((e : wBeta c t u).1.1 : α)) *
        (PresentedGroup.of t : wG u) ^
          (-((e : wBeta c t u).1.2 + 1) - c ((e : wBeta c t u).1.1 : α)) := by
  rw [show ((wPhi hFw hc hA hB (wGA e) : wB c t u) : wH c t u)
      = PresentedGroup.of (wBetaOf c t u
          (((e : wBeta c t u).1.1, (e : wBeta c t u).1.2 + 1) : WgtBeta t)) from
    hphi (e : wBeta c t u) (Subgroup.subset_closure ⟨e, rfl⟩) e.2,
    wBaseHom_gen]
  rw [wBetaOf_val c t u (show (((e : wBeta c t u).1.1, (e : wBeta c t u).1.2 + 1) : WgtBeta t)
      ∈ wDecSet c t u from e.2)]

/-- The base map `wBaseHom` is compatible with the HNN relation of `wK`: this is the
`hcompat` that `wPsi` needs. -/
theorem wgc_wBaseHom_compat [DecidableEq α] (hct : c t = 1) (hu : cohom c u = 1)
    (hFw : FreiheitssatzAt (wW c t u)) (hc : IsCyclicallyReducedRelator (wW c t u))
    (hA : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTA c t u))
    (hB : (wW c t u) ∉ Subgroup.closure (FreeGroup.of '' wTB c t u))
    (hphi : wPhiOfHyp c t u hFw hc hA hB) :
    wCompatHyp c t u hct hu hFw hc hA hB := by
  intro a
  refine Subgroup.closure_induction
    (p := fun y hy => (PresentedGroup.of t : wG u) * wBaseHom hct hu y
      = wBaseHom hct hu
          ((wPhi hFw hc hA hB
              (⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u) : wB c t u) : wH c t u) *
          (PresentedGroup.of t : wG u)) ?_ ?_ ?_ ?_ a.2
  · rintro y ⟨e, rfl⟩
    dsimp only
    rw [show (⟨PresentedGroup.of (e : wBeta c t u), _⟩ : wA c t u) = wGA e from Subtype.ext rfl,
      wgc_wBaseHom_wPhiGA hct hu hFw hc hA hB hphi e, wBaseHom_gen]
    group
  · rw [show (⟨1, by rw [wgc_wA_eq_closure]; exact Subgroup.one_mem _⟩ : wA c t u) = 1 from
        Subtype.ext rfl, MulEquiv.map_one (wPhi hFw hc hA hB),
      show (((1 : wB c t u)) : wH c t u) = 1 from rfl, map_one, mul_one, one_mul]
  · rintro y z hy hz ihy ihz
    have hE : (⟨y * z, by rw [wgc_wA_eq_closure]; exact Subgroup.mul_mem _ hy hz⟩ : wA c t u)
        = (⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u) *
          (⟨z, by rw [wgc_wA_eq_closure]; exact hz⟩ : wA c t u) := Subtype.ext rfl
    have hφ : ((wPhi hFw hc hA hB
          ((⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u) *
            (⟨z, by rw [wgc_wA_eq_closure]; exact hz⟩ : wA c t u)) : wB c t u) : wH c t u)
        = ((wPhi hFw hc hA hB
              (⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u) : wB c t u) : wH c t u) *
          ((wPhi hFw hc hA hB
              (⟨z, by rw [wgc_wA_eq_closure]; exact hz⟩ : wA c t u) : wB c t u) : wH c t u) := by
      rw [map_mul]; rfl
    rw [hE, hφ, map_mul, ← mul_assoc, ihy, mul_assoc, ihz, map_mul]
    group
  · rintro y hy ihy
    have hE : (⟨y⁻¹, by rw [wgc_wA_eq_closure]; exact Subgroup.inv_mem _ hy⟩ : wA c t u)
        = (⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u)⁻¹ := Subtype.ext rfl
    have hφ : ((wPhi hFw hc hA hB
          ((⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u)⁻¹) : wB c t u) : wH c t u)
        = (((wPhi hFw hc hA hB
              (⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u) : wB c t u) : wH c t u))⁻¹ := by
      rw [map_inv]; rfl
    rw [hE, hφ, map_inv (wBaseHom hct hu) y]
    have hY : wBaseHom hct hu y
        = (PresentedGroup.of t : wG u)⁻¹ *
            ((wBaseHom hct hu ((wPhi hFw hc hA hB
                (⟨y, by rw [wgc_wA_eq_closure]; exact hy⟩ : wA c t u) : wB c t u) : wH c t u)) *
              (PresentedGroup.of t : wG u)) := by
      rw [← ihy]; group
    rw [hY, map_inv]
    group

end Compat

end Work.OROneRel
