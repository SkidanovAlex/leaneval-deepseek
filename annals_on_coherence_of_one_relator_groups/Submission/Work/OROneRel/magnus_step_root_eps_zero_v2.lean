import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.rho_magnet
import Submission.Work.OROneRel.rho_magRew
import Submission.Work.OROneRel.rho_injective
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.not_isProperPower_of
import Submission.Work.OROneRel.relatorLetters_pow_subset
import Submission.Work.OROneRel.le_relatorNorm_pow
import Submission.Work.OROneRel.EpsV2.Toolbox

namespace Work.OROneRel

universe u

/-- **The Magnus step, exponent-sum-zero case, with the root tracked up to conjugacy.**

Let `u : FreeGroup α` be cyclically reduced and not a proper power, let `t : α` be a letter of `u`
of vanishing exponent sum in `u`, and let `l ≥ 1`.  Then the one-relator group `⟨α | u ^ l⟩` is an
HNN extension of the shorter one-relator group `⟨β | v ^ l⟩` (same exponent `l`, the root `v` again
not a proper power and strictly shorter than `u`), and the class of `u` is *conjugate* to the class
of the root `v`.

The proof runs the exponent-sum-zero Magnus--Moldavanskii step
(`Submission.Work.OROneRel.mmStepData_of_expsum_zero`, which needs the Freiheitssatz
`Submission.Work.OROneRel.freiheitssatz_at`) at the *power* relator `u ^ l`, and then transports the
resulting HNN structure back to the root: the decorated alphabet of `u ^ l` agrees with that of `u`
and the Magnus rewriting of `u ^ l` is the `l`-th power of the rewriting of `u`
(`Submission.Work.OROneRel.EpsV2.Toolbox`).  The images of the generators under the
Magnus--Moldavanskii map are computed with `EpsV2.mmTheta_lift_mmRho`, which shows that the class of
`u` is the class of the root `of (mk v)` itself -- so the conjugating element `c` may be taken to
be `1`. -/
theorem magnus_step_root_eps_zero_v2 {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (t : α)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u)
    (he : Work.OROneRel.eps t u = 0) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  -- ## The relator `u ^ l`
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hcycw : FreeGroup.IsCyclicallyReduced u.toWord := by
    simpa only [IsCyclicallyReducedRelator] using hcyc
  have hcyc' : IsCyclicallyReducedRelator (u ^ l) := isCyclicallyReducedRelator_pow hcyc l
  have h1' : u ^ l ≠ 1 := by
    intro h
    have hle := le_relatorNorm_pow u l hu1
    rw [h] at hle
    simp [relatorNorm, FreeGroup.norm] at hle
    omega
  have htw : (u ^ l).toWord = (List.replicate l u.toWord).flatten := by
    rw [FreeGroup.toWord_pow, (hcycw.flatten_replicate l).1.reduce_eq]
  have ht' : t ∈ relatorLetters (u ^ l) := by
    obtain ⟨b, hb⟩ := ht
    refine ⟨b, ?_⟩
    rw [htw]
    exact List.mem_flatten.mpr ⟨u.toWord, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩
  have hes : sigma t u = 1 := (eps_eq_zero_iff_sigma_eq_one t u).mp he
  have he' : eps t (u ^ l) = 0 := by
    refine (eps_eq_zero_iff_sigma_eq_one t (u ^ l)).mpr ?_
    rw [map_pow, hes, one_pow]
  -- ## The Magnus--Moldavanskii step at the power relator
  have hFw : FreiheitssatzAt (mmW t (u ^ l)) := freiheitssatz_at _
  have hred : FreeGroup.IsReduced (mmWL t (u ^ l)) := mmWL_isReduced t (u ^ l) hcyc' he'
  have hc : IsCyclicallyReducedRelator (mmW t (u ^ l)) := mmW_isCyclicallyReduced hcyc' he'
  have hA' : mmW t (u ^ l) ∉ Subgroup.closure (FreeGroup.of '' mmTA t (u ^ l)) :=
    mmW_notMem_closure_TA h1' ht' he' hred
  have hB' : mmW t (u ^ l) ∉ Subgroup.closure (FreeGroup.of '' mmTB t (u ^ l)) :=
    mmW_notMem_closure_TB h1' ht' he' hred
  have hrel : FreeGroup.lift (mmThetaFun hFw hc hA' hB') (u ^ l) = 1 :=
    mmThetaFun_relator he' hFw hc hA' hB'
  have hC2 : (mmPsi he' hFw hc hA' hB').comp (mmTheta hFw hc hA' hB' hrel)
      = MonoidHom.id (mmG (u ^ l)) := mmPsi_comp_mmTheta he' hFw hc hA' hB' hrel
  have hC3 : (mmTheta hFw hc hA' hB' hrel).comp (mmPsi he' hFw hc hA' hB')
      = MonoidHom.id (mmK t (u ^ l) hFw hc hA' hB') := mmTheta_comp_mmPsi he' hFw hc hA' hB' hrel
  let e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃* mmK t (u ^ l) hFw hc hA' hB' :=
    (MonoidHom.toMulEquiv (mmPsi he' hFw hc hA' hB') (mmTheta hFw hc hA' hB' hrel) hC3 hC2).symm
  -- ## The root of the rewriting of `u ^ l`
  let v : FreeGroup (mmBeta t (u ^ l)) := EpsV2.rootW t u l hcyc he hl
  have hmw : mmW t (u ^ l) = v ^ l := (EpsV2.rootW_pow t u l hcyc he hl).symm
  have hnpv : ¬ IsProperPower v := EpsV2.not_isProperPower_rootW t u l hu hcyc he hl
  have hnorm : relatorNorm v < relatorNorm u := EpsV2.relatorNorm_rootW_lt t u l hcyc he hl ht
  -- ## The class of `u` is the class of the root
  have hcomp : (mmTheta hFw hc hA' hB' hrel).comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
      = FreeGroup.lift (mmThetaFun hFw hc hA' hB') := by
    refine FreeGroup.ext_hom _ _ fun y => ?_
    show mmTheta hFw hc hA' hB' hrel (PresentedGroup.of y)
        = FreeGroup.lift (mmThetaFun hFw hc hA' hB') (FreeGroup.of y)
    rw [FreeGroup.lift_apply_of]
    exact mmTheta_of hFw hc hA' hB' hrel y
  have hconj : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
      = HNNExtension.of (PresentedGroup.mk
          ({mmW t (u ^ l)} : Set (FreeGroup (mmBeta t (u ^ l)))) v) := by
    have h1 : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
        = (FreeGroup.lift (mmThetaFun hFw hc hA' hB')) u := by
      have h2 : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
          = mmTheta hFw hc hA' hB' hrel (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) := rfl
      rw [h2]
      exact congrArg (fun f => f u) hcomp
    have h3 : (FreeGroup.lift (mmThetaFun hFw hc hA' hB')) u
        = (FreeGroup.lift (mmThetaFun hFw hc hA' hB'))
            (FreeGroup.lift (fun p : mmBeta t (u ^ l) => EpsV2.mmRhoFun t p.1) v) :=
      congrArg (FreeGroup.lift (mmThetaFun hFw hc hA' hB'))
        (EpsV2.lift_mmRho_rootW t u l hcyc he hl).symm
    have h4 : (FreeGroup.lift (mmThetaFun hFw hc hA' hB'))
            (FreeGroup.lift (fun p : mmBeta t (u ^ l) => EpsV2.mmRhoFun t p.1) v)
        = HNNExtension.of (PresentedGroup.mk
            ({mmW t (u ^ l)} : Set (FreeGroup (mmBeta t (u ^ l)))) v) :=
      EpsV2.mmTheta_lift_mmRho hFw hc hA' hB' v
    exact h1.trans (h3.trans h4)
  -- ## Assembly
  refine ⟨mmBeta t (u ^ l), v, hnpv, hnorm, ?_⟩
  rw [← hmw]
  refine ⟨mmA t (u ^ l), mmB t (u ^ l), mmPhi hFw hc hA' hB', e, 1, ?_⟩
  simpa using hconj

end Work.OROneRel
