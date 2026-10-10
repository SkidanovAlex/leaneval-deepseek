import Mathlib
import Submission.Work.MotV5.RigAS.PlaceData
import Submission.Work.MotV5.RigAS.kleinResidue
import Submission.Work.MotV5.RigAS.residueLiftUnstable
import Submission.Work.MotV5.RigAS.residueLiftGalois
import Submission.Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace Work.MotV5.RigAS

theorem residueLift_e1 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜) (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜) (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D) (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ))) (htriv : Work.MotV.TrivOn 𝕜 v) (ht : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)) (V : Valuation ↥(Work.MotV5.asFieldL D g) (WithZero (Multiplicative ℤ))) (hV : Work.MotV5.RigAS.IsPlaceExtension D g τ σS σ h v V) : Work.MotV5.RigAS.IsResidueLift D g τ σS σ h v V := by
  by_cases hstab : ∀ x : ↥(Work.MotV5.asFieldL D g),
      V (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h x) = V x
  · -- `σ'`-stable place: the Klein argument + the residue-field (Artin) step
    obtain ⟨z, hz1, hz2⟩ :=
      klein_residueAction_nontrivial D hD g τ σS σ h v V htriv hV hstab
    have hFL : Work.MotV5.asTwistFieldTrue D g τ σS ≤ Work.MotV5.asFieldL D g :=
      Work.MotV5.asTwistFieldTrue_le_asFieldL D g τ σS
    letI : Algebra ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) :=
      ((Subfield.inclusion hFL :
          ↥((Work.MotV5.asTwistFieldTrue D g τ σS).toSubfield) →+*
            ↥((Work.MotV5.asFieldL D g).toSubfield))).toAlgebra
    have halg : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
        algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x
          = Work.MotV5.RigAS.twistIncl D g τ σS x :=
      fun _ => Subtype.ext rfl
    have hfr : (Work.MotV5.asTwistFieldTrue D g τ σS).relfinrank (Work.MotV5.asFieldL D g) = 5 :=
      (Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable 𝕜 D g τ σS h.h5L h.hneL
        h.hpres).1
    have hfin : Module.finrank ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
        ↥(Work.MotV5.asFieldL D g) = 5 := by
      have h2 : Module.finrank ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
          ↥(IntermediateField.extendScalars hFL) = 5 := by
        rw [← IntermediateField.relfinrank_eq_finrank_of_le hFL]
        exact hfr
      exact h2
    haveI : FiniteDimensional ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
        ↥(Work.MotV5.asFieldL D g) :=
      FiniteDimensional.of_finrank_pos (by rw [hfin]; norm_num)
    have hσfix : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
        Work.MotV5.RigAS.twistSigmaL D g τ σS σ h
            (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x)
          = algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x := by
      intro x
      rw [halg x]
      have hx := Work.MotV5.asTwistFieldTrue_le_asTwistFieldFix D g τ σS x.2
      rw [Work.MotV5.asTwistFieldFix, IntermediateField.mem_fixedField_iff] at hx
      have h2 : Work.MotV5.asTwistAction D τ σS (x : Work.MotV.Om D) = (x : Work.MotV.Om D) := by
        have h3 := hx (Work.MotV5.asTwistAction D τ σS) (Subgroup.mem_zpowers _)
        simpa [AlgEquiv.smul_def] using h3
      apply Subtype.ext
      show Work.MotV5.asTwistAction D τ σS (x : Work.MotV.Om D) = (x : Work.MotV.Om D)
      exact h2
    have hσ5 : ∀ x : ↥(Work.MotV5.asFieldL D g),
        (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h ^ 5) x = x := by
      have h5eq : (restrictRingEquiv (Work.MotV5.asFieldL D g) (Work.MotV5.asTwistAction D τ σS)
          h.hpres h.h5L) ^ 5 = 1 :=
        restrictRingEquiv_pow_five_eq_one _ _ h.hpres h.h5L
      intro x
      rw [show Work.MotV5.RigAS.twistSigmaL D g τ σS σ h
          = restrictRingEquiv (Work.MotV5.asFieldL D g) (Work.MotV5.asTwistAction D τ σS)
              h.hpres h.h5L from rfl, h5eq]
      rfl
    have hres := residueLiftGalois (F := ↥(Work.MotV5.asTwistFieldTrue D g τ σS))
      (L := ↥(Work.MotV5.asFieldL D g))
      v V (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h) hσfix hstab hσ5 ⟨z, hz1, hz2⟩ hfin
      (by intro x; rw [halg x]; exact hV.1 x)
    intro x hx hx2
    obtain ⟨y, hy⟩ := hres x hx hx2
    exact ⟨y, by rw [← halg y]; exact hy⟩
  · -- non-`σ'`-stable place: the place is not unique, hence the residue degree is `1`
    exact residueLiftUnstable 𝕜 D hD g hg τ σS σ h v htriv ht V hV hstab

end Work.MotV5.RigAS
