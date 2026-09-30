import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlModelDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# The two radial homotopies realising the homotopy equivalence of the overlap with the model pair

On the gluing region `ovlV = {x ≠ 0} × ℍ` of the two charts of `Vk (-2)` the radial homotopy
`(x, y) ↦ ((1-t) + t/‖x‖) • x` retracts the base onto the unit sphere and thereby realises
`pSi ∘ pS ~ id` (`vkOvlBaseHomotopy`); it preserves the sphere-bundle part `{‖y‖ = 1}` setwise.

On the model total space `S3H = S³ × ℍ` the fibrewise radial homotopy
`(s, y) ↦ (s, (t + (1-t)/max 1 ‖y‖) • y)` realises `PsiM ∘ PhiM ~ id` (`vkOvlFibreHomotopy`).
-/

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology
open scoped Topology unitInterval

noncomputable section



/-- value of the base homotopy -/
def vkOvlBaseHVal (z : I × ovlV) : Submission.Milnor.MSpace8 :=
  (((1 - (z.1 : ℝ)) * (‖(z.2 : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ + (z.1 : ℝ)) •
      (z.2 : Submission.Milnor.MSpace8).1, (z.2 : Submission.Milnor.MSpace8).2)

theorem vkOvlBaseHVal_mem (z : I × ovlV) : vkOvlBaseHVal z ∈ Submission.Milnor.vOpens := by
  rw [Submission.Milnor.mem_vOpens]
  have hx : (z.2 : Submission.Milnor.MSpace8).1 ≠ 0 :=
    Submission.Milnor.mem_vOpens.mp z.2.2
  have hxpos : 0 < ‖(z.2 : Submission.Milnor.MSpace8).1‖ := norm_pos_iff.mpr hx
  have hxinv : 0 < (‖(z.2 : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ := inv_pos.mpr hxpos
  have ht0 : 0 ≤ (z.1 : ℝ) := z.1.2.1
  have ht1 : (z.1 : ℝ) ≤ 1 := z.1.2.2
  have hpos : 0 < (1 - (z.1 : ℝ)) * (‖(z.2 : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹
      + (z.1 : ℝ) := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; norm_num
    · have h1 : 0 < 1 - (z.1 : ℝ) := by linarith
      have h2 : 0 < (1 - (z.1 : ℝ)) * (‖(z.2 : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ :=
        mul_pos h1 hxinv
      linarith
  exact smul_ne_zero (ne_of_gt hpos) hx

theorem continuous_vkOvlBaseHVal : Continuous vkOvlBaseHVal := by
  have hq : Continuous fun z : I × ovlV => (z.2 : Submission.Milnor.MSpace8) :=
    continuous_subtype_val.comp continuous_snd
  have ht : Continuous fun z : I × ovlV => (z.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have hxinv : Continuous fun z : I × ovlV =>
      (‖(z.2 : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ :=
    (hq.fst.norm).inv₀ (fun z => ne_of_gt (norm_pos_iff.mpr
      (Submission.Milnor.mem_vOpens.mp z.2.2)))
  have hc : Continuous fun z : I × ovlV =>
      (1 - (z.1 : ℝ)) * (‖(z.2 : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ + (z.1 : ℝ) :=
    ((continuous_const.sub ht).mul hxinv).add ht
  exact Continuous.prodMk (hc.smul hq.fst) hq.snd

theorem vkOvlBaseHomotopy :
    ∃ H : (pSi.comp pS).Homotopy (ContinuousMap.id ovlV),
      ∀ (t : ↑unitInterval) (q : ovlV), q ∈ ovlVA → H.toFun (t, q) ∈ ovlVA := by
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨vkOvlBaseHVal z, vkOvlBaseHVal_mem z⟩, continuous_vkOvlBaseHVal.subtype_mk vkOvlBaseHVal_mem⟩
    ?_ ?_, ?_⟩
  · intro q
    apply Subtype.ext
    show vkOvlBaseHVal (0, q) = ((pSi.comp pS) q : Submission.Milnor.MSpace8)
    apply Prod.ext
    · show ((1 - ((0 : ↑unitInterval) : ℝ)) *
          (‖(q : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ + ((0 : ↑unitInterval) : ℝ)) •
          (q : Submission.Milnor.MSpace8).1 =
        (Work.Milnor.vSphProj q : EuclideanSpace ℝ (Fin 4))
      rw [vSphProj_apply]
      norm_num
    · rfl
  · intro q
    apply Subtype.ext
    show vkOvlBaseHVal (1, q) = (q : Submission.Milnor.MSpace8)
    apply Prod.ext
    · show ((1 - ((1 : ↑unitInterval) : ℝ)) *
          (‖(q : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ + ((1 : ↑unitInterval) : ℝ)) •
          (q : Submission.Milnor.MSpace8).1 = (q : Submission.Milnor.MSpace8).1
      norm_num
    · rfl
  · intro t q hq
    show ‖(vkOvlBaseHVal (t, q) : Submission.Milnor.MSpace8).2‖ = 1
    exact hq

/-- value of the fibre homotopy -/
def vkOvlFibHVal (z : I × S3H) : S3H :=
  (z.2.1, ((z.1 : ℝ) + (1 - (z.1 : ℝ)) * rho z.2.2) • z.2.2)

theorem continuous_vkOvlFibHVal : Continuous vkOvlFibHVal := by
  have h1 : Continuous fun z : I × S3H => z.2.1 := continuous_fst.comp continuous_snd
  have h2 : Continuous fun z : I × S3H => z.2.2 := continuous_snd.comp continuous_snd
  have ht : Continuous fun z : I × S3H => (z.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have hρ : Continuous fun z : I × S3H => rho z.2.2 := continuous_rho.comp h2
  exact Continuous.prodMk h1 ((ht.add ((continuous_const.sub ht).mul hρ)).smul h2)

theorem vkOvlFibreHomotopy :
    Nonempty ((PsiM.comp PhiM).Homotopy (ContinuousMap.id S3H)) := by
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨vkOvlFibHVal, continuous_vkOvlFibHVal⟩ ?_ ?_⟩
  · intro p
    apply Prod.ext
    · rfl
    · show (((0 : ↑unitInterval) : ℝ) + (1 - ((0 : ↑unitInterval) : ℝ)) * rho p.2) • p.2 =
        linIsom.symm (fibRetract p.2)
      rw [show (((0 : ↑unitInterval) : ℝ) + (1 - ((0 : ↑unitInterval) : ℝ)) * rho p.2) =
        rho p.2 by norm_num, fibRetract, map_smul, linIsom.symm_apply_apply]
  · intro p
    apply Prod.ext
    · rfl
    · show (((1 : ↑unitInterval) : ℝ) + (1 - ((1 : ↑unitInterval) : ℝ)) * rho p.2) • p.2 = p.2
      norm_num


end

end Work.Cohomology.Crux
