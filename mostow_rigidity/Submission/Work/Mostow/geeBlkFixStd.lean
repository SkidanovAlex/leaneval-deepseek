import Mathlib
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.stab_fermi_foot
import Submission.Work.Mostow.cardKAux
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.rotCanonAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- An element of `PO (k+m) 1` fixing the standard stratum pointwise is a pure normal block with
trivial restriction. -/
theorem geeBlkFixStd (k m : ℕ) (g : LeanEval.Geometry.MostowRigidity.PO (k + m) 1)
    (hg : ∀ v : Submission.Mostow.E k,
      g • Submission.Mostow.coordEmb k m v = Submission.Mostow.coordEmb k m v) :
    g = Submission.Mostow.blk k m 1 (Submission.Mostow.nrmStd k m g) ∧
      Submission.Mostow.resStd k m g = 1 := by
  have hAk : POActionProp k := rcPOActionProp k
  have hIk : HypIsometryProp k := rcHypIsometryProp k
  have hA : POActionProp (k + m) := rcPOActionProp (k + m)
  have hI : HypIsometryProp (k + m) := rcHypIsometryProp (k + m)
  have hP := POBasic.ofProp hA
  have hPk := POBasic.ofProp hAk
  have hstab : g ∈ SetStabStd k m := by
    rw [rhd_mem_stab_iff]
    intro u
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, (hg v).symm⟩
    · rintro ⟨v, hv⟩
      have h2 : g⁻¹ • (g • u) = g⁻¹ • (coordEmb k m v) := congrArg _ hv.symm
      rw [← hP.mul_smul g⁻¹ g u, inv_mul_cancel, hP.one_smul] at h2
      rw [← hg v, ← hP.mul_smul g⁻¹ g (coordEmb k m v), inv_mul_cancel, hP.one_smul] at h2
      exact ⟨v, h2.symm⟩
  have hdec := stab_eq_blk k m hAk hIk hA hI g hstab
  have hs : resStd k m g = 1 := by
    apply hPk.faithful
    intro v
    have h1 := rhd_blk_smul_coordEmb k m hAk hIk hA hI (resStd k m g) (nrmStd k m g) v
    have h2 : blk k m (resStd k m g) (nrmStd k m g) • coordEmb k m v = g • coordEmb k m v := by
      rw [← hdec]
    rw [h2, hg v] at h1
    exact (rhd_coordEmb_injective k m h1).symm
  refine ⟨?_, hs⟩
  conv_lhs => rw [hdec]
  rw [hs]

end Work.Mostow
