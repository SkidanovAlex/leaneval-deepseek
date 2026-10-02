/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The numeric hypotheses of the Krawczyk criterion, from the Boolean certificate `ok`

Item **A1** of the `SeedCertNum` contract (`NOTES_LEAD_mandelbar_noncusp.md` §2.2).  `KrawData.ok`
is the whole numerical check of the A1 certificate as a single `Bool`.  This file unpacks it:

* `0 < r` from `Dya.pos D.r`;
* the five nonnegativity clauses `0 ≤ ε, η, α, β` (the dyadic quantities of `A1Cert.lean` as real
  numbers) using the bridge `Work.SeedCertNum.matdya_*` of `matdya_toReal.lean`;
* the Jacobian enclosure `‖fderiv ℝ (Φ x₀) u - matLin A‖ ≤ ε` on the whole ball from `allJint`
  (`Work.SeedCertNum.fderiv_Phi_bound`);
* the three linear-algebra bounds `‖1 - M A‖ ≤ α`, `‖M‖ ≤ β`, `‖M (Φ u₀)‖ ≤ η` from
  `norm_matLin_le`, `matLin_mul`, `matLin_sub_id` and the residual bound `φ_u0_resid`;
* the ball condition `(α + β ε) r + η < r` from `Dya.lt`.

It is exactly the hypothesis package consumed by `Work.SeedCertNum.krawczyk_numeric`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Data
import Submission.Work.SeedCertNum.krawczyk_numeric
import Submission.Work.SeedCertNum.jentry_mem_Jint
import Submission.Work.SeedCertNum.norm_matLin_sub_le
import Submission.Work.SeedCertNum.hasFDerivAt_Phi
import Submission.Work.SeedCertNum.matLin_mul
import Submission.Work.SeedCertNum.matLin_sub_id
import Submission.Work.SeedCertNum.matLin_matOf
import Submission.Work.SeedCertNum.norm_matLin_le
import Submission.Work.SeedCertNum.mem_closedBall_iff
import Submission.Work.SeedCertNum.d1Chart_sound_nonneg
import Submission.Work.SeedCertNum.matdya_toReal
import Submission.Work.SeedCertNum.phi_u0_resid
import Submission.Work.SeedCertNum.fderiv_Phi_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

theorem kraw_ok_numeric (D : Work.SeedCert.KrawData) (h : Work.SeedCert.KrawData.ok D = true) :
    0 < Work.SeedCert.KrawData.rad D ∧
    0 ≤ (Work.SeedCert.KrawData.eps D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.eta D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.alpha D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.beta D).toReal ∧
    (∀ u ∈ Metric.closedBall (Work.SeedCert.KrawData.u₀ D) (Work.SeedCert.KrawData.rad D),
        ‖fderiv ℝ (Work.SeedCert.Phi (D.x₀).toReal) u - Work.SeedCert.matLin (Work.SeedCert.KrawData.Acr D)‖
          ≤ (Work.SeedCert.KrawData.eps D).toReal) ∧
    ‖(1 : Work.SeedCert.E3 →L[ℝ] Work.SeedCert.E3) -
        (Work.SeedCert.matLin (Work.SeedCert.KrawData.Mbr D)).comp
          (Work.SeedCert.matLin (Work.SeedCert.KrawData.Acr D))‖
      ≤ (Work.SeedCert.KrawData.alpha D).toReal ∧
    ‖Work.SeedCert.matLin (Work.SeedCert.KrawData.Mbr D)‖ ≤ (Work.SeedCert.KrawData.beta D).toReal ∧
    ‖Work.SeedCert.matLin (Work.SeedCert.KrawData.Mbr D)
        (Work.SeedCert.Phi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D))‖
      ≤ (Work.SeedCert.KrawData.eta D).toReal ∧
    ((Work.SeedCert.KrawData.alpha D).toReal +
        (Work.SeedCert.KrawData.beta D).toReal * (Work.SeedCert.KrawData.eps D).toReal) *
        (Work.SeedCert.KrawData.rad D) + (Work.SeedCert.KrawData.eta D).toReal
      < Work.SeedCert.KrawData.rad D := by
  have hD := h
  simp only [KrawData.ok, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨hpos, hallJ⟩, heta⟩, hball⟩ := hD
  have hrad : 0 < KrawData.rad D := by
    simpa [KrawData.rad] using (Dya.toReal_pos_iff D.r).mp hpos
  have heps : 0 ≤ (KrawData.eps D).toReal := matdya_eps_nonneg D
  have heta' : 0 ≤ (KrawData.eta D).toReal :=
    le_trans (matdya_etaBound_nonneg D) (Dya.toReal_le_of_le heta)
  have halpha : 0 ≤ (KrawData.alpha D).toReal := matdya_alpha_nonneg D
  have hbeta : 0 ≤ (KrawData.beta D).toReal := matdya_beta_nonneg D
  have hfd : ∀ u ∈ Metric.closedBall (KrawData.u₀ D) (KrawData.rad D),
      ‖fderiv ℝ (Phi (D.x₀).toReal) u - matLin (KrawData.Acr D)‖ ≤ (KrawData.eps D).toReal := by
    intro u hu
    simpa only [matdya_eps_toReal D] using fderiv_Phi_bound D h u hu
  have hBeta : ‖matLin (KrawData.Mbr D)‖ ≤ (KrawData.beta D).toReal := by
    rw [matdya_beta_toReal D]
    exact norm_matLin_le _
  have hAlpha : ‖(1 : E3 →L[ℝ] E3) -
      (matLin (KrawData.Mbr D)).comp (matLin (KrawData.Acr D))‖ ≤ (KrawData.alpha D).toReal := by
    rw [matLin_mul (KrawData.Mbr D) (KrawData.Acr D)]
    rw [show (1 : E3 →L[ℝ] E3) = ContinuousLinearMap.id ℝ E3 from rfl]
    have h1 : ContinuousLinearMap.id ℝ E3 - matLin (matMul (KrawData.Mbr D) (KrawData.Acr D))
        = -(matLin (matSub (matMul (KrawData.Mbr D) (KrawData.Acr D)) matId)) := by
      rw [← matLin_sub_id (matMul (KrawData.Mbr D) (KrawData.Acr D))]
      abel
    rw [h1, norm_neg, matdya_alpha_toReal D]
    exact norm_matLin_le _
  have hEta : ‖matLin (KrawData.Mbr D) (Phi (D.x₀).toReal (KrawData.u₀ D))‖
      ≤ (KrawData.eta D).toReal := by
    refine le_trans ?_ (Dya.toReal_le_of_le heta)
    calc ‖matLin (KrawData.Mbr D) (Phi (D.x₀).toReal (KrawData.u₀ D))‖
        ≤ ‖matLin (KrawData.Mbr D)‖ * ‖Phi (D.x₀).toReal (KrawData.u₀ D)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (KrawData.beta D).toReal * (KrawData.residBound D).toReal :=
          mul_le_mul hBeta (phi_u0_resid D) (norm_nonneg _) hbeta
      _ = (KrawData.etaBound D).toReal := by rw [KrawData.etaBound, Dya.toReal_mul]
  have hball' : ((KrawData.alpha D).toReal +
        (KrawData.beta D).toReal * (KrawData.eps D).toReal) * (KrawData.rad D)
        + (KrawData.eta D).toReal < KrawData.rad D := by
    have hlt := Dya.toReal_lt_of_lt hball
    simpa only [KrawData.rad, Dya.toReal_add, Dya.toReal_mul] using hlt
  exact ⟨hrad, heps, heta', halpha, hbeta, hfd, hAlpha, hBeta, hEta, hball'⟩

end Work.SeedCertNum
