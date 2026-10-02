import Submission.Work.PTGeometric.ContinuousToPreData
import Submission.Work.ThomBordism.smoothingAgreement

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **The second smoothing step (inside the last mile) does not change the field on the collar `Sh`.**

`Work.PTGeometric.ambientPreData_of_continuous` replaces the field `v` of the continuous ambient data
by its `C^∞` smoothing (`Work.PTGeometric.smoothMap_into_tautTotal_eqOn`), which agrees with `v` on the
closed collar `Sh`.  Since `∂M ⊆ interior Sh` (`ContinuousAmbientData.bdry_subset_Sh`), the field is
unchanged **on the whole boundary**, which is what identifies the level set of the produced
ambient-collapse-end data with the raw level set near its boundary. -/
theorem ambientPreData_of_continuous_v_eqOn_Sh {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (D : ContinuousAmbientData n k ι Fam)
    (hmkC : ∀ (Pall : D.M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡∂ ((8 + k) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) Pall →
      (∀ x, Pall x ∈ Gr n k) →
      (∀ j, closure (D.UE j) ⊆
        {y : D.M | ∀ z : EuclideanSpace ℝ (Fin n), Pall y z = z → D.ellE j z = 0 → z = 0}) →
      ∃ (m' : ℕ) (C : AmbCharts n k D.M Pall m'), ∀ j : Fin D.mE, ∃ l : Fin m',
        C.ell l = D.ellE j ∧ C.U l = D.UE j) :
    ∀ x ∈ D.Sh, (ambientPreData_of_continuous hk D hmkC).v x = D.v x := by
  classical
  let hsm0 := smoothMap_into_tautTotal_eqOn n k hk D.M D.P D.v D.hP D.hv D.Sh D.isClosed_Sh D.V
      D.isOpen_V D.Sh_subset_V D.hPsmV D.hvsmV
      (fun x => ⟨D.P x, (D.isProj x).1, (D.isProj x).2.1, (D.isProj x).2.2, by simp⟩)
      (fun x _ => ⟨(D.isProj x).1, (D.isProj x).2.1, (D.isProj x).2.2⟩)
      (fun x _ => D.mem x)
  have heqSh := (Classical.choose_spec (Classical.choose_spec hsm0)).2.2.2.2
  intro x hx
  change (Classical.choose (Classical.choose_spec hsm0)) x = D.v x
  exact (heqSh x hx).2

/-- The `'`-form of the second smoothing agreement. -/
theorem ambientPreData_of_continuous'_v_eqOn_Sh {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (D : ContinuousAmbientData n k ι Fam) :
    ∀ x ∈ D.Sh, (ambientPreData_of_continuous' hk D).v x = D.v x :=
  ambientPreData_of_continuous_v_eqOn_Sh hk D _ 

end

end Work.PTGeometric
