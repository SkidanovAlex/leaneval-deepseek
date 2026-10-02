import Submission.Work.ThomBordism.chainSetup_psi_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} (Z : RealBundle B F ι)

/-- **The cochain-map property of `psiAbs`** (Leibniz plus the cocycle condition of the chosen
representative, plus the degree-cast bookkeeping).  The pieces (`psiAbs_d_cup`,
`pullAbs_cochainDiff`, `tauRepAt_cochainDiff`, `sset_of_d_transfer`, `subtype_val_cast`,
`cast_congrArg`, `eq_transport_cancel`) are all proved in
`Submission.Work.ThomBordism.chainSetup_psi_aux`; what is left here is only the `Eq.rec`-transport
of the degree cast `Nat.add_right_comm m 1 n` — the two sides live in the cochain families of
`SSetCochainComplex ℤ X` at the degrees `(m+n)+1` and `(m+1)+n`, which are equal but not
syntactically so. -/
theorem psiAbs_relDiff (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) (m : ℕ) (a : BaseC W m) :
    relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n)
        (psiAbs Z n U τ W hW m a)
      = (Nat.add_right_comm m 1 n) ▸
          (psiAbs Z n U τ W hW (m + 1)
            (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a)) := by
  apply Subtype.ext
  rw [relDiffLM_coe, subtype_val_cast, cast_congrArg]
  -- both sides now live in the cochain family of `SSetCochainComplex ℤ Y`
  change ((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))).d
        (m + n) ((m + n) + 1)).hom ((psiAbs Z n U τ W hW m a).1)
      = (Nat.add_right_comm m 1 n) ▸ ((psiAbs Z n U τ W hW (m + 1)
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a)).1)
  -- transfer the differential to the shifted degree pair `(m+n, (m+1)+n)`
  have h2 : (Nat.add_right_comm m 1 n) ▸
        (((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))).d
          (m + n) ((m + 1) + n)).hom ((psiAbs Z n U τ W hW m a).1))
      = ((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))).d
          (m + n) ((m + n) + 1)).hom ((psiAbs Z n U τ W hW m a).1) := by
    rw [sset_of_d_transfer (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (m := m) (n := n)
      ((psiAbs Z n U τ W hW m a).1)]
    exact eq_transport_cancel
      (P := fun t => ↥((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))).X t))
      (Nat.add_right_comm m 1 n) _
  rw [← h2]
  -- the cup shapes and the Leibniz rule with the cocycle `tauRepAt`
  rw [show (psiAbs Z n U τ W hW m a).1
      = cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m)
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n) from rfl]
  rw [psiAbs_d_cup Z n U τ W hW m a, pullAbs_cochainDiff]
  rw [show (psiAbs Z n U τ W hW (m + 1)
        (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a)).1
      = cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          (pullAbs Z W (m + 1) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a) :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (m + 1))
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n) from rfl]

/-- The `TotComplex`-differential form of `psiAbs_relDiff` (the shape used by the cone). -/
theorem psiAbs_diff (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (a : BaseC W m) :
    ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom (psiAbs Z n U τ W hW m a)
      = psiAbs Z n U τ W hW (m + 1) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a) := by
  rw [totComplex_d_transfer Z n W (m := m) (psiAbs Z n U τ W hW m a)]
  rw [totComplex_d_consecutive Z n W (psiAbs Z n U τ W hW m a)]
  rw [psiAbs_relDiff]
  exact eq_transport_cancel' (Nat.add_right_comm m 1 n) (P := fun t => TotC Z W t) _

end

end Work.ThomBordism
