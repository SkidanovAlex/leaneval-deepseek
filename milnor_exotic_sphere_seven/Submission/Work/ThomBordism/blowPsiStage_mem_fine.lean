import Mathlib
import Submission.Work.ThomBordism.blowPsi
import Submission.Work.ThomBordism.valuePmOneV2Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **The `t`-th stage of `blowPsiHomotopy` is injective away from the base point of the tube.**

Every stage of the interpolating family is a *fibrewise positive radial rescaling* of the normal
bundle followed by the capping and the tube map; such a map fixes the projection to the base and
only rescales the normal vector by a positive number, hence it can only send a point of the open
tube to `E.e x` if the point itself was `E.e x`.  Equivalently: the fine pair
`(C.U, C.U ∖ {E.e x})` is preserved by the homotopy, even though `blowPsi` is not positive at the
norm-`ε` sphere and the *closed* tube form of the statement fails.

This is the hypothesis `hp` of `Work.ThomBordism.blowPsiStage_one_relCohMap_eq_incl_fine`. -/
theorem blowPsiStage_mem_fine {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) (t : unitInterval) :
    ∀ y ∈ ({y : ↥C.openTube | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x} : Set ↥C.openTube),
      Work.ThomBordism.blowPsiStage E C t y ∈ Work.ThomBordism.tubePtSet E C x := by
  intro y hy
  show ((Work.ThomBordism.blowPsiStage E C t y : ↥C.U) : Work.Tubular.Euc (8 + k)) ≠ E.e x
  intro h
  -- The tube inverse of the stage is the capped interpolated rescaling of the tube inverse of `y`.
  have hq : Work.ThomBordism.cap E ε
      (Work.ThomBordism.radialRescale E (Work.ThomBordism.blowPsi ε ((t : unitInterval) : ℝ))
        (C.inv y.1)) = Work.Tubular.zeroSectionNormal E x := by
    rw [← Work.ThomBordism.blowPsiStage_inv_eq E C t y]
    rw [h]
    exact Work.ThomBordism.inv_embed E C x
  -- Its projection is the projection of `C.inv y.1` (a radial rescaling is fibrewise), which is
  -- therefore `x`.
  have hproj : ((C.inv y.1 : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1 = x := by
    have h1 := congrArg (fun z : Work.Tubular.NormalTotal E =>
      ((z : V.pt × Work.Tubular.Euc (8 + k))).1) hq
    simpa [Work.ThomBordism.cap] using h1
  -- Its normal vector is `(capping coefficient) • (blowPsi coefficient) • (normal vector of
  -- `C.inv y.1`)`, and both coefficients are nonzero on the open tube, so that vector vanishes.
  have hvec : ((C.inv y.1 : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 := by
    have h1 := congrArg (fun z : Work.Tubular.NormalTotal E =>
      ((z : V.pt × Work.Tubular.Euc (8 + k))).2) hq
    rw [Work.ThomBordism.cap, Work.ThomBordism.radialRescale_coe,
      Work.ThomBordism.radialRescale_coe, Work.Tubular.zeroSectionNormal_apply] at h1
    simp only at h1
    have hb : Work.ThomBordism.blowPsi ε ((t : unitInterval) : ℝ)
        (Work.Tubular.normalNorm E (C.inv y.1)) ≠ 0 :=
      ne_of_gt (Work.ThomBordism.blowPsi_pos C.eps_pos (C.normalNorm_inv_lt y.2)
        (unitInterval.nonneg t) (unitInterval.le_one t))
    have hc : Work.ThomBordism.capCoeff ε
        (Work.Tubular.normalNorm E
          (Work.ThomBordism.radialRescale E (Work.ThomBordism.blowPsi ε ((t : unitInterval) : ℝ))
            (C.inv y.1))) ≠ 0 :=
      ne_of_gt (Work.ThomBordism.capCoeff_pos C.eps_pos _ (Work.Tubular.normalNorm_nonneg E _))
    rcases smul_eq_zero.mp h1 with h0 | h2
    · exact absurd h0 hc
    · rcases smul_eq_zero.mp h2 with h3 | h4
      · exact absurd h3 hb
      · exact h4
  -- Hence `C.inv y.1` is the zero-section point at `x`, so `y.1 = tubeMap E (C.inv y.1) = E.e x`.
  have hp : C.inv y.1 = Work.Tubular.zeroSectionNormal E x := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simpa using hproj
    · simp [hvec]
  have hyeq : (y.1 : Work.Tubular.Euc (8 + k)) = E.e x := by
    have h1 : Work.Tubular.tubeMap E (C.inv y.1) = y.1 := C.tubeMap_inv y.1 (C.openTube_subset_U y.2)
    rw [hp, Work.ThomBordism.tubeMap_zeroSectionNormal] at h1
    exact h1.symm
  exact hy hyeq

end Work.ThomBordism
