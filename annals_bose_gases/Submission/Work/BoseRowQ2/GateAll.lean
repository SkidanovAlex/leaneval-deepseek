import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Work.BoseRowQ2.Rows
import Submission.Work.BoseRowsFS.exists_honestGateFS_of_honestInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# ⛔ `Work.BoseRowQ2.GateAll` — **RETIRED** (lead's ruling, 2026-10-07 17:20)

**Read this first.**  This module is *superseded* and must not be used:
`RowReserveLabelZero` and `exists_honestGateFS_of_honestInterface_all` are retired
by the lead's ruling — the `All` gate (`Work.BoseBoxFock.HonestGateFSAll` /
`exists_honestGateFSAll_of_honestInterface`, design `Submission/Work/BOSE_ALL_DESIGN.md`
item 6, vocabulary `Submission/Work/BoseBoxFock/AllDefs.lean`) takes
**`RowQ2AllRegimeN` directly**, with the reserve row `½⟨dNumOpR (RHi ∧ ¬PHq)⟩` built
into its own `Q3KernelFSAll.q2exLowerR` field (no separate obligation, no
`RowReserveLabelZero`).  Nothing below is needed for that route; the module is kept
only because files are never deleted in this project.

**The extra obligation is not merely unnecessary — it is FALSE.**  `RowReserveLabelZero`
(defined in `Rows.lean`) demands `2ρŴ₁ω(0)⟨n₀⟩ ≤ ½⟨dNumOpR (rHi ∧ ¬P_H^q)⟩` for **every**
`Ψ`; on the label-`0` one-particle state `Ψ = a₀†|vac⟩` the left side is `2ρŴ₁ω(0) > 0`
while the right side vanishes, because `rHi F E k` is a lower bound on `‖F.kmom k‖`
(`BoseGateFS/Defs.lean` l.148) and `kmom 0 = 0` (`Work.BoseBoxFock.kmomLab_zero`).  The
label-`0` tower is being turned into a machine-checked refutation of this route by the
sibling area `Submission/Work/BoseGateRefute/` (`WitnessAlg.lean`; also announced in
`Submission/Work/BoseGateAll/Defs.lean` §notes).  Hence the theorem below, though
proved, is vacuous, and the `All` gate is the only viable node.

**Note for the `All` gate's interface.**  The row it consumes must be at a cube size
and a threshold that the row *produces*: `Work.BoseRowQ2.RowQ2AllCore R εg` gives
`∃ Ng εg', εg' ≤ εg ∧ RowQ2AllCoreAt R εg' Ng`, because (i) `GchiAt` needs the
cube-size row (`FINDING_RowQ2AllCore_FALSE.md`) and (ii) the two-sided `ε`-window of
`Rows.lean` §2 is nonempty only for `μa³ ≲ 10^{-17684}`, so `RowQ2AllRegimeN` at an
`O(1)` threshold is false.  So `hrow3All : RowQ2AllRegimeN hthr.Ng R hthr.εg` has to
be supplied at a `hthr` whose `Ng` is large enough and whose `εg` is small enough —
i.e. the caller first moves `hthr` (`GateThresholds.mono` for `εg`, and the same
monotonicity for `Ng`; both directions are monotone because the rows' hypotheses are
`∀ μ, Ng μ ≤ (HM μ).N` and `μ a³ ≤ εg`), exactly as
`Work.BoseRowsFS.RowIntOneRegime_honest` already forces for row 2.

---

`Work.BoseRowsFS.exists_honestGateFS_of_honestInterface` closes the honest gate
from FS §4's régime, the `GateThresholds` bundle and the `HonestInterface` rows,
with **row 3 alone** (`hrow3`) still an input — in the *reserved* form used by the
gate's `GateInput.q2exLowerR` (`Work.BoseGateFS.Reserve.q2exLowerR_of_q2exLower`):
`Q2ex` (no label `0`) plus the free reserve `(1/2)⟨dNumOpR (rHi ∖ P_H^q)⟩`.

The corrected row `RowQ2AllRegimeN` (`Defs.lean`, assembled from the three rows of
`Rows.lean` by `RowQ2All_of_rows.lean`) carries the *correct* first-quantised
object `Q2exAll = Q2ex + 2ρŴ₁ω(0)·n₀` but **no** reserve.  Since the gate's
structures (`KzOpFS`, `GateInput`, `HonestRows`) hard-wire `Q2ex` and lie outside
this directory, the two are bridged here by the *one* extra obligation

    `RowReserveLabelZero : 2ρŴ₁ω(0)⟨n₀⟩ ≤ (1/2)⟨dNumOpR (rHi ∖ P_H^q)⟩`,

i.e. the gate's free reserve pays the label-`0` correction that `Q2exAll` adds.
That obligation is exactly what `NOTES.md` §A.4 flags: the reserve is a
`𝒟_k`-weighted sum over the bounded annulus `{(d²ℓ)⁻¹/2 ≤ ‖k‖ < (4K_H a)⁻¹}`,
which is *not* of the order of the `(b/400)ℓ⁻²` gap but is numerically enormous
(`≳ X^{686}` at FS's parameters), so the label-`0` content is absorbed there and
not by the `b/400` gap.  With it,
`exists_honestGateFS_of_honestInterface_all` is the gate node's deliverable from
the corrected row.

**⚠ The threshold must be shrunk by the caller.**  By `Rows.lean` §2 the
two-sided `ε`-window that FS l.3253–3257 needs is nonempty only for
`μa³ ≲ 10^{-17684}`, so `RowQ2AllCore` (`Rows.lean`) *produces* its own threshold
`εg' ≤ hthr.εg`, and the caller must re-instantiate `GateThresholds` and
`HonestInterface` at `εg'` (via `GateThresholds.mono`) before invoking this
theorem — exactly as `Work.BoseRowsFS.RowIntOneRegime_honest` already requires for
row 2.  The hypothesis `hrow3All` below is therefore the row *at the shrunk*
threshold.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `(KzEnvAt E ρ).rho = ρ` for `ρ ≥ 0` (the condensate density is `ρ` again). -/
lemma kzEnvAt_rho_of_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {E : Q3Env Mode} {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (KzEnvAt E ρ).rho = ρ := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  show (Real.sqrt (ρ * E.ell ^ 3)) ^ 2 / E.ell ^ 3 = ρ
  rw [Real.sq_sqrt (by positivity), mul_div_assoc, div_self (pow_ne_zero 3 (ne_of_gt hℓ)),
    mul_one]

/-- The `ρ`-re-pointing does not change `W1omega`. -/
lemma kzEnvAt_W1omega {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (ρ : ℝ) : (KzEnvAt E ρ).W1omega = E.W1omega := rfl

/-- The `ρ`-re-pointing does not change `W1omega0`. -/
lemma kzEnvAt_W1omega0 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (ρ : ℝ) : (KzEnvAt E ρ).W1omega0 = E.W1omega0 := rfl

/-- **The honest gate from the corrected row 3.**  The same hypotheses as
`Work.BoseRowsFS.exists_honestGateFS_of_honestInterface`, with `hrow3` replaced by
the corrected row `RowQ2AllRegimeN` plus the single extra obligation
`RowReserveLabelZero`. -/
theorem exists_honestGateFS_of_honestInterface_all
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsFS.HonestInterface R hthr)
    (hrow3All : RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) hthr.Ng R hthr.εg)
    (hres : RowReserveLabelZero (h := h) (fc := fc) (fu := fu) R hthr.εg) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ Work.BoseBoxFock.HonestGateFS v h fc fu K₀ b₀ := by
  classical
  refine Work.BoseRowsFS.exists_honestGateFS_of_honestInterface R hR hav hv_nonneg hvrad
    hv_supp hthr H (fun HM hN μ hμ hε ρ hρ Ψ => ?_)
  have hℓ : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav]
    exact ellH_pos v μ
  have hρr : (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).rho = ρ :=
    kzEnvAt_rho_of_nonneg hρ.1 hℓ
  have h0 : (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).W1omega 0
      = (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).W1omega0 :=
    honE_W1omega_zero v h fc fu HM μ
  -- the label-`0` splitting of `Q2exAll`
  have hsplit : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
          (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
      = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2ex
            (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
        + 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp 0) := by
    rw [FockData.Q2exAll_eq_Q2ex_add_two (F := Work.BoseRowsFS.honF v h fc fu HM μ)
        (E := KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ) h0,
      FockData.qw_add, FockData.qw_smul]
    rw [kzEnvAt_W1omega0, hρr]
  have hres' := hres HM μ hμ hε ρ hρ Ψ
  calc 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
              (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                  (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) :=
        hrow3All HM hN μ hμ hε ρ hρ Ψ
    _ = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2ex
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp 0)
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                  (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) := by
        rw [hsplit]
    _ ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2ex
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + (1 / 2) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).dNumOpR
                (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
                (fun k => rHi (Work.BoseRowsFS.honF v h fc fu HM μ)
                    (Work.BoseRowsFS.honE v h fc fu HM μ) k
                  ∧ ¬ (Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                      (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                      (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                  (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) :=
        add_le_add (add_le_add le_rfl hres') le_rfl
    _ = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2ex
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                  (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + (1 / 2) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).dNumOpR
                (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
                (fun k => rHi (Work.BoseRowsFS.honF v h fc fu HM μ)
                    (Work.BoseRowsFS.honE v h fc fu HM μ) k
                  ∧ ¬ (Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                      (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                      (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k)) := by
        ring

end Work.BoseRowQ2
