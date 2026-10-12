import ChallengeDeps
import Submission.Work.BoseFixR.All.FarKernelRowsB
import Submission.Work.BoseFixR.All.FarResidAux
import Submission.Work.BoseFixR.All.epsFar_le_inv_eight
import Submission.Work.BoseFixR.All.farEnvSideB
import Submission.Work.BoseFixR.FarCorrSlotB
import Submission.Work.BoseFixR.FarResidBaux.epsSplitEqB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/FarResidOp.lean`

`All.FarResidB`/`All.FarResidBVar` consume the zero-point slot in its **scalar** form
`hZP : zpSumOf (farEnv E v μ ρ) ρ ≤ C + CE/2`.  The far leg of the honest family is driven
instead by the **operator** form of the zero-point slot

  `hZPop : -(C + CE/2)·‖f‖² ≤ ⟨f, KzBogFS F (farEnv E v μ ρ) ρ f⟩`,

which is what the slots `All.farZPWin` (sharp, `C = ½ρ²ℓ³C₀Mcont`, `ρ ≥ μ/10`) and
`All.farZPGen` (crude, all `ρ ≥ 0`) deliver.  This file contains the bookkeeping of
`farResidB_bookkeeping` with that single input replaced; everything else (the `ε`-split of
`KzBogFS`, the `ε^{-1/2}`-diagonal, the ε-corrected three-`Q` slot) is a verbatim copy, and
the only use of `hZP` in the original proof — the passage through `FarBogPair` — is dropped,
and the `FarBogPair` side conditions (which held only for `ρ > 0`) are replaced by the bare
evenness of `τ` (supplied by `All.honestBoxFam_tau_even`); hence the lemma applies at `ρ = 0`
as well, with no case split.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The bookkeeping of the far residual, with the zero-point slot in operator form.** -/
theorem farResidOp {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (D : KzDatum) {μ ρ C CE : ℝ} (f : D.F.H) (hf : D.T.NWindow D.E.bigM f)
    (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ)
    (hZPop : -(C + CE / 2) * D.F.normSq f
        ≤ D.F.qw f (Work.BoseBoxFock.KzBogFS D.F (Work.BoseFixR.All.farEnv D.E v μ ρ) ρ))
    (h3Q : ∀ g : D.F.H, D.T.NWindow D.E.bigM g →
        -(CE / 4) * D.F.normSq g
          ≤ D.F.qw g (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw g (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw g (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw g (∑ k : D.Mode, (Work.BoseFixR.All.epsFar v μ ρ * D.E.tau k) • D.F.nOp k))
    (hτev : ∀ k : D.Mode, D.E.tau (-k) = D.E.tau k)
    (hτ0 : ∀ k : D.Mode, 0 ≤ D.E.tau k)
    (hε1 : Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 2)
    (hwin : ∑ k : D.Mode, (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k))
        ≤ 16 * D.E.bigM * D.F.normSq f)
    (hcorr : 16 * ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
        * D.E.bigM ≤ CE / 4)
    (hCnn : 0 ≤ C) (hEEnn : 0 ≤ CE) :
    -CE * D.F.normSq f ≤ C * D.F.normSq f
      + D.F.qw f (Work.BoseBoxFock.KzBogFS D.F D.E ρ)
      + D.F.qw f (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ))
      + D.F.qw f (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ))
      + D.F.qw f (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ)) := by
  have h3 := h3Q f hf
  set Nf := D.F.normSq f with hNfdef
  set Z := D.F.qw f (Work.BoseBoxFock.KzBogFS D.F D.E ρ) with hZdef
  set Bk := D.F.qw f (Work.BoseBoxFock.KzBogFS D.F (Work.BoseFixR.All.farEnv D.E v μ ρ) ρ)
    with hBkdef
  set A1 := D.F.qw f (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ)) with hA1def
  set A2 := D.F.qw f (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ)) with hA2def
  set A3 := D.F.qw f (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ)) with hA3def
  set H3 := D.F.qw f (∑ k : D.Mode, (Work.BoseFixR.All.epsFar v μ ρ * D.E.tau k) • D.F.nOp k)
    with hH3def
  set R := ∑ k : D.Mode,
      (Work.BoseFixR.All.epsFar v μ ρ * D.E.tau k) * D.F.qw f (D.F.nOp k) with hRdef
  set Wv := ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
      * (∑ k : D.Mode, (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k))) with hWvdef
  have hNf0 : 0 ≤ Nf := by rw [hNfdef]; exact D.F.normSq_nonneg f
  have hH3R : H3 = R := by
    rw [hH3def, hRdef]
    exact Work.BoseFixR.All.qw_sum_finset_zp D.F Finset.univ
      (fun k => Work.BoseFixR.All.epsFar v μ ρ * D.E.tau k) (fun k => D.F.nOp k) f
  rw [hH3R] at h3
  -- the `ε`-split of `KzBogFS` at `farEnv`
  have hsplit : Z = Bk + (∑ k : D.Mode, (1 / 2 : ℝ)
      * ((D.E.tau k - (Work.BoseFixR.All.farEnv D.E v μ ρ).tau k)
          * D.F.qw f (D.F.nOp k + D.F.nOp (-k)))) :=
    Work.BoseFixR.All.KzBogFS_epsSplit D.F D.E v μ ρ f
  have hsplitS : (∑ k : D.Mode, (1 / 2 : ℝ)
      * ((D.E.tau k - (Work.BoseFixR.All.farEnv D.E v μ ρ).tau k)
          * D.F.qw f (D.F.nOp k + D.F.nOp (-k)))) = R - Wv := by
    rw [hRdef, hWvdef]
    exact FarResidBaux.epsSplitEqB D.F D.E v μ ρ f hτev
  have hZeq : Z = Bk + R - Wv := by rw [hsplit, hsplitS]; ring
  -- the `ε^{-1/2}`-diagonal against the window and `FarCorrSlotB`
  have hWle : Wv ≤ (CE / 4) * Nf := by
    have hρa : 0 ≤ ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
      mul_nonneg (mul_nonneg hρ (Real.rpow_nonneg (Real.sqrt_nonneg _) _)) hav.le
    have h2 : ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
          * (16 * D.E.bigM * Nf)
        = (16 * ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * D.E.bigM)
            * Nf := by ring
    calc Wv = ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
          * (∑ k : D.Mode, (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k))) := rfl
      _ ≤ ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
          * (16 * D.E.bigM * Nf) := mul_le_mul_of_nonneg_left hwin hρa
      _ = (16 * ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v * D.E.bigM)
            * Nf := h2
      _ ≤ (CE / 4) * Nf := mul_le_mul_of_nonneg_right hcorr hNf0
  -- the zero-point slot, in *operator* form: this replaces `FarBogPair` + the scalar `hZP`
  have hbog : -(C + CE / 2) * Nf ≤ Bk := by
    rw [hBkdef, hNfdef]
    exact hZPop
  linarith [hbog, hZeq, h3, hWle]

end Work.BoseFixR.All
