import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.rowsOfShiftLarge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.rowOneLedgerWide`

The **wide-window** row-1 ledger: the PROVED `Work.BoseB1Cube.rowOneLedger` with its *unused*
hypothesis `t ≤ 5 μ` deleted.  Every hypothesis of the wide statement is consumed by the same
scalar step (`windowArith`, which needs only `4 μ ≤ t`), so the proof is a verbatim copy of
`rowOneLedgerRows` / `rowOneLedger` with the `h5` argument removed.

The helpers `ledgerColQ`, `ledgerColPc`, `ledgerG1`, `ledgerG2`, `ledgerG3` are `private` in
`rowsOfShiftLarge.lean`, hence invisible here; they are reproduced verbatim.  The conclusion of the
target is `Work.BoseB1Cube.payLedger`'s body (`payLedger` is definitionally the right-hand side of
`rowOneLedger`'s conclusion), closed by `rw [payLedger]`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Work.BoseB1Cube

/-! ## §1. The row-1 ledger, rows displayed, with no upper window bound -/

/-- **The row-1 ledger, rows displayed, with the upper window bound deleted.**  Identical to the
PROVED `Work.BoseB1Cube.rowOneLedgerRows` except that the (unused) hypothesis `t ≤ 5 μ` is gone. -/
theorem rowOneLedgerRowsWide {V μ a Γ κ K D₀ D₁ D₂ δ G M₁ MΔ S Q t Pc bg C Cn caT : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hCn : 4 ≤ Cn) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hSQ : S + Q = t * V) (ht : 0 ≤ t) (h4 : 4 * μ ≤ t)
    (hPc : S ^ 2 - S ≤ Pc) (hPcnn : 0 ≤ Pc)
    (hGle : G ≤ D₀ * M₁) (hM2m : (1 - K * δ) * G ≤ MΔ) (hM2ub : MΔ ≤ 2 * M₁)
    (hM1ub : M₁ ≤ D₁ * a * V) (hGub : G ≤ D₂ * a * V)
    (hδ : 0 ≤ δ) (hδΓ : δ ≤ 2 * Γ) (hK : 0 ≤ K) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hκΓ : κ * Γ ≤ 1 / 8) (hKδ : K * δ ≤ 1 / 2) (hμV : 1 ≤ μ * V)
    (hbg : (D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t ≤ bg)
    (hQcol : Q * (D₂ + D₁ / 2) * a * t + Q * C * a * t * (4 * Cn - 2) + C * a * Q ^ 2 / V
      ≤ bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q)
    (hPcrow : (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 - K * δ) * G * (S / V) / V
      ≤ (1 / 2) * MΔ * Pc / V ^ 2)
    (hG1 : (1 / 2) * G * (Q / V) * (t + S / V) ≤ D₂ * a * t * Q)
    (hG2 : (1 / 4) * M₁ * (t ^ 2 - (S / V) ^ 2) ≤ (1 / 2) * D₁ * a * t * Q)
    (hG3 : -(1 / 2) * G * (Q / V) * (t + S / V) - (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2
      ≤ (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2)
    (hsmall : M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2)
      + (1 / 2) * (1 + κ * Γ) * G * (t / V) + (1 / 2) * (1 - K * δ) * G * (S / V) / V
      + (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2 + C * a * caT ≤ (1 / 2) * μ ^ 2 * M₁) :
    (1 / 18) * μ * t * M₁
      ≤ (1 / 4) * (S / V - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁ - M₁ * (S / V) / V
        - μ * M₁ / (2 * V) - M₁ / (4 * V ^ 2)
        + (1 / 2) * MΔ * Pc / V ^ 2
        + bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q
        - (1 / 2) * (1 + κ * Γ) * G * (t ^ 2 + t / V)
        - C * a * caT := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have htV : t = (S + Q) / V := by rw [eq_div_iff hVne]; linarith [hSQ]
  have htsub : t - S / V = Q / V := by rw [htV]; ring
  have hQ0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have hsp1 : (0 : ℝ) ≤ Q * C * a * t * (4 * Cn - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hQ hC) ha) ht) (by linarith [hCn])
  have hsp2 : (0 : ℝ) ≤ C * a * Q ^ 2 / V :=
    div_nonneg (mul_nonneg (mul_nonneg hC ha) (sq_nonneg Q)) hV.le
  have hsp3 : (0 : ℝ) ≤ (1 / 2) * μ * M₁ * (Q / V) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hμ.le) hM1) hQ0
  have hS1 : 0 ≤ (1 / 2) * MΔ * Pc / V ^ 2 + D₂ * a * t * Q
      + (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2
      + (1 / 2) * (1 - K * δ) * G * (S / V) / V := by nlinarith [hPcrow, hG3, hG1]
  have hS2 : 0 ≤ -(M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2))
      - (1 / 2) * (1 + κ * Γ) * G * (t / V) - (1 / 2) * (1 - K * δ) * G * (S / V) / V
      - (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2 - C * a * caT + (1 / 2) * μ ^ 2 * M₁ := by
    nlinarith [hsmall]
  have hS3 : 0 ≤ bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q
      - Q * (D₂ + D₁ / 2) * a * t := by nlinarith [hQcol, hsp1, hsp2]
  have hS4 : 0 ≤ (1 / 2) * D₁ * a * t * Q - (1 / 4) * M₁ * (t ^ 2 - (S / V) ^ 2) := by
    nlinarith [hG2]
  have hid2 : (1 / 4) * (S / V - μ) ^ 2 * M₁
      = (1 / 4) * (t - μ) ^ 2 * M₁ - (1 / 4) * M₁ * (t ^ 2 - (S / V) ^ 2)
        + (1 / 2) * μ * M₁ * (Q / V) := by
    rw [show Q / V = t - S / V from htsub.symm]
    ring
  have hfin := windowArith hμ hM1 h4
  nlinarith [hS1, hS2, hS3, hS4, hsp3, hid2, hfin]

/-! ## §2. The rows of `payPortLedger2`, restated (private in that module) -/

private theorem ledgerColQ {S Q t V D₁ D₂ a bg C Cn μ : ℝ}
    (hbg : (D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t ≤ bg)
    (hQ : 0 ≤ Q) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (htsum : S / V + t = 2 * t - Q / V) :
    Q * (D₂ + D₁ / 2) * a * t + Q * C * a * t * (4 * Cn - 2) + C * a * Q ^ 2 / V
      ≤ bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q := by
  have h1 : ((D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t) * Q ≤ bg * Q :=
    mul_le_mul_of_nonneg_right hbg hQ
  have h2 : (μ + S / V) + (μ + t) = 2 * μ + 2 * t - Q / V := by linarith [htsum]
  have h3 : 0 ≤ C * a * Q := mul_nonneg (mul_nonneg hC ha) hQ
  ring_nf at h1 h2 h3 ⊢
  nlinarith [h1, h2, h3]

private theorem ledgerColPc {S V G K δ MΔ Pc : ℝ} (hKδ : K * δ ≤ 1 / 2) (hG : 0 ≤ G)
    (hM2m : (1 - K * δ) * G ≤ MΔ) (hPc : S ^ 2 - S ≤ Pc) (hPcnn : 0 ≤ Pc) :
    (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 - K * δ) * G * (S / V) / V
      ≤ (1 / 2) * MΔ * Pc / V ^ 2 := by
  have hG0 : 0 ≤ (1 - K * δ) * G := mul_nonneg (by linarith [hKδ]) hG
  have ht1 : (1 / 2) * ((1 - K * δ) * G) * Pc / V ^ 2 ≤ (1 / 2) * MΔ * Pc / V ^ 2 := by
    have h0 : 0 ≤ (1 / 2) * Pc / V ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hPcnn) (by positivity)
    have h := mul_le_mul_of_nonneg_right hM2m h0
    ring_nf at h ⊢
    linarith [h]
  have ht2 : (1 / 2) * ((1 - K * δ) * G) * (S ^ 2 - S) / V ^ 2
      ≤ (1 / 2) * ((1 - K * δ) * G) * Pc / V ^ 2 := by
    have h0 : 0 ≤ (1 / 2) * ((1 - K * δ) * G) / V ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hG0) (by positivity)
    have h := mul_le_mul_of_nonneg_left hPc h0
    ring_nf at h ⊢
    linarith [h]
  ring_nf at ht1 ht2 ⊢
  linarith [ht1, ht2]

private theorem ledgerG1 {G D₂ a V Q t S : ℝ} (hGub : G ≤ D₂ * a * V) (hQ : 0 ≤ Q)
    (hV : 0 < V) (hSVt : S / V ≤ t) (hSV0 : 0 ≤ S / V) (ht : 0 ≤ t)
    (hD₂ : 0 ≤ D₂) (ha : 0 ≤ a) :
    (1 / 2) * G * (Q / V) * (t + S / V) ≤ D₂ * a * t * Q := by
  have hQd0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have h1 : G * (Q / V) ≤ D₂ * a * Q := by
    have h := mul_le_mul_of_nonneg_right hGub hQd0
    have he : (D₂ * a * V) * (Q / V) = D₂ * a * Q := by
      field_simp
    linarith [h, he]
  have htxt0 : 0 ≤ t + S / V := by linarith [hSV0, ht]
  have htxt2 : t + S / V ≤ 2 * t := by linarith [hSVt]
  have h2 : (0 : ℝ) ≤ D₂ * a * Q := mul_nonneg (mul_nonneg hD₂ ha) hQ
  have h5 : (1 / 2) * (G * (Q / V) * (t + S / V)) ≤ (1 / 2) * ((D₂ * a * Q) * (2 * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul h1 htxt2 htxt0 h2) (by norm_num)
  have h6 : (1 / 2) * ((D₂ * a * Q) * (2 * t)) = D₂ * a * t * Q := by ring
  linarith [h5, h6]

private theorem ledgerG2 {M₁ D₁ a V Q t S : ℝ} (hM1ub : M₁ ≤ D₁ * a * V)
    (hQ : 0 ≤ Q) (hV : 0 < V) (htsub : t - S / V = Q / V) (hSV0 : 0 ≤ S / V) (ht : 0 ≤ t)
    (hSVt : S / V ≤ t) (hD₁ : 0 ≤ D₁) (ha : 0 ≤ a) :
    (1 / 4) * M₁ * (t ^ 2 - (S / V) ^ 2) ≤ (1 / 2) * D₁ * a * t * Q := by
  have hQd0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have htxt0 : 0 ≤ t + S / V := by linarith [hSV0, ht]
  have htxt2 : t + S / V ≤ 2 * t := by linarith [hSVt]
  have hfac : t ^ 2 - (S / V) ^ 2 = (Q / V) * (t + S / V) := by nlinarith [htsub, htxt0]
  have hD1aQ : (0 : ℝ) ≤ D₁ * a * Q := mul_nonneg (mul_nonneg hD₁ ha) hQ
  have h6a : M₁ * ((Q / V) * (t + S / V)) ≤ (D₁ * a * Q) * (t + S / V) := by
    calc M₁ * ((Q / V) * (t + S / V)) = (M₁ * (Q / V)) * (t + S / V) := by ring
      _ ≤ ((D₁ * a * V) * (Q / V)) * (t + S / V) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM1ub hQd0) htxt0
      _ = (D₁ * a * Q) * (t + S / V) := by
          field_simp
  have h6b : (D₁ * a * Q) * (t + S / V) ≤ (D₁ * a * Q) * (2 * t) :=
    mul_le_mul_of_nonneg_left htxt2 hD1aQ
  have h6 : M₁ * ((Q / V) * (t + S / V)) ≤ (D₁ * a * Q) * (2 * t) := le_trans h6a h6b
  have h7 : (1 / 4) * (M₁ * ((Q / V) * (t + S / V))) ≤ (1 / 4) * ((D₁ * a * Q) * (2 * t)) :=
    mul_le_mul_of_nonneg_left h6 (by norm_num)
  have h8 : (1 / 4) * ((D₁ * a * Q) * (2 * t)) = (1 / 2) * D₁ * a * t * Q := by ring
  rw [hfac]
  linarith [h7, h8]

private theorem ledgerG3 {G K κ Γ δ S Q t V : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hδΓ : δ ≤ 2 * Γ)
    (hV : 0 < V) (hQ : 0 ≤ Q) (hSV0 : 0 ≤ S / V) (ht : 0 ≤ t) (hG : 0 ≤ G)
    (hSVt : S / V ≤ t) (htsub : t - S / V = Q / V) :
    -(1 / 2) * G * (Q / V) * (t + S / V) - (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2
      ≤ (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2 := by
  have hQd0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have htxt0 : 0 ≤ t + S / V := by linarith [hSV0, ht]
  have hfac : (S / V) ^ 2 = t ^ 2 - (Q / V) * (t + S / V) := by nlinarith [htsub, htxt0]
  have hsq : (S / V) ^ 2 ≤ t ^ 2 := by nlinarith [hSVt, htxt0]
  have hpos : (0 : ℝ) ≤ 2 * Γ * t ^ 2 - δ * (S / V) ^ 2 := by nlinarith [hδΓ, hsq, hδ]
  have hmain : (0 : ℝ) ≤ (1 / 2) * G * (K * (2 * Γ * t ^ 2 - δ * (S / V) ^ 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) hG) (mul_nonneg hK hpos)
  have hid : (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2
        + (1 / 2) * G * (Q / V) * (t + S / V) + (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2
      = (1 / 2) * G * (K * (2 * Γ * t ^ 2 - δ * (S / V) ^ 2)) := by
    rw [hfac]; ring
  linarith [hid, hmain]

/-! ## §3. The wide-window row-1 ledger -/

/-- **The (wide-window) row-1 ledger.**  The row-1 demand `(1/18)μtM₁` (which carries no credit)
is dominated by the payment rung's expanded body `payLedger`, from the *same* row hypotheses as the
PROVED `Work.BoseB1Cube.payPortLedger2`, plus the `1/V`/`Γ`-bundle `hsmall`.

This is the PROVED `Work.BoseB1Cube.rowOneLedger` with its **unused** hypothesis
`h5 : t ≤ 5 μ` deleted (in `rowOneLedgerRows` the only window input consumed is
`h4 : 4 μ ≤ t`, via `windowArith`).  PROOF RECIPE: copy `rowOneLedgerRows` and `rowOneLedger` (and
their private helpers `ledgerColQ`, `ledgerColPc`, `ledgerG1`, `ledgerG2`, `ledgerG3`) from
`Submission/Work/BoseB1Cube/rowsOfShiftLarge.lean`, drop the `h5` argument from both statements and
from the internal call, and keep everything else identical.  The conclusion is `payLedger`'s body
(`payLedger` is defined in that same file and is definitionally the right-hand side of
`rowOneLedger`'s conclusion); `rw [payLedger]` or `change` before the final `nlinarith`. -/
theorem rowOneLedgerWide {V μ a Γ κ K D₀ D₁ D₂ δ G M₁ MΔ S Q t Pc bg C Cn caT : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hCn : 4 ≤ Cn) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hSQ : S + Q = t * V) (ht : 0 ≤ t) (h4 : 4 * μ ≤ t)
    (hPc : S ^ 2 - S ≤ Pc) (hPcnn : 0 ≤ Pc)
    (hGle : G ≤ D₀ * M₁) (hM2m : (1 - K * δ) * G ≤ MΔ) (hM2ub : MΔ ≤ 2 * M₁)
    (hM1ub : M₁ ≤ D₁ * a * V) (hGub : G ≤ D₂ * a * V)
    (hδ : 0 ≤ δ) (hδΓ : δ ≤ 2 * Γ) (hK : 0 ≤ K) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hκΓ : κ * Γ ≤ 1 / 8) (hKδ : K * δ ≤ 1 / 2) (hμV : 1 ≤ μ * V)
    (hbg : (D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t ≤ bg)
    (hsmall : M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2)
      + (1 / 2) * (1 + κ * Γ) * G * (t / V) + (1 / 2) * (1 - K * δ) * G * (S / V) / V
      + (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2 + C * a * caT ≤ (1 / 2) * μ ^ 2 * M₁) :
    (1 / 18) * μ * t * M₁
      ≤ Work.BoseB1Cube.payLedger V μ a Γ κ G M₁ MΔ S Q t Pc bg C caT := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have htV : t = (S + Q) / V := by rw [eq_div_iff hVne]; linarith [hSQ]
  have htsum : S / V + t = 2 * t - Q / V := by rw [htV]; ring
  have htsub : t - S / V = Q / V := by rw [htV]; ring
  have hSV0 : 0 ≤ S / V := div_nonneg hS hV.le
  have hSVt : S / V ≤ t := by rw [div_le_iff₀ hV]; nlinarith [hSQ, hQ]
  have h₁ := ledgerColQ (D₁ := D₁) (D₂ := D₂) hbg hQ hC ha htsum
  have h₂ := ledgerColPc (S := S) (V := V) (G := G) (K := K) (δ := δ) (MΔ := MΔ) (Pc := Pc)
    hKδ hG hM2m hPc hPcnn
  have h₃ : (1 / 2) * G * (Q / V) * (t + S / V) ≤ D₂ * a * t * Q :=
    ledgerG1 (G := G) (D₂ := D₂) hGub hQ hV hSVt hSV0 ht hD₂ ha
  have h₄ : (1 / 4) * M₁ * (t ^ 2 - (S / V) ^ 2) ≤ (1 / 2) * D₁ * a * t * Q :=
    ledgerG2 (M₁ := M₁) (D₁ := D₁) hM1ub hQ hV htsub hSV0 ht hSVt hD₁ ha
  have h₅ : -(1 / 2) * G * (Q / V) * (t + S / V) - (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2
      ≤ (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2 :=
    ledgerG3 (G := G) (K := K) (κ := κ) (Γ := Γ) (δ := δ)
      hK hδ hδΓ hV hQ hSV0 ht hG hSVt htsub
  rw [payLedger]
  exact rowOneLedgerRowsWide hV hμ ha hΓ hκ hC hCn hM1 hG hS hQ hSQ ht h4 hPc hPcnn hGle hM2m
    hM2ub hM1ub hGub hδ hδΓ hK hD₀ hD₁ hD₂ hκΓ hKδ hμV hbg h₁ h₂ h₃ h₄ h₅ hsmall

end Work.BoseB1Cube
