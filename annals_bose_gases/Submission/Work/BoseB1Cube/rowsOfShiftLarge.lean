import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.boxMassGeOfGate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.rowsOfShiftLarge`

The two per-size rows of FS `thm:smallbox` at the sliding box, on the **large-window / flatness**
region of `goodSet`: for every admissible `μ`, every `u ∈ goodSet`, assuming

* the **window gate** `a v ≤ μ·PBW h μ u` (the negation of `smallWin`), and
* FS's **flatness / shift hypothesis** `(1 − 2·PBΓ v μ)·chiMass ≤ ∫ χ_B(x)χ_B(x−z)`
  (`‖z‖ ≤ R`, the hypothesis of the PROVED `Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass`),

the two rows of `Work.BoseB1Cube.CubeRowsOn` hold at `4 = 4`.

## The route

* the assembly rung `Work.BoseB1Cube.sbWordCube_ge_payPortR3` (payment + refined Bogoliubov port)
  and the expanded body `payPortR3Lower`;
* **row 2** by the PROVED ledger `payPortLedger2` (which consumes the credit
  `C(μ²aΓ·PBW + μa)` to pay the `1/V`-rows and the port's Γ-rows);
* **row 1** by the new ledger `rowOneLedgerRows` below: its demand `(1/18)μtW` carries *no* credit,
  so the credit's unused half is spent on the `1/V`-rows (`hsmall` bundle) and the remaining
  surplus `¼(t−μ)²W − ½μ²W` pays the demand on the window `t ∈ [4μ,5μ)`;
* the two analytic inputs are the PROVED `shiftMassLower` (the sharp lower mass law
  `(1−θ)·8π(a v)·chiMass ≤ PBW` *without* the core hypothesis, from the shift hypothesis) and the
  PROVED `shiftR3Row` (the `R₃` column at the total count), plus `boxMassGeOfGate`
  (`64 ≤ μ·|B(u)|`, i.e. the corner boxes on which the window vanishes are excluded by the gate).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## §1. The pure-real row-1 ledger

The row inequalities are those of the PROVED `Work.BoseB1Cube.payPortLedger2` (`colQ`, `colPc`,
`gRow1`, `gRow2`, `gRow3`), but the *demand* is the row-1 demand `(1/18)μtM₁` (no credit), and the
`1/V`-rows plus the port's `Γ`-rows are grouped into the single bundle `hsmall`. -/

/-- **The row-1 window arithmetic**: on `t ≥ 4μ` the surplus `¼(t−μ)² − μ²` of `a0MainLocBox`
dominates the demand `(1/18)μt`. -/
theorem windowArith {μ t M₁ : ℝ} (hμ : 0 < μ) (hM1 : 0 ≤ M₁) (h4 : 4 * μ ≤ t) :
    (1 / 18) * μ * t * M₁ + μ ^ 2 * M₁ ≤ (1 / 4) * (t - μ) ^ 2 * M₁ := by
  have h4' : μ * (4 * μ) ≤ μ * t := mul_le_mul_of_nonneg_left h4 hμ.le
  have hmn : (1 / 18) * μ * t + μ ^ 2 ≤ (3 / 4) * μ * (t - μ) := by
    nlinarith [h4', hμ]
  have h30 : 0 ≤ t - μ := by linarith
  have h31 : 3 * μ ≤ t - μ := by linarith
  have hs : (3 * μ) * (t - μ) ≤ (t - μ) * (t - μ) :=
    mul_le_mul_of_nonneg_right h31 h30
  have hstep : (3 / 4) * μ * (t - μ) ≤ (1 / 4) * (t - μ) ^ 2 := by
    nlinarith [hs]
  have hfin : (1 / 18) * μ * t + μ ^ 2 ≤ (1 / 4) * (t - μ) ^ 2 := le_trans hmn hstep
  nlinarith [hfin, hM1, hμ]

/-- **The row-1 ledger, rows displayed.**  From the row inequalities of `payPortLedger2` and the
`1/V`/`Γ`-bundle `hsmall`, the row-1 demand is dominated by the rung's body. -/
theorem rowOneLedgerRows {V μ a Γ κ K D₀ D₁ D₂ δ G M₁ MΔ S Q t Pc bg C Cn caT : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hCn : 4 ≤ Cn) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hSQ : S + Q = t * V) (ht : 0 ≤ t) (h4 : 4 * μ ≤ t) (h5 : t ≤ 5 * μ)
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

/-! ## §2. The row-1 ledger at the corpus's row hypotheses -/

/-- **The rows of `payPortLedger2`, restated** (they are `private` in that module). -/
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

/-- **The row-1 ledger at the corpus's row hypotheses**: the same inputs as `payPortLedger2`
plus the `1/V`/`Γ`-bundle `hsmall` and the window `t ∈ [4μ,5μ)`. -/
theorem rowOneLedger {V μ a Γ κ K D₀ D₁ D₂ δ G M₁ MΔ S Q t Pc bg C Cn caT : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hCn : 4 ≤ Cn) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hSQ : S + Q = t * V) (ht : 0 ≤ t) (h4 : 4 * μ ≤ t) (h5 : t ≤ 5 * μ)
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
      ≤ (1 / 4) * (S / V - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁ - M₁ * (S / V) / V
        - μ * M₁ / (2 * V) - M₁ / (4 * V ^ 2)
        + (1 / 2) * MΔ * Pc / V ^ 2
        + bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q
        - (1 / 2) * (1 + κ * Γ) * G * (t ^ 2 + t / V)
        - C * a * caT := by
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
  exact rowOneLedgerRows hV hμ ha hΓ hκ hC hCn hM1 hG hS hQ hSQ ht h4 h5 hPc hPcnn hGle hM2m
    hM2ub hM1ub hGub hδ hδΓ hK hD₀ hD₁ hD₂ hκΓ hKδ hμV hbg h₁ h₂ h₃ h₄ h₅ hsmall

/-- The `n = 0` clause of the word: with no particles every slot sum is empty. -/
private theorem sbWordCube_zero_particles {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (u : E3) (Ψ : X 0 → ℝ) : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 := by
  simp only [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral,
    Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.cnPlusBoxInd,
    Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword,
    Submission.BoseGases.pairSet]
  simp

/-- **The `PBΓ`-smallness threshold**: `PBΓ v μ = fsXp (μ·a³) (287/2) → 0`, so for every
prescribed `Γ₀ > 0` there is a diluteness threshold below which `PBΓ v μ ≤ Γ₀`. -/
theorem exists_pbGamma_le {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {Γ₀ : ℝ}
    (hΓ₀ : 0 < Γ₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε μ →
      Work.BoseFixB1B.PBΓ v μ ≤ Γ₀ := by
  obtain ⟨ε₁, hε₁, hle⟩ := exists_fsXp_mul_le (C := 1) (c := Γ₀) (e := (287 / 2 : ℝ))
    (by norm_num) hΓ₀ (by norm_num)
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  intro μ hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 :=
    mul_pos hAdm.1 (pow_pos hav 3)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right _ _)
  have hta : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ := le_trans hAdm.2.1 (min_le_left _ _)
  have hΓeq : Work.BoseFixB1B.PBΓ v μ
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) := by
    rw [show Work.BoseFixB1B.PBΓ v μ
        = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) from rfl,
      Work.BoseFixB1.KB3_half_eq hav hAdm.1]
  rw [hΓeq]
  exact le_trans (fsXp_mono_le ht0 hta (by norm_num)) (by simpa using hle)

/-! ## §3. `payPortR3Lower` in the ledger's letters

The scalar ledgers (`payPortLedger2`, `rowOneLedger`) conclude at the *expanded* rung body.  The
definition `payLedger` is that expansion, so that the definitional identity
`payPortR3Lower = payLedger` can be stated once here and attributed at the call site by a single
rewrite (`rw [payPortR3Lower_eq ...]`), keeping the expensive `unfold`/`ring` out of the
state-level assembly. -/

/-- **The ledger's right-hand side.**  Exactly the conclusion body of the PROVED
`Work.BoseB1Cube.payPortLedger2` / `rowOneLedger`. -/
noncomputable def payLedger (V μ a Γ κ G M₁ MΔ S Q t Pc bg C caT : ℝ) : ℝ :=
  (1 / 4) * (S / V - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁ - M₁ * (S / V) / V
    - μ * M₁ / (2 * V) - M₁ / (4 * V ^ 2)
    + (1 / 2) * MΔ * Pc / V ^ 2
    + bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q
    - (1 / 2) * (1 + κ * Γ) * G * (t ^ 2 + t / V)
    - C * a * caT

/-- **The elementary regrouping** `(((n+1)·n)/V² = (n/V)² + (n/V)/V` — valid for every `V`, with
the convention `x/0 = 0`. -/
theorem succ_mul_div_sq {n V : ℝ} :
    (((n : ℝ) + 1) * (n : ℝ)) / V ^ 2 = ((n : ℝ) / V) ^ 2 + (n : ℝ) / V / V := by
  rcases eq_or_ne V 0 with rfl | hV
  · simp
  · field_simp
    try ring

/-- **`payPortR3Lower` in the ledger's letters**: the definitional unfolding of the assembly rung,
with `a0MainLocBox` expanded and `(((n+1)n)/V²)` regrouped. -/
theorem payPortR3Lower_eq {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    {Φ : X n → ℝ} {u : E3} {κ C V χ Γ M₁ M₂ S Q Pc t c₀ G : ℝ}
    (hV : V = Work.BoseFixB1.bV v μ u)
    (hχ : χ = Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u)
    (hΓ : Γ = Work.BoseFixB1B.PBΓ v μ)
    (hM₁ : M₁ = Work.BoseFixB1.bW v h μ u)
    (hM₂ : M₂ = Work.BoseFixB1.bM2 v h μ u)
    (hS : S = Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Φ)
    (hQ : Q = Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Φ)
    (hPc : Pc = Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Φ)
    (ht : t = (n : ℝ) / V)
    (hc₀ : c₀ = Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    (hG : G = Submission.BoseGases.g0w0Mass h * χ) :
    payPortR3Lower v h μ n Φ u κ C
      = payLedger V μ (_root_.BoseGases.a v) Γ κ G M₁ (M₂ - M₁) S Q t Pc
          (Work.BoseFixB1.bGapCoeff v μ) C (c₀ ^ 3 * t * χ) := by
  subst V
  subst χ
  subst Γ
  subst M₁
  subst M₂
  subst S
  subst Q
  subst Pc
  subst c₀
  subst G
  subst t
  simp only [payLedger, payPortR3Lower, Work.BoseFixB1.a0MainLocBox, Work.BoseFixB1.bM2]
  rw [succ_mul_div_sq]
  ring

theorem rowsOfShiftLarge {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (_root_.BoseGases.a v) ≤ μ * Work.BoseFixB1B.PBW h μ u →
        (∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
          (1 - 2 * Work.BoseFixB1B.PBΓ v μ) *
              Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
            ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u x
                * Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u (x - z)) →
        (∀ {n' : ℕ}, 4 * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ) →
            (n' : ℝ) < 5 * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Ψ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
              Work.BoseFixB1B.InBox v μ u Ψ →
              (1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u)
                  * Work.BoseFixB1B.PBW h μ u
                  * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
          ∧ (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 8 * μ * Work.BoseFixB1B.PBBV v μ u →
              ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
                Work.BoseFixB1B.InBox v μ u Ψ →
                ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2
                      * Work.BoseFixB1B.PBW h μ u
                    - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
                    - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                          * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
                    * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                  ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ) := by
  classical
  -- ## 1. the analytic ingredients (all PROVED corpus lemmas)
  obtain ⟨εP, κ, CP, hεP, hκ0, hCP0, hrung⟩ :=
    sbWordCube_ge_payPortR3 h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εG, hεG, hGates⟩ := boxDataGatesContDiff h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εW, KW, hεW, hKW0, hWrow⟩ :=
    Work.BoseFixB1S.w1MassB_le_const_mul_boxMass h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εM, hεM, hM2le2⟩ := bM2_le_two_mul_bW h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εγ, hεγ, hγ⟩ := gammaRegimeAt (v := v) hav hR
  obtain ⟨εV, hεV, hVgate⟩ := boxMassGeOfGate h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εR3, hεR3, hR3row⟩ :=
    shiftR3Row (v := v) h hv hv1 hvrad hR hv_supp hav (Cn := 4) (by norm_num)
  -- ## 2. the constants
  set D₁ : ℝ := KW with hD₁def
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁def]; exact hKW0
  set D₂ : ℝ := 8 * Real.pi *
    (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
    with hD₂def
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂def]; positivity
  set C : ℝ := max CP (9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130) + 1
    with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ max CP (9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130) :=
      le_trans hCP0 (le_max_left _ _)
    linarith
  have hCPle : CP ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))
  have hCredC : 2 * D₁ * 4 + 3 * D₁ / 4 + 4 * D₂ * 4 ≤ C := by
    have h2 : 2 * D₁ * 4 + 3 * D₁ / 4 + 4 * D₂ * 4 ≤ 9 * D₁ + 16 * D₂ := by
      nlinarith [hD₁0, hD₂0]
    have h3 : 9 * D₁ + 16 * D₂ ≤
        9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130 := by
      have h4 : (0 : ℝ) ≤ 128 * (2 + κ) / (_root_.BoseGases.a v) + 130 := by positivity
      linarith
    have h4 : 9 * D₁ + 16 * D₂ ≤
        max CP (9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130) :=
      le_trans h3 (le_max_right _ _)
    rw [hCdef]
    linarith [h2, h4]
  have hCaC : 4 * 2 * (2 * 1 + κ) * 4 ^ 2 ≤ C * (_root_.BoseGases.a v) := by
    have h2 : 128 * (2 + κ) / (_root_.BoseGases.a v) * (_root_.BoseGases.a v)
        = 128 * (2 + κ) := by
      rw [div_mul_cancel₀ _ (ne_of_gt hav)]
    have h3 : 128 * (2 + κ) / (_root_.BoseGases.a v) ≤ C := by
      rw [hCdef]
      have h4 : 128 * (2 + κ) / (_root_.BoseGases.a v) ≤
          9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130 := by
        nlinarith [hD₁0, hD₂0, hκ0]
      have h5 : max CP (9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130)
          ≤ max CP (9 * D₁ + 16 * D₂ + 128 * (2 + κ) / (_root_.BoseGases.a v) + 130) + 1 := by
        linarith
      linarith [le_trans h4 (le_max_right CP (9 * D₁ + 16 * D₂ + 128 * (2 + κ)
        / (_root_.BoseGases.a v) + 130)), h5]
    have h5 : 128 * (2 + κ) ≤ C * (_root_.BoseGases.a v) := by
      have h6 := mul_le_mul_of_nonneg_right h3 hav.le
      linarith [h2, h6]
    nlinarith [h5]
  set Kg : ℝ := 8 * D₂ + 4 * D₁ + 130 * C + 1 with hKgdef
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; nlinarith [hD₁0, hD₂0, hC0]
  obtain ⟨εbg, hεbg, hbggate⟩ := bGapCoeff_gate (v := v) hav Kg hKg0
  -- ## 3. the `Γ`-threshold
  obtain ⟨εΓ, hεΓ, hΓle⟩ := exists_pbGamma_le (v := v) hav
    (Γ₀ := min (min (1 / (8 * (max κ 1))) (1 / (500 * (2 + κ))))
      (1 / (10 * (C * (_root_.BoseGases.a v) + 1))))
    (by refine lt_min (lt_min (div_pos one_pos (by positivity)) (div_pos one_pos (by positivity)))
          (div_pos one_pos (by positivity)))
  -- ## 4. the merged diluteness threshold
  let T : Finset ℝ := {εP, εG, εW, εM, εγ, εV, εR3, εΓ, εbg, 1}
  have hT : T.Nonempty := by simp [T]
  set ε₀ : ℝ := T.min' hT with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def, Finset.lt_min'_iff]
    intro y hy
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hεP, hεG, hεW, hεM, hεγ, hεV, hεR3, hεΓ, hεbg, one_pos]
  have hle₀ : ∀ {ε' : ℝ}, ε' ∈ T → ε₀ ≤ ε' := by
    intro ε' hε'
    rw [hε₀def]
    exact Finset.min'_le T ε' hε'
  refine ⟨ε₀, C, hε₀pos, hC0, ?_⟩
  intro μ hAdm u hu hgate hshift
  have AdmOf : ∀ {ε' : ℝ}, ε' ∈ T → Work.BoseBoxFix.Adm v ε' μ :=
    fun hε' => Work.BoseFixB1.Adm.mono hAdm (hle₀ hε')
  have hAdmP : Work.BoseBoxFix.Adm v εP μ := AdmOf (by simp [T])
  have hAdmG : Work.BoseBoxFix.Adm v εG μ := AdmOf (by simp [T])
  have hAdmW : Work.BoseBoxFix.Adm v εW μ := AdmOf (by simp [T])
  have hAdmM : Work.BoseBoxFix.Adm v εM μ := AdmOf (by simp [T])
  have hAdmγ : Work.BoseBoxFix.Adm v εγ μ := AdmOf (by simp [T])
  have hAdmV : Work.BoseBoxFix.Adm v εV μ := AdmOf (by simp [T])
  have hAdmR3 : Work.BoseBoxFix.Adm v εR3 μ := AdmOf (by simp [T])
  have hAdmΓ : Work.BoseBoxFix.Adm v εΓ μ := AdmOf (by simp [T])
  have hAdmbg : Work.BoseBoxFix.Adm v εbg μ := AdmOf (by simp [T])
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := AdmOf (by simp [T])
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM48 : 1 ≤ Work.BoseFixB1.bM v μ := by
    show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hMe : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := rfl
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := hAdm1.2.1
  have hVgood : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood hav hμ hdil1 hu
  have hV64 : 64 ≤ μ * Work.BoseFixB1B.PBBV v μ u := hVgate μ hAdmV u hu hgate
  -- ## 5. the state-level abbreviations
  set V : ℝ := Work.BoseFixB1.bV v μ u with hVdef
  set χ : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bD v μ) u with hχdef
  set Γ : ℝ := Work.BoseFixB1B.PBΓ v μ with hΓdef
  set M₁ : ℝ := Work.BoseFixB1.bW v h μ u with hM₁def
  set M₂ : ℝ := Work.BoseFixB1.bM2 v h μ u with hM₂def
  have hVPB : Work.BoseFixB1B.PBBV v μ u = V := by rw [hVdef]; rfl
  have hV0 : 0 < V := by
    rw [hVdef]
    exact Work.BoseFixB1.boxMass_pos_of_goodSet (Work.BoseFixB1.adm_ell_pos hAdm)
      (Work.BoseFixB1.adm_d_pos hAdm) hμ hu
  have hχ0 : 0 ≤ χ := by rw [hχdef]; exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hM₁0 : 0 ≤ M₁ := by
    rw [hM₁def]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp (Work.BoseFixB1.adm_ell_pos hAdm)
      (Work.BoseFixB1.adm_d_pos hAdm) u
  have hG0 : 0 ≤ Submission.BoseGases.g0w0Mass h * χ :=
    mul_nonneg (Work.SmallBoxA0.g0w0Mass_nonneg_general hR hv_supp h) hχ0
  obtain ⟨hR16, hRχ, hd8, hΓpos', hΓhalf, _hΓsharp⟩ := hγ hAdmγ
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; linarith [hΓpos']
  have hΓhalf' : 2 * Γ ≤ 1 / 2 := by rw [hΓdef]; exact hΓhalf
  have hM2le : M₂ ≤ 2 * M₁ := by rw [hM₂def, hM₁def]; exact hM2le2 μ hAdmM u
  have hM2ub : M₂ - M₁ ≤ 2 * M₁ := by linarith [hM2le]
  -- the weight bridge `boxM1 = bW`
  have hbM1 : Work.BoseFixB1.bM1 v h μ u = Work.BoseFixB1.bW v h μ u :=
    (Work.BoseFixB1S.mfW_eq_mfM1 (v := v) (h := h) (μ := μ) (u := u) hM48 hℓ hd).symm
  have hW1 : Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) = M₁ := by
    rw [hM₁def]
    exact hbM1
  -- the mass comparison `(1 - 2Γ)·g₀w₀·χ ≤ M₂ - M₁`
  have hM2m : (1 - 1 * (2 * Γ)) * (Submission.BoseGases.g0w0Mass h * χ) ≤ M₂ - M₁ := by
    have hraw := Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass (v := v) (R := R) hv_supp hR hv hvrad
      hv1 h (M := Work.BoseFixB1.bM v μ) hM48 (ℓ := Work.BoseFixB1.bSide v μ)
      (d := Work.BoseFixB1.bD v μ) (θ := 2 * Work.BoseFixB1B.PBΓ v μ) hℓ hd hR16 hRχ u hshift
    have hB2 : Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
        = M₂ := by rw [hM₂def]; rfl
    have hL : (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u
        = (1 - 1 * (2 * Γ)) * (Submission.BoseGases.g0w0Mass h * χ) := by
      rw [hΓdef, hχdef]; ring
    rw [← hL, ← hB2, ← hW1]
    exact hraw
  have hGle2 : Submission.BoseGases.g0w0Mass h * χ ≤ 2 * M₁ := by
    have h1 : (1 : ℝ) / 2 ≤ 1 - 1 * (2 * Γ) := by linarith [hΓhalf]
    have h2 : (1 : ℝ) / 2 * (Submission.BoseGases.g0w0Mass h * χ)
        ≤ (1 - 1 * (2 * Γ)) * (Submission.BoseGases.g0w0Mass h * χ) :=
      mul_le_mul_of_nonneg_right h1 hG0
    have h3 : M₂ - M₁ ≤ M₁ := by linarith [hM2le]
    linarith [h2, hM2m, h3]
  -- the upper mass rows
  have hM1ub : M₁ ≤ D₁ * (_root_.BoseGases.a v) * V := by
    have h1 := hWrow μ hAdmW u
    rw [hM₁def, hD₁def, hVdef]
    simpa only [Work.BoseFixB1.bW, Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
      Work.BoseFixB1.bV] using h1
  have hGub : Submission.BoseGases.g0w0Mass h * χ ≤ D₂ * (_root_.BoseGases.a v) * V := by
    have hχb := Work.BoseFixB1S.chiMass_le_const_mul_boxMass (M := Work.BoseFixB1.bM v μ) hM48
      hℓ hd u
    have hχb' : χ ≤ (Submission.BoseGases.chiSupAbs *
        Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 * V := by
      rw [hχdef, hVdef]
      simpa only [Work.BoseFixB1.bV, hMe] using hχb
    have hGle : Submission.BoseGases.g0w0Mass h ≤ 8 * Real.pi * (_root_.BoseGases.a v) :=
      Work.SmallBoxA0.g0w0Mass_le_av hR hv hvrad hv_supp h
    calc Submission.BoseGases.g0w0Mass h * χ
        ≤ (8 * Real.pi * (_root_.BoseGases.a v)) *
            ((Submission.BoseGases.chiSupAbs *
              Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 * V) :=
          mul_le_mul hGle hχb' hχ0 (by positivity)
      _ = D₂ * (_root_.BoseGases.a v) * V := by rw [hD₂def]; ring
  -- the `Γ`-smallnesses
  have hΓκ : κ * Γ ≤ 1 / 8 := by
    have h1 : Work.BoseFixB1B.PBΓ v μ ≤ 1 / (8 * (max κ 1)) :=
      le_trans (hΓle μ hAdmΓ) (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : κ ≤ max κ 1 := le_max_left _ _
    have hΓpos2 : 0 < Work.BoseFixB1B.PBΓ v μ := by
      rcases lt_or_ge (Work.BoseFixB1B.PBΓ v μ) 0 with hlt | hge
      · nlinarith [hΓpos', hlt]
      · exact lt_of_le_of_ne hge (by intro h0; rw [h0] at hΓpos'; linarith [hΓpos'])
    have h2pos : (0 : ℝ) < max κ 1 := lt_of_lt_of_le one_pos (le_max_right κ 1)
    have h4 : κ * Work.BoseFixB1B.PBΓ v μ ≤ (max κ 1) * (1 / (8 * (max κ 1))) :=
      mul_le_mul h2 h1 (le_of_lt hΓpos2) (le_of_lt h2pos)
    have h5 : (max κ 1) * (1 / (8 * (max κ 1))) = 1 / 8 := by
      rw [mul_one_div, div_eq_iff (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt h2pos))]
      ring
    rw [hΓdef]
    linarith [h4, h5]
  have hΓCaT : Γ ≤ 1 / (10 * (C * (_root_.BoseGases.a v) + 1)) := by
    rw [hΓdef]
    exact le_trans (hΓle μ hAdmΓ) (min_le_right _ _)
  have hΓsmallRow : (2 + κ) * Γ ≤ 1 / 500 := by
    have h1 : Work.BoseFixB1B.PBΓ v μ ≤ 1 / (500 * (2 + κ)) :=
      le_trans (hΓle μ hAdmΓ) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 : 0 < 500 * (2 + κ) := by positivity
    rw [le_div_iff₀ h2] at h1
    rw [hΓdef, le_div_iff₀ (by norm_num : (0 : ℝ) < 500)]
    nlinarith [h1, h2]
  have hδ0 : (0 : ℝ) ≤ 2 * Γ := by linarith [hΓ0]
  have hK1 : (0 : ℝ) ≤ 1 := by norm_num
  have hD₀2 : (0 : ℝ) ≤ 2 := by norm_num
  have hKδ' : 1 * (2 * Γ) ≤ 1 / 2 := by linarith [hΓhalf']
  -- the gap gate for a generic count
  have hbg' : ∀ {t : ℝ}, t ≤ 2 * 4 * μ →
      (D₂ + D₁ / 2) * (_root_.BoseGases.a v) * t + 2 * C * (_root_.BoseGases.a v) * μ
        + 4 * 4 * C * (_root_.BoseGases.a v) * t ≤ Work.BoseFixB1.bGapCoeff v μ := by
    intro t ht
    have hμa0 : (0 : ℝ) ≤ μ * (_root_.BoseGases.a v) := mul_nonneg hμ.le hav.le
    have ht8 : t ≤ 8 * μ := by linarith [ht]
    have h1 : (D₂ + D₁ / 2) * (_root_.BoseGases.a v) * t
        ≤ (8 * D₂ + 4 * D₁) * (μ * (_root_.BoseGases.a v)) := by
      nlinarith [ht8, hD₁0, hD₂0, hμ, hav.le]
    have h2 : 4 * 4 * C * (_root_.BoseGases.a v) * t ≤ 128 * C * (μ * (_root_.BoseGases.a v)) := by
      nlinarith [ht8, hC0, hμ, hav.le]
    have h3 : 2 * C * (_root_.BoseGases.a v) * μ = 2 * C * (μ * (_root_.BoseGases.a v)) := by ring
    have h4 : (8 * D₂ + 4 * D₁ + 130 * C) * (μ * (_root_.BoseGases.a v))
        ≤ Kg * (μ * (_root_.BoseGases.a v)) := by
      rw [hKgdef]
      nlinarith [hD₁0, hD₂0, hC0, hμa0]
    have hgg := hbggate μ hAdmbg
    linarith [h1, h2, h3, h4, hgg]
  -- the `R₃` row for a generic count
  have hR3' : ∀ {n : ℕ}, (n : ℝ) ≤ 8 * μ * V →
      2 * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ
        ≤ μ ^ 2 * Γ * M₁ := by
    intro n hn
    have h2 := hR3row (μ := μ) hAdmR3 u hu hshift
      (show (n : ℝ) ≤ 2 * (4 : ℝ) * μ * Work.BoseFixB1B.PBBV v μ u by
        rw [hVPB]; linarith [hn])
    rw [hVPB] at h2
    rw [hχdef, hΓdef, hM₁def]
    exact h2
  have hR3led : ∀ {n : ℕ}, (n : ℝ) ≤ 8 * μ * V →
      2 * C * (_root_.BoseGases.a v)
          * ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)
        ≤ C * μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ := by
    intro n hn
    have h := mul_le_mul_of_nonneg_left (hR3' hn) (mul_nonneg hC0 hav.le)
    have e1 : 2 * C * (_root_.BoseGases.a v)
        * ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)
        = C * (_root_.BoseGases.a v)
          * (2 * ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)) := by
      ring
    have e2 : C * (_root_.BoseGases.a v) * (μ ^ 2 * Γ * M₁)
        = C * μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ := by ring
    linarith [h, e1, e2]
  -- ## 6. the two rows
  constructor
  · -- ### row 1
    intro n h4n h5n Ψ hΨc hIn
    rw [hVPB] at h4n h5n
    change (1 / 18) * μ * ((n : ℝ) / V) * M₁
        * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ
    by_cases hI0 : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 0
    · have hbI : Work.BoseFixB1.bI v μ Ψ = 0 := by rw [Work.BoseFixB1.bI]; exact hI0
      have hz := sbWordCube_eq_zero_of_bI_eq_zero (v := v) (h := h) (μ := μ) hΨc hbI u
      rw [hI0, mul_zero, hz]
    · have hpcm : 0 < ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2 :=
        lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg _)) (Ne.symm hI0)
      have hn1 : 1 ≤ n := by
        have h4' : (4 : ℝ) ≤ (n : ℝ) := by
          have h4n' : (4 : ℝ) * (μ * V) ≤ (n : ℝ) := by nlinarith [h4n, hVgood, hμ]
          nlinarith [h4n', hVgood, hμ]
        exact_mod_cast (by linarith : (1 : ℝ) ≤ (n : ℝ))
      set s : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2
        with hsdef
      set c : ℝ := (Real.sqrt s)⁻¹ with hcdef
      set Φ : X n → ℝ := fun x => c * Ψ x with hΦdef
      have hsc : Real.sqrt s * c = 1 := by
        rw [hcdef, mul_inv_cancel₀ (Real.sqrt_pos_of_pos hpcm).ne']
      have hcs : c ^ 2 * s = 1 := by
        have h1 : Real.sqrt s * Real.sqrt s = s := by rw [← sq, Real.sq_sqrt hpcm.le]
        nlinarith [hsc, h1]
      have hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ := by
        rw [hΦdef]; exact contDiff_const.mul hΨc
      have hnormI : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Φ x) ^ 2) = 1 := by
        show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (c * Ψ x) ^ 2) = 1
        rw [Work.BoseFixB1S.normB_smul' (ℓ := Work.BoseFixB1.bSide v μ) Ψ c,
          show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = s
            from rfl]
        exact hcs
      have hnormΦ : Work.BoseFixB1.bI v μ Φ = 1 := hnormI
      have hsuppΦ : ∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u := by
        filter_upwards [hIn] with x hx hne
        exact hx (fun hz => hne (by simp [hΦdef, hz]))
      obtain ⟨hVpos, hWdef, hM1nn, hM2le', hPcnn, hcS2⟩ := hGates μ hAdmG n Φ hΦc u hu hnormI
      set S : ℝ := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Φ with hSdef
      set Q : ℝ := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Φ with hQdef
      set Pc : ℝ := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Φ with hPcdef
      have hS0 : 0 ≤ S := by
        rw [hSdef]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      have hQ0 : 0 ≤ Q := by
        rw [hQdef]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      have hPc0 : 0 ≤ Pc := by rw [hPcdef]; exact hPcnn
      have hS2S : S ^ 2 - S ≤ Pc := by rw [hPcdef]; simpa only [pow_two] using hcS2
      have hSQ : S + Q = ((n : ℝ) / V) * V := by
        rw [hSdef, hQdef]
        simp only [Work.BoseFixB1.bA]
        have hsplit := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
          (volA := Work.BoseFixB1.bV v μ u) hℓ hVpos
          (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
          (by simp only [Work.BoseFixB1.bV, Work.SmallBoxSliding.boxMass_eq_measureReal,
            MeasureTheory.Measure.real_def])
          (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΦc.continuous hsuppΦ
        rw [hsplit, hnormI, mul_one, div_mul_cancel₀ _ (ne_of_gt hV0)]
      have ht0 : 0 ≤ (n : ℝ) / V := div_nonneg (Nat.cast_nonneg n) hV0.le
      have h4μ : 4 * μ ≤ (n : ℝ) / V := by
        rw [le_div_iff₀ hV0]; exact h4n
      have h5μ : (n : ℝ) / V ≤ 5 * μ := by
        rw [div_le_iff₀ hV0]; linarith [h5n]
      have hwin8 : (n : ℝ) ≤ 8 * μ * V := by nlinarith [h5n, hμ, hV0]
      have h8μ' : (n : ℝ) / V ≤ 2 * 4 * μ := by linarith [h5μ]
      have hV64' : 64 ≤ μ * V := by rw [← hVPB]; exact hV64
      have hsmall := smallRowsBundle (V := V) (μ := μ) (a := _root_.BoseGases.a v) (χ := χ)
        (G := Submission.BoseGases.g0w0Mass h * χ) (M₁ := M₁) (S := S) (Q := Q)
        (c₀ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (Γ := Γ) (κ := κ) (KK := 1) (C := C)
        (n := (n : ℝ)) hV0 hμ hΓ0 hκ0 hC0 hM₁0 hG0 hS0 hQ0 hχ0
        (le_of_lt (Work.BoseFixB1S.sbCut_pos hμ hav)) (Nat.cast_nonneg n) hSQ h4μ h5μ hV64'
        (by norm_num) (by norm_num) (by simpa using hKδ') hΓκ hGle2 (hR3' hwin8) hΓCaT hΓsmallRow
      have hled := rowOneLedger (V := V) (μ := μ) (a := _root_.BoseGases.a v) (Γ := Γ) (κ := κ)
        (K := 1) (D₀ := 2) (D₁ := D₁) (D₂ := D₂) (δ := 2 * Γ)
        (G := Submission.BoseGases.g0w0Mass h * χ) (M₁ := M₁) (MΔ := M₂ - M₁) (S := S) (Q := Q)
        (t := (n : ℝ) / V) (Pc := Pc) (bg := Work.BoseFixB1.bGapCoeff v μ) (C := C) (Cn := 4)
        (caT := (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)
        hV0 hμ hav.le hΓ0 hκ0 hC0 (le_rfl : (4 : ℝ) ≤ 4) hM₁0 hG0 hS0 hQ0 hSQ ht0 h4μ h5μ hS2S
        hPc0 hGle2 hM2m hM2ub hM1ub hGub hδ0 (le_refl (2 * Γ)) hK1 hD₀2 hD₁0 hD₂0 hΓκ
        (by simpa using hKδ') hVgood (hbg' h8μ') hsmall
      have hpay := payPortR3Lower_eq (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) (u := u)
        (κ := κ) (C := C) (V := V) (χ := χ) (Γ := Γ) (M₁ := M₁) (M₂ := M₂) (S := S) (Q := Q)
        (Pc := Pc) (t := (n : ℝ) / V) (c₀ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
        (G := Submission.BoseGases.g0w0Mass h * χ)
        hVdef hχdef hΓdef hM₁def hM₂def hSdef hQdef hPcdef rfl rfl rfl
      have hcore : (1 / 18) * μ * ((n : ℝ) / V) * M₁ ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
        have hr := hrung μ hAdmP n Φ u hu hn1 hΦc hnormΦ hsuppΦ
        have hsbcut : (0 : ℝ) ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
          le_of_lt (Work.BoseFixB1S.sbCut_pos hμ hav)
        have hmono := payPortR3Lower_mono_C (v := v) h (μ := μ) (n := n) (Φ := Φ) (u := u)
          (κ := κ) (C := CP) (C' := C) hCPle hav.le hμ.le hsbcut hVpos hS0 hQ0 hχ0
        have hfin : payLedger V μ (_root_.BoseGases.a v) Γ κ
            (Submission.BoseGases.g0w0Mass h * χ) M₁ (M₂ - M₁) S Q ((n : ℝ) / V) Pc
            (Work.BoseFixB1.bGapCoeff v μ) C
            ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
          rw [← hpay]
          exact le_trans hmono hr
        exact le_trans hled hfin
      have hgoal : (1 / 18) * μ * ((n : ℝ) / V) * M₁ * s
          ≤ s * Work.BoseFixB1B.sbWordCube v h μ u Φ := by
        rw [mul_comm s (Work.BoseFixB1B.sbWordCube v h μ u Φ)]
        exact mul_le_mul_of_nonneg_right hcore hpcm.le
      have hΨeq : (fun x => Real.sqrt s * Φ x) = Ψ := by
        funext x; rw [hΦdef]; simp only; rw [← mul_assoc, hsc, one_mul]
      have hsW : Work.BoseFixB1B.sbWordCube v h μ u Ψ = s * Work.BoseFixB1B.sbWordCube v h μ u Φ := by
        conv_lhs => rw [← hΨeq]
        rw [Work.BoseFixB1S.sbWordCube_smul h u Φ (Real.sqrt s), Real.sq_sqrt hpcm.le]
      rw [hsW]
      exact hgoal
  · -- ### row 2
    intro n h8n Ψ hΨc hIn
    rw [hVPB] at h8n
    change ((1 / 4) * (((n : ℝ) / V) - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁
        - C * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ + μ * (_root_.BoseGases.a v)))
        * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      rw [show Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0
        from sbWordCube_zero_particles (v := v) (h := h) (μ := μ) u Ψ]
      have h1 : (0 : ℝ) ≤ C * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁
          + μ * (_root_.BoseGases.a v)) :=
        mul_nonneg hC0 (add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) hΓ0) hM₁0)
          (mul_nonneg hμ.le hav.le))
      have hneg : (1 / 4) * (((0 : ℝ) / V) - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ + μ * (_root_.BoseGases.a v)) ≤ 0 := by
        rw [zero_div]
        nlinarith [h1, hM₁0, sq_nonneg μ]
      exact mul_nonpos_of_nonpos_of_nonneg (by simpa only [Nat.cast_zero] using hneg)
        (integral_nonneg (fun x => sq_nonneg _))
    · have hn1 : 1 ≤ n := hn
      by_cases hI0 : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 0
      · have hbI : Work.BoseFixB1.bI v μ Ψ = 0 := by rw [Work.BoseFixB1.bI]; exact hI0
        have hz := sbWordCube_eq_zero_of_bI_eq_zero (v := v) (h := h) (μ := μ) hΨc hbI u
        have h2 : ((1 / 4) * (((n : ℝ) / V) - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ + μ * (_root_.BoseGases.a v))) * (0 : ℝ)
            = 0 := by ring
        rw [hI0, hz, h2]
      · have hpcm : 0 < ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2 :=
          lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg _)) (Ne.symm hI0)
        set s : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2
          with hsdef
        set c : ℝ := (Real.sqrt s)⁻¹ with hcdef
        set Φ : X n → ℝ := fun x => c * Ψ x with hΦdef
        have hsc : Real.sqrt s * c = 1 := by
          rw [hcdef, mul_inv_cancel₀ (Real.sqrt_pos_of_pos hpcm).ne']
        have hcs : c ^ 2 * s = 1 := by
          have h1 : Real.sqrt s * Real.sqrt s = s := by rw [← sq, Real.sq_sqrt hpcm.le]
          nlinarith [hsc, h1]
        have hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ := by
          rw [hΦdef]; exact contDiff_const.mul hΨc
        have hnormI : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Φ x) ^ 2) = 1 := by
          show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (c * Ψ x) ^ 2) = 1
          rw [Work.BoseFixB1S.normB_smul' (ℓ := Work.BoseFixB1.bSide v μ) Ψ c,
            show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = s
              from rfl]
          exact hcs
        have hnormΦ : Work.BoseFixB1.bI v μ Φ = 1 := hnormI
        have hsuppΦ : ∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
            Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u := by
          filter_upwards [hIn] with x hx hne
          exact hx (fun hz => hne (by simp [hΦdef, hz]))
        obtain ⟨hVpos, hWdef, hM1nn, hM2le', hPcnn, hcS2⟩ := hGates μ hAdmG n Φ hΦc u hu hnormI
        set S : ℝ := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Φ with hSdef
        set Q : ℝ := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Φ with hQdef
        set Pc : ℝ := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) Φ with hPcdef
        have hS0 : 0 ≤ S := by
          rw [hSdef]
          exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
        have hQ0 : 0 ≤ Q := by
          rw [hQdef]
          exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
        have hPc0 : 0 ≤ Pc := by rw [hPcdef]; exact hPcnn
        have hS2S : S ^ 2 - S ≤ Pc := by rw [hPcdef]; simpa only [pow_two] using hcS2
        have hSQ : S + Q = ((n : ℝ) / V) * V := by
          rw [hSdef, hQdef]
          simp only [Work.BoseFixB1.bA]
          have hsplit := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
            (volA := Work.BoseFixB1.bV v μ u) hℓ hVpos
            (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
            (by simp only [Work.BoseFixB1.bV, Work.SmallBoxSliding.boxMass_eq_measureReal,
              MeasureTheory.Measure.real_def])
            (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΦc.continuous hsuppΦ
          rw [hsplit, hnormI, mul_one, div_mul_cancel₀ _ (ne_of_gt hV0)]
        have ht0 : 0 ≤ (n : ℝ) / V := div_nonneg (Nat.cast_nonneg n) hV0.le
        have htw : (n : ℝ) / V ≤ 2 * 4 * μ := by
          rw [div_le_iff₀ hV0, show (2 : ℝ) * 4 * μ * V = 8 * μ * V by ring]
          exact h8n
        have hled := payPortLedger2 (V := V) (μ := μ) (a := _root_.BoseGases.a v) (Γ := Γ)
          (κ := κ) (K := 1) (D₀ := 2) (D₁ := D₁) (D₂ := D₂) (δ := 2 * Γ)
          (G := Submission.BoseGases.g0w0Mass h * χ) (M₁ := M₁) (MΔ := M₂ - M₁) (S := S) (Q := Q)
          (t := (n : ℝ) / V) (Pc := Pc) (bg := Work.BoseFixB1.bGapCoeff v μ) (C := C) (Cn := 4)
          (caT := (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)
          hV0 hμ hav.le hΓ0 hκ0 hC0 (le_rfl : (4 : ℝ) ≤ 4) hM₁0 hG0 hS0 hQ0 hSQ ht0 htw hS2S hPc0
          hGle2 hM2m hM1ub hGub hδ0 (le_refl (2 * Γ)) hK1 hD₀2 hD₁0 hD₂0 hΓκ (by simpa using hKδ')
          hVgood hCaC (hbg' htw) (hR3led h8n) hCredC
        have hpay := payPortR3Lower_eq (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) (u := u)
          (κ := κ) (C := C) (V := V) (χ := χ) (Γ := Γ) (M₁ := M₁) (M₂ := M₂) (S := S) (Q := Q)
          (Pc := Pc) (t := (n : ℝ) / V) (c₀ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
          (G := Submission.BoseGases.g0w0Mass h * χ)
          hVdef hχdef hΓdef hM₁def hM₂def hSdef hQdef hPcdef rfl rfl rfl
        have hcore : (1 / 4) * (((n : ℝ) / V) - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ + μ * (_root_.BoseGases.a v))
            ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
          have hr := hrung μ hAdmP n Φ u hu hn1 hΦc hnormΦ hsuppΦ
          have hsbcut : (0 : ℝ) ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
            le_of_lt (Work.BoseFixB1S.sbCut_pos hμ hav)
          have hmono := payPortR3Lower_mono_C (v := v) h (μ := μ) (n := n) (Φ := Φ) (u := u)
            (κ := κ) (C := CP) (C' := C) hCPle hav.le hμ.le hsbcut hVpos hS0 hQ0 hχ0
          have hfin : payLedger V μ (_root_.BoseGases.a v) Γ κ
              (Submission.BoseGases.g0w0Mass h * χ) M₁ (M₂ - M₁) S Q ((n : ℝ) / V) Pc
              (Work.BoseFixB1.bGapCoeff v μ) C
              ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * ((n : ℝ) / V) * χ)
              ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
            rw [← hpay]
            exact le_trans hmono hr
          exact le_trans hled hfin
        have hgoal : ((1 / 4) * (((n : ℝ) / V) - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ + μ * (_root_.BoseGases.a v))) * s
            ≤ s * Work.BoseFixB1B.sbWordCube v h μ u Φ := by
          rw [mul_comm s (Work.BoseFixB1B.sbWordCube v h μ u Φ)]
          exact mul_le_mul_of_nonneg_right hcore hpcm.le
        have hΨeq : (fun x => Real.sqrt s * Φ x) = Ψ := by
          funext x; rw [hΦdef]; simp only; rw [← mul_assoc, hsc, one_mul]
        have hsW : Work.BoseFixB1B.sbWordCube v h μ u Ψ
            = s * Work.BoseFixB1B.sbWordCube v h μ u Φ := by
          conv_lhs => rw [← hΨeq]
          rw [Work.BoseFixB1S.sbWordCube_smul h u Φ (Real.sqrt s), Real.sq_sqrt hpcm.le]
        rw [hsW]
        exact hgoal

end Work.BoseB1Cube
