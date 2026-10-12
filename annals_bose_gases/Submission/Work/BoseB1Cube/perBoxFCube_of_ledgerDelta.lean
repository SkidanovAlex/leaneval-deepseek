import ChallengeDeps
import Submission.Work.BoseFixB1S.LowCountWindowAllJCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# `Work.BoseB1Cube.perBoxFCube_of_ledgerDelta`

The **Δ-augmented ledger at the matched (cube) window**: the cube twin of the PROVED
`Work.BoseFixB1.Up.perBoxF_of_ledger_delta`
(`Submission/Work/BoseFixB1/Up/FlatLedgerDelta.lean`).

The only difference between `Work.BoseFixB1S.PerBoxFCube` and `Work.BoseFixB1.PerBoxF` is the word
on the right-hand side: `PerBoxFCube` uses the matched-window sliding word
`Work.BoseFixB1B.sbWordCube` (= `sbKinCube + sbPot`) instead of the frozen `sbWord`
(= `sbKin + sbPot`), whose kinetic slot carries the *ball* window while its kernels carry the cube
bump `chiSmallB`.  Every other atom of the ledger (`w1MassB`, `flatTau`, `flatFibSum`,
`flatPairSum`, `flatPairMass`, `flatFterm`, `normB`, `chiMass`, the error bracket) is
*window-free*, so the proof is the verbatim port of the flat-branch proof: unfold the row, use the
split `sbWordCube = sbKinCube + sbPot` together with the hypothesis
`hsplit : sbPot = −μ·fibSum + pairSum`, and close by the pure-real arithmetic
`cubeArithDeltaCore`.  The kinetic payer `P` enters only through `hkin : P ≤ sbKinCube`.
-/

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The pure-real arithmetic of the Δ-augmented ledger

This is `Work.BoseFixB1.Up.flatArithDeltaCore`, restated (with the same proof) in this file so that
the module's import cone stays the cube chapter's.  With `0 < μ`, `0 < c₁`, `0 ≤ τ` and the five
rows

* `(F)`   `c₁(W₁·Fb) ≤ c₁W₁·(I·F(τ) + 4μ²V/(τ+μ)²)`,
* `(fib)` `μ·Fs ≤ μW₁τI + Efib`,
* `(PQ₂)` `½W₂(τ²I+V) ≤ Ps + Epair`,
* `(kin)` `P ≤ sbK`,
* `(bud)` `Efib + Epair ≤ Cerr + W₁·[(τ−μ)²I(½ − c₁μ/(τ+μ)) + V(½ − 4c₁μ²/(τ+μ)²)]
                    + ½(W₂−W₁)(τ²I+V) + P`

one gets `c₁(W₁·Fb) − ½μ²W₁I − Cerr ≤ sbK − μ·Fs + Ps`, where `F(t) = μ(t−μ)²/(t+μ)`.  The extra
`½(W₂−W₁)(τ²I+V)` is the pair-condensate surplus kept by the `W₁`-form of the `F`-row and spent by
`(bud)`. -/
theorem cubeArithDeltaCore {μ c₁ W₁ W₂ I τ V Fb Fs Ps Efib Epair P Cerr sbK : ℝ}
    (hμ : 0 < μ) (hc₁ : 0 < c₁) (hτ : 0 ≤ τ)
    (hF : c₁ * (W₁ * Fb)
        ≤ c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2))
    (hfib : μ * Fs ≤ μ * W₁ * τ * I + Efib)
    (hpair : (1 / 2) * W₂ * (τ ^ 2 * I + V) ≤ Ps + Epair)
    (hkin : P ≤ sbK)
    (hbud : Efib + Epair ≤ Cerr
        + W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2))
        + (1 / 2) * (W₂ - W₁) * (τ ^ 2 * I + V) + P) :
    c₁ * (W₁ * Fb) - (1 / 2) * μ ^ 2 * W₁ * I - Cerr ≤ sbK - μ * Fs + Ps := by
  have hτμ : 0 < τ + μ := by linarith
  -- the exact slack identity, scaled by `W₁`
  have hid : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
        + W₁ * (μ * τ * I)
      = (1 / 2) * W₁ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
        - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
    have h : τ + μ ≠ 0 := ne_of_gt hτμ
    field_simp
    ring
  -- (A) the left-hand side
  have hA : c₁ * (W₁ * Fb) - (1 / 2) * μ ^ 2 * W₁ * I - Cerr
      ≤ (1 / 2) * W₁ * (τ ^ 2 * I + V) - W₁ * (μ * τ * I)
        - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) - Cerr := by
    linarith [hF, hid]
  -- (B) the right-hand side
  have hB : (1 / 2) * W₂ * (τ ^ 2 * I + V) - Epair - Efib + P - μ * W₁ * τ * I
      ≤ sbK - μ * Fs + Ps := by
    linarith [hpair, hfib, hkin]
  linarith [hA, hB, hbud]

theorem perBoxFCube_of_ledgerDelta {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R C μ c₁ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)} {Efib Epair V P : ℝ}
    (hμ : 0 < μ) (hc₁ : 0 < c₁) (hc₁8 : c₁ ≤ 1 / 8)
    (hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    (hW1 : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u)
    (hW12 : Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u
      ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u)
    (hτ : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hV : 0 ≤ V)
    (hF : Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            * (μ * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
                / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
          + 4 * μ ^ 2
              / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2
            * V)
    (hfib : μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + Efib)
    (hpair : (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
          * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + V)
        ≤ Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + Epair)
    (hsplit : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = -(μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hkin : P ≤ Work.BoseFixB1B.sbKinCube v μ u
        (Φ : Submission.BoseGases.X n → ℝ))
    (hbud : Efib + Epair
      ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                  * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + μ * (_root_.BoseGases.a v)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          * ((Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              * (1 / 2 - c₁ * μ
                  / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2
                / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2))
        + (1 / 2)
            * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u
              - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + V)
        + P) :
    Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u := by
  rw [Work.BoseFixB1S.PerBoxFCube, Work.BoseFixB1B.sbWordCube, hsplit]
  have hFb_eq : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
            / Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
      = Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hFb_eq]
  set I : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hIdef
  set τ : ℝ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hτdef
  set W₁ : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₁def
  set W₂ : ℝ := Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₂def
  set Fb : ℝ := Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) with hFbdef
  set Fs : ℝ := Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hFsdef
  set Ps : ℝ := Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hPsdef
  set sbK : ℝ := Work.BoseFixB1B.sbKinCube v μ u
      (Φ : Submission.BoseGases.X n → ℝ) with hsbKdef
  set Cerr : ℝ := C * (μ ^ 2 * (_root_.BoseGases.a v)
        * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (_root_.BoseGases.a v)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) with hCerrdef
  have hI : 0 ≤ I := by rw [hIdef]; exact hN
  have hW₁ : 0 ≤ W₁ := by rw [hW₁def]; exact hW1
  have hW₁₂ : W₁ ≤ W₂ := by rw [hW₁def, hW₂def]; exact hW12
  have hτ' : 0 ≤ τ := by rw [hτdef]; exact hτ
  -- the `F`-row: the conclusion's slot carries the extra factor `W₁`, so scale it here
  have hFtmp : Fb ≤ I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 / (τ + μ) ^ 2 * V := hF
  have hF' : c₁ * (W₁ * Fb)
      ≤ c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hFtmp (mul_nonneg hc₁.le hW₁)
    calc c₁ * (W₁ * Fb) = (c₁ * W₁) * Fb := by ring
      _ ≤ (c₁ * W₁) * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 / (τ + μ) ^ 2 * V) := hh
      _ = c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) := by ring
  have hhgoal := cubeArithDeltaCore (μ := μ) (c₁ := c₁) (W₁ := W₁) (W₂ := W₂) (I := I) (τ := τ)
    (V := V) (Fb := Fb) (Fs := Fs) (Ps := Ps) (Efib := Efib) (Epair := Epair) (P := P)
    (Cerr := Cerr) (sbK := sbK) hμ hc₁ hτ' hF' hfib hpair hkin hbud
  linarith [hhgoal]

end Work.BoseB1Cube
