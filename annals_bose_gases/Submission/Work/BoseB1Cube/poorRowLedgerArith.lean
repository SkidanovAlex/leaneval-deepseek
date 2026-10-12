import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.poorRowLedgerArith` — the pure-real assembly of the **poor row**

This module isolates, in pure real arithmetic, the step by which the *rung*
`Work.BoseB1Cube.boxQSum_ge_sharpInc_bV` and the **matched-constant** port
(`Work.BoseB1Cube.slidingBogPortCubeContDiff`, i.e. FS `lm:appbogolubov` with the prescribed `eps`)
close the residual of `Work.BoseB1Cube.nomRowLinWindowRow` on the **poor half** `n₊ < n/2`, the half
`Work.BoseB1Cube.richRow_holds` does not cover.  See
`FINDING_nomRowLinWindowRow_session7.md` §§1–2.

With `V = bV`, `W = bW`, `S = boxFlatCount`, `Pc = boxPairCount`, `Var := Pc − (S²−S) ≥ 0`,
`n = S + bQ` the particle number, `G = g0w0Mass`, `Xm = chiMass`, `gap = bGapCoeff`,
`cs = bSpectralCube`, `bQ = boxQCount`, the two corpus rows are

* rung  : `A0 + bA2 + ½(M₂/V²)Pc − ¼(W/V²)(Pc + S²−S) − C a(μ + S/V) bQ + boxSqPart ≤ boxQSum`,
* port  : `−[½(1+eps)(G·Xm)(((n+1)n)/V²) + C a(μ + n/V) bQ + C a μ] ≤ cs + bA2`.

Adding the port into the rung's displayed `bA2`, using the pair-square row
`½(M₂−W)(S²−S)/V² ≤ ½(M₂/V²)Pc − ¼(W/V²)(Pc + S²−S)` (the mass gap with the nonnegative `Var`
dropped) and dropping the nonnegative `boxSqPart`, and paying all `bQ`-rows and the constant row by
the **free gate constant** `gap ≥ K a μ`, the residual is the single **core** inequality

    (CORE)  D ≤ A0 + ½(M₂−W)(S²−S)/V² − ½(1+eps)(G·Xm)((n+1)n)/V² + (the credit rows) ,
    D := (1/18) μ (n/V) W .

This module proves that (CORE) plus the stated bookkeeping rows yields the row
`D ≤ gap·bQ + cs + boxQSum`.  The content of (CORE) — the port's `(ε+2Γ)n²`-row against the pair
square's `S²`-row — is the ledger of the FINDING §1.1 and is discharged in the application.
-/

noncomputable section

open scoped Real

set_option autoImplicit false

namespace Work.BoseB1Cube

/-- FS's box `A₀`-main term (`Work.BoseFixB1.a0MainLocBox`), spelled out so that this module needs
nothing beyond Mathlib. -/
def a0MainLocBox' (V μ W S : ℝ) : ℝ :=
  (1 / 4) * (S / V - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W
    - (W / (2 * V)) * (2 * (S / V) + μ) - W / (4 * V ^ 2)

/-- **The poor-row assembly.**  Given the rung, the port, the `bQ`-threshold `1 ≤ K·bQ` (which the
proved pair arm leaves to this branch), the gate `K a μ ≤ gap`, the `K`-bookkeeping row, the
pair-square row and the core inequality (CORE), the node's inequality holds with `cs + boxQSum` in
place of `sbWordCube`. -/
theorem poorRowLedgerArith {μ a V W M2 S Pc Var G Xm n bQ gap cs bA2 boxSqPart A0 boxQSum eps C K : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a)
    (hQ : 0 ≤ bQ) (hn0 : 0 ≤ n) (hbQthr : 1 ≤ K * bQ) (hK : 0 < K) (hboxsq : 0 ≤ boxSqPart)
    (hKa : K * a * μ ≤ gap) (hC : 0 ≤ C)
    (hKC : C * (2 * μ + n / V + S / V) + C * μ * K ≤ K * μ)
    (hcsrow : -((1 / 2) * (1 + eps) * (G * Xm) * (((n + 1) * n) / V ^ 2)
                + C * a * (μ + n / V) * bQ + C * a * μ) ≤ cs + bA2)
    (hrung : A0 + bA2 + (1 / 2) * (M2 / V ^ 2) * Pc - (1 / 4) * (W / V ^ 2) * (Pc + S ^ 2 - S)
              - C * a * (μ + S / V) * bQ + boxSqPart ≤ boxQSum)
    (hhalf : (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
              ≤ (1 / 2) * (M2 / V ^ 2) * Pc - (1 / 4) * (W / V ^ 2) * (Pc + S ^ 2 - S))
    (hcore : (1 / 18) * μ * (n / V) * W
                + C * a * (μ + n / V) * bQ + C * a * μ + C * a * (μ + S / V) * bQ
              ≤ A0 + (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
                - (1 / 2) * (1 + eps) * (G * Xm) * (((n + 1) * n) / V ^ 2)
                + gap * bQ) :
    (1 / 18) * μ * (n / V) * W ≤ gap * bQ + cs + boxQSum := by
  have hμa : 0 ≤ a * μ := mul_nonneg ha (le_of_lt hμ)
  have hCaμ : 0 ≤ C * a * μ := mul_nonneg (mul_nonneg hC ha) (le_of_lt hμ)
  -- the port, substituted into the rung's displayed `bA2`
  have h1 : A0 + (cs + bA2) + (1 / 2) * (M2 / V ^ 2) * Pc
      - (1 / 4) * (W / V ^ 2) * (Pc + S ^ 2 - S) - C * a * (μ + S / V) * bQ + boxSqPart
      ≤ cs + boxQSum := by linarith [hrung]
  have h2 : A0 - ((1 / 2) * (1 + eps) * (G * Xm) * (((n + 1) * n) / V ^ 2)
        + C * a * (μ + n / V) * bQ + C * a * μ)
      + (1 / 2) * (M2 / V ^ 2) * Pc
      - (1 / 4) * (W / V ^ 2) * (Pc + S ^ 2 - S) - C * a * (μ + S / V) * bQ + boxSqPart
      ≤ cs + boxQSum := by linarith [h1, hcsrow]
  have h3 : A0 + (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
      - ((1 / 2) * (1 + eps) * (G * Xm) * (((n + 1) * n) / V ^ 2)
        + C * a * (μ + n / V) * bQ + C * a * μ)
      - C * a * (μ + S / V) * bQ ≤ cs + boxQSum := by linarith [h2, hhalf, hboxsq]
  -- the gate pays every `bQ`-row and the constant row
  have hkey : C * a * (2 * μ + n / V + S / V) + C * a * μ * K ≤ gap := by
    have h1 : C * a * (2 * μ + n / V + S / V) + C * a * μ * K
        = a * (C * (2 * μ + n / V + S / V) + C * μ * K) := by ring
    rw [h1]
    calc a * (C * (2 * μ + n / V + S / V) + C * μ * K) ≤ a * (K * μ) :=
          mul_le_mul_of_nonneg_left hKC ha
      _ = K * a * μ := by ring
      _ ≤ gap := hKa
  have hcredit : C * a * (μ + n / V) * bQ + C * a * μ + C * a * (μ + S / V) * bQ
      ≤ gap * bQ := by
    have h1 : C * a * (μ + n / V) * bQ + C * a * μ + C * a * (μ + S / V) * bQ
        = (C * a * (2 * μ + n / V + S / V)) * bQ + C * a * μ := by ring
    have h2 : C * a * μ ≤ C * a * μ * K * bQ := by
      have hKb := mul_le_mul_of_nonneg_right hbQthr hCaμ
      nlinarith [hKb, hCaμ]
    have h3 : (C * a * (2 * μ + n / V + S / V)) * bQ + C * a * μ * K * bQ ≤ gap * bQ := by
      have h := mul_le_mul_of_nonneg_right hkey hQ
      nlinarith [h]
    linarith [h1, h2, h3]
  linarith [h3, hcore]


/-- **The `hhalf` row of the poor-row assembly, pure algebra.**  From the pair-count Jensen row
`S² − S ≤ Pc` (`Work.BoseB1Cube.sqSubLePairCountOfMoments`) and the trivial `W ≤ 2M₂`
(`Work.BoseB1Cube.bM2_le_two_mul_bW`), the pair-square group dominates `½((M₂−W)/V²)(S²−S)`:

    (1/2)·((M₂−W)/V²)·(S²−S) ≤ (1/2)·(M₂/V²)·Pc − (1/4)·(W/V²)·(Pc + S² − S) .

(Write `Pc = (S²−S) + Var` with `Var ≥ 0`: the difference of the two sides is `(2M₂−W)·Var/(4V²)`.) -/
theorem poorRow_halfRow {M2 W V S Pc : ℝ} (hV : 0 < V)
    (hjen : S ^ 2 - S ≤ Pc) (hW2 : W ≤ 2 * M2) (hVarnn : S ^ 2 - S ≤ Pc) :
    (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
      ≤ (1 / 2) * (M2 / V ^ 2) * Pc - (1 / 4) * (W / V ^ 2) * (Pc + S ^ 2 - S) := by
  have h2 : (0 : ℝ) < V ^ 2 := by positivity
  have hcoef : (0 : ℝ) ≤ (2 * M2 - W) / (4 * V ^ 2) := by
    apply div_nonneg _ (by positivity)
    linarith
  have hdiff : (1 / 2) * (M2 / V ^ 2) * Pc - (1 / 4) * (W / V ^ 2) * (Pc + S ^ 2 - S)
      - (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
      = ((2 * M2 - W) / (4 * V ^ 2)) * (Pc - (S ^ 2 - S)) := by ring
  have hkey : 0 ≤ (2 * M2 - W) / (4 * V ^ 2) * (Pc - (S ^ 2 - S)) :=
    mul_nonneg hcoef (by linarith [hjen])
  linarith [hdiff, hkey]


/-- **`hcore` from the pure core, plus the gate bookkeeping.**  The credits
`C a(μ + n/V)bQ + C a μ + C a(μ + S/V)bQ` are paid by `Kc·a·μ·bQ` (the `hKC` row together with the
threshold `1 ≤ Kg·bQ`), and the gate `Kg·a·μ ≤ gap` turns the core's slack `(Kg−Kc)aμbQ` into the
`gap·bQ` of `poorRowLedgerArith`'s `hcore`.  This is the last link between the pure-real core
(`Work.BoseB1Cube.poorRow_coreArith`) and the landed assembly
(`Work.BoseB1Cube.demand_le_sbWordCube_of_ledgerRows`). -/
theorem poorRow_hcore_of_core {μ a V W M2 S n G Xm eps Gam Kg Kc bQ gap A0 C : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hQ : 0 ≤ bQ) (hC : 0 ≤ C)
    (hKa : Kg * a * μ ≤ gap) (hKg : Kc ≤ Kg) (hbQthr : 1 ≤ Kc * bQ)
    (hKC : C * (2 * μ + n / V + S / V) + C * μ * Kc ≤ Kc * μ)
    (hcore : (1 / 18) * μ * (n / V) * W
              ≤ A0 + (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
                - (1 / 2) * (1 + eps) * (G * Xm) * (((n + 1) * n) / V ^ 2)
                + (Kg - Kc) * a * μ * bQ) :
    (1 / 18) * μ * (n / V) * W + C * a * (μ + n / V) * bQ + C * a * μ
        + C * a * (μ + S / V) * bQ
      ≤ A0 + (1 / 2) * ((M2 - W) / V ^ 2) * (S ^ 2 - S)
        - (1 / 2) * (1 + eps) * (G * Xm) * (((n + 1) * n) / V ^ 2) + gap * bQ := by
  have hCaμ : 0 ≤ C * a * μ := mul_nonneg (mul_nonneg hC ha) (le_of_lt hμ)
  -- the credits are paid by `Kc·a·μ·bQ`
  have hcred : C * a * (μ + n / V) * bQ + C * a * μ + C * a * (μ + S / V) * bQ
      ≤ Kc * a * μ * bQ := by
    have h1 : C * a * (μ + n / V) * bQ + C * a * (μ + S / V) * bQ
        = C * a * (2 * μ + n / V + S / V) * bQ := by ring
    have h2 : C * a * μ ≤ C * a * μ * (Kc * bQ) := by
      have := mul_le_mul_of_nonneg_right hbQthr hCaμ
      nlinarith [this, hCaμ]
    have h3 : C * a * (2 * μ + n / V + S / V) * bQ + C * a * μ * Kc * bQ
        ≤ Kc * a * μ * bQ := by
      have h2' : 0 ≤ a * μ * bQ := by positivity
      nlinarith [hKC, h2', ha, hμ, hQ, hC]
    linarith [h1, h2, h3]
  -- the gate turns the core's slack into `gap·bQ`
  have hslack : Kc * a * μ * bQ ≤ gap * bQ - (Kg - Kc) * a * μ * bQ := by
    have h1 : Kg * a * μ * bQ ≤ gap * bQ := by
      have h2 : 0 ≤ a * μ * bQ := by positivity
      nlinarith [hKa, h2, ha, hμ, hQ]
    nlinarith [h1, hKg, mul_nonneg ha (mul_nonneg (le_of_lt hμ) hQ)]
  linarith [hcore, hcred, hslack]

end Work.BoseB1Cube
