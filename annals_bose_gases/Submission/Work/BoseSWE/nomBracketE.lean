import ChallengeDeps
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.nomBracketE` — the scalar bookkeeping of the `E`-route's descent

Subproject `BoseSWE` (the small-window hole-free route with the vanishing slack
`ErrE v C μ n = C·(a v)·μ·n·d^80`).  This module contains the **slack arithmetic** of FS's
`n = m·n₀ + n''` grouping (`final_v2.tex` ll. 3990–4055) as it is used by the `E`-twin
`Work.BoseSWE.nomRow_descentStepE`:

* `ErrE_nonneg`, `ErrE_mono` — the slack is nonnegative and monotone in the particle number
  (`ErrE` is `n`-linear with a nonnegative coefficient), so that `m·ErrE(n₀) ≤ ErrE(m·n₀ + n'')`;
* `nomBracket_le_groupBracketE` — the `E`-version of the PROVED
  `Work.BoseB1Cube.nomBracket_le_groupBracket`: the twin's inequality plus the superadditivity of
  the slack.  The slack is *not* multiplied by the state's `L²`-mass in this scalar step: it enters
  as the constant `ErrE(n)` on the left and `ErrE(n₀)` inside the group row `G₁`;
* `PerBoxFNomE_iff_row` — `PerBoxFNomE` is `perBoxRow` minus `ErrE·‖Φ‖²` (definitional).

Everything here is `sorry`-free and rests on the PROVED `Work.BoseB1Cube` twin only.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- The slack `ErrE v CE μ n = CE·(a v)·μ·n·d^80` is nonnegative (all four factors are). -/
theorem ErrE_nonneg {v : E3 → ℝ} {CE μ : ℝ} {n : ℕ} (hCE : 0 ≤ CE)
    (hav : 0 ≤ _root_.BoseGases.a v) (hμ : 0 ≤ μ) : 0 ≤ ErrE v CE μ n := by
  unfold ErrE
  have hd : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCE hav) hμ) (Nat.cast_nonneg n)) hd

/-- The slack is monotone in the particle number: `ErrE` is `n`-linear with a nonnegative
coefficient.  In particular `m·ErrE v CE μ n₀ ≤ ErrE v CE μ (m·n₀ + n'')`. -/
theorem ErrE_mono {v : E3 → ℝ} {CE μ : ℝ} {n m : ℕ} (hCE : 0 ≤ CE)
    (hav : 0 ≤ _root_.BoseGases.a v) (hμ : 0 ≤ μ) (hnm : n ≤ m) :
    ErrE v CE μ n ≤ ErrE v CE μ m := by
  unfold ErrE
  have hd : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by positivity
  have hcoef : 0 ≤ CE * _root_.BoseGases.a v * μ * (Work.BoseFixB1.bD v μ) ^ 80 :=
    mul_nonneg (mul_nonneg (mul_nonneg hCE hav) hμ) hd
  have hle : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  calc CE * _root_.BoseGases.a v * μ * (n : ℝ) * (Work.BoseFixB1.bD v μ) ^ 80
      = (CE * _root_.BoseGases.a v * μ * (Work.BoseFixB1.bD v μ) ^ 80) * (n : ℝ) := by ring
    _ ≤ (CE * _root_.BoseGases.a v * μ * (Work.BoseFixB1.bD v μ) ^ 80) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hle hcoef
    _ = CE * _root_.BoseGases.a v * μ * (m : ℝ) * (Work.BoseFixB1.bD v μ) ^ 80 := by ring

/-- **The `E`-version of `Work.BoseB1Cube.nomBracket_le_groupBracket`.**

With `N = m·n₀ + n''`, the bracket of the nominal row at the full density `N/V`, *with the slack
`CE·av·μ·N·d80` subtracted*, is dominated by the two group rows of the descent — the first of which
carries the slack `CE·av·μ·n₀·d80` at the group size:

    c₁·W·ψ(1,μ,N/V) − ½μ²W − E − CE·av·μ·N·d80
      ≤ m·[(1/18)μ(n₀/V)W − CE·av·μ·n₀·d80] + ([¼(n''/V − μ)² − ½μ²]W − E) ,   c₁ = 1/40 .

This is the twin `nomBracket_le_groupBracket` plus the superadditivity of the slack
(`m·n₀ ≤ N`, everything else nonnegative). -/
theorem nomBracket_le_groupBracketE {μ V W E Cn CE av d80 : ℝ} {n₀ n'' m : ℕ}
    (hμ : 0 < μ) (hV : 0 < V) (hW : 0 ≤ W) (hCn : 2 ≤ Cn) (hCnμV : Cn * μ * V ≤ (n₀ : ℝ))
    (hnr : (n'' : ℝ) < (n₀ : ℝ)) (hCE : 0 ≤ CE) (hav : 0 ≤ av) (hd80 : 0 ≤ d80) :
    (1 / 40) * (W * Work.SmallBoxSliding.psiWeight 1 μ ((((m * n₀ + n'' : ℕ) : ℝ) / V)))
        - (1 / 2) * μ ^ 2 * W - E
        - CE * av * μ * ((((m * n₀ + n'' : ℕ) : ℝ))) * d80
      ≤ (m : ℝ) * ((1 / 18) * μ * ((n₀ : ℝ) / V) * W - CE * av * μ * (n₀ : ℝ) * d80)
        + (((1 / 4) * (((n'' : ℝ) / V) - μ) ^ 2 - (1 / 2) * μ ^ 2) * W - E) := by
  have hbase := Work.BoseB1Cube.nomBracket_le_groupBracket (μ := μ) (V := V) (W := W) (E := E)
    (Cn := Cn) (n₀ := n₀) (n'' := n'') (m := m) hμ hV hW hCn hCnμV hnr
  have hcast : (((m * n₀ + n'' : ℕ) : ℝ)) = (m : ℝ) * (n₀ : ℝ) + (n'' : ℝ) := by push_cast; ring
  have hle : (m : ℝ) * (n₀ : ℝ) ≤ (((m * n₀ + n'' : ℕ) : ℝ)) := by
    rw [hcast]; linarith [show (0 : ℝ) ≤ (n'' : ℝ) by positivity]
  have hcoef : 0 ≤ CE * av * μ * d80 :=
    mul_nonneg (mul_nonneg (mul_nonneg hCE hav) hμ.le) hd80
  have hslack : (m : ℝ) * (CE * av * μ * (n₀ : ℝ) * d80)
      ≤ CE * av * μ * ((((m * n₀ + n'' : ℕ) : ℝ))) * d80 := by
    calc (m : ℝ) * (CE * av * μ * (n₀ : ℝ) * d80)
        = (CE * av * μ * d80) * ((m : ℝ) * (n₀ : ℝ)) := by ring
      _ ≤ (CE * av * μ * d80) * (((m * n₀ + n'' : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hle hcoef
      _ = CE * av * μ * ((((m * n₀ + n'' : ℕ) : ℝ))) * d80 := by ring
  linarith [hbase, hslack]

/-- `PerBoxFNomE` is exactly `perBoxRow` with the slack `ErrE v CE μ n·‖Φ‖²` subtracted from the
left-hand side (definitional; the extra term of `PerBoxFNomE` over `Work.BoseB1Cube.PerBoxFNom`). -/
theorem PerBoxFNomE_iff_row {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C CE μp μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))} {u : E3} :
    PerBoxFNomE v h R c₁ C CE μp μ n Φ u
      ↔ Work.BoseB1Cube.perBoxRow v h R c₁ C μp μ n Φ u
          - ErrE v CE μ n * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  unfold PerBoxFNomE Work.BoseB1Cube.perBoxRow
  constructor <;> intro hh <;> linarith

end Work.BoseSWE
