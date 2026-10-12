import ChallengeDeps
import Submission.Work.BoseFixR.BogZeroPointLeHalfMul
import Submission.Work.BoseFixR.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarZSumHalf.lean` — the (‡)-summation of the `FarResidAdm` assembly

Step (‡)+(d) of `FINDING_FarResidAdm_S3.md` §2: at the `ε`-split environment
`E' = farEnv E v μ ρ` the per-pair zero point of FS `eq:Rough2` is*split off* from the
denominator of the cheap Taylor bound, so that the result depends on the weight `Ŵ₁`
only through the **single** combination `Σ_k Ŵ₁(k)²/𝒜₁(k)` with

    𝒜₁(k) = (1−ε)·τ_k + ρ·ε^{−1/2}·a    ("the ε-split diagonal, without ℬ"),
    ℬ_k   = ρ·Ŵ₁(k)                       (the pairing),

i.e. `𝒜_k = 𝒜₁(k) + ℬ_k`.  This is what lets the `κ`-optimised estimate (`SumSqDivLe`)
control the whole slot.

The per-`k` input is `Work.BoseFixR.BogZeroPointLeHalfMul`:

    bogZeroPoint (𝒜₁+ℬ) ℬ ≤ (1/2 + 64√ε)·ℬ²/𝒜₁  (0 < 𝒜₁, |ℬ| ≤ 16π√ε·𝒜₁) .

The hypothesis `|ℬ| ≤ 16π√ε·𝒜₁` is exactly what `hW1` (`|Ŵ₁(k)| ≤ 16π·a`) and
`𝒜₁(k) ≥ ρ·ε^{−1/2}·a` give:  `16π√ε·𝒜₁ ≥ 16π√ε·ρ ε^{−1/2}a = 16πρa ≥ |ℬ_k|`.

**The sign is essential and is why the bound carries `√ε` and not `ε`** (reviewer of
`BogZeroPointLeHalfMul`: for `t = ℬ/𝒜₁ < 0` the identity
`bogZeroPoint = 𝒜₁t²f(t)`, `f(t) = 1/(1+t+√(1+2t)) = 1/2 − t/2 + 5t²/8 − …` gives the
`+O(√ε)` term, not `+O(ε)`).  Harmless: the final constant is `1/4 + 32√ε ≤ 1/4 + o(1)`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `A`-field of `KzEnvAt (farEnv E v μ ρ) ρ` is the `ε`-split diagonal. -/
@[simp] lemma KzEnvAt_farEnv_A' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (KzEnvAt (farEnv E v μ ρ) ρ).A k
      = (1 - epsFar v μ ρ) * E.tau k + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v
        + ρ * E.W1 k := rfl

/-- The `B`-field of `KzEnvAt (farEnv E v μ ρ) ρ` is the pairing `ℬ_k = ρŴ₁(k)`. -/
@[simp] lemma KzEnvAt_farEnv_B' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (KzEnvAt (farEnv E v μ ρ) ρ).B k = ρ * E.W1 k := rfl

/-- **The (‡)-summation.**  The sum of the per-pair zero points of the `ε`-split pair form
is at most `ρ²(1/4 + 32√ε)` times the *single* weighted lattice sum
`Σ_k Ŵ₁(k)²/𝒜₁(k)`.

The hypotheses are the ones the consumer supplies: `0 < ε ≤ 10^{-8}` (the `ε`-smallness of
FS `eq:ChoiceEpsilon`), `0 < ρ`, `0 < a`, positivity of the diagonal part `𝒜₁`, and the
per-sample bound `|Ŵ₁(k)| ≤ 16πa` (`hW1` of the target). -/
theorem sum_half_bogZeroPoint_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ)
    (hε0 : 0 ≤ epsFar v μ ρ) (hε1 : epsFar v μ ρ ≤ 1 / 10 ^ 8)
    (hεpos : 0 < epsFar v μ ρ) (hρ : 0 < ρ) (ha : 0 < a v)
    (hτ : ∀ k : Mode, 0 ≤ (1 - epsFar v μ ρ) * E.tau k)
    (hW1 : ∀ k : Mode, |E.W1 k| ≤ 16 * Real.pi * a v) :
    (∑ k : Mode, (1 / 2 : ℝ) *
        Work.BoseB6.bogZeroPoint ((KzEnvAt (farEnv E v μ ρ) ρ).A k)
          ((KzEnvAt (farEnv E v μ ρ) ρ).B k))
      ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
          * ∑ k : Mode, (E.W1 k) ^ 2
              / ((1 - epsFar v μ ρ) * E.tau k
                  + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v) := by
  set ε := epsFar v μ ρ with hεdef
  have hεsqrt0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  -- the positive diagonal part `𝒜₁(k)`
  have hA1pos : ∀ k : Mode, 0 < (1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v := by
    intro k
    have h1 : 0 < ρ * ε ^ (-(1 / 2 : ℝ)) * a v := by
      refine mul_pos (mul_pos hρ ?_) ha
      exact Real.rpow_pos_of_pos hεpos _
    linarith [hτ k]
  -- `|ℬ_k| ≤ 16π√ε·𝒜₁(k)`
  have hB : ∀ k : Mode, |ρ * E.W1 k|
      ≤ 16 * Real.pi * Real.sqrt ε
          * ((1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v) := by
    intro k
    have hWk := hW1 k
    have hA1 := hA1pos k
    -- `16π√ε·(ρε^{-1/2}a) = 16πρa`
    have hkey : 16 * Real.pi * Real.sqrt ε * (ρ * ε ^ (-(1 / 2 : ℝ)) * a v)
        = 16 * Real.pi * ρ * a v := by
      have h1 : Real.sqrt ε * ε ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_add hεpos]
        norm_num
      calc 16 * Real.pi * Real.sqrt ε * (ρ * ε ^ (-(1 / 2 : ℝ)) * a v)
          = 16 * Real.pi * ρ * a v * (Real.sqrt ε * ε ^ (-(1 / 2 : ℝ))) := by ring
        _ = 16 * Real.pi * ρ * a v := by rw [h1, mul_one]
    have h2 : |ρ * E.W1 k| ≤ 16 * Real.pi * ρ * a v := by
      rw [abs_mul, abs_of_pos hρ]
      have h3 : ρ * |E.W1 k| ≤ ρ * (16 * Real.pi * a v) :=
        mul_le_mul_of_nonneg_left hWk hρ.le
      calc ρ * |E.W1 k| ≤ ρ * (16 * Real.pi * a v) := h3
        _ = 16 * Real.pi * ρ * a v := by ring
    have h4 : 16 * Real.pi * ρ * a v
        ≤ 16 * Real.pi * Real.sqrt ε
            * ((1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v) := by
      rw [← hkey]
      exact mul_le_mul_of_nonneg_left (by linarith [hτ k])
        (mul_nonneg (by positivity) hεsqrt0)
    linarith [h2, h4]
  -- the per-`k` Taylor bound
  have hpt : ∀ k : Mode,
      (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          ((1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v + ρ * E.W1 k) (ρ * E.W1 k)
        ≤ ρ ^ 2 * (1 / 4 + 32 * Real.sqrt ε) * (E.W1 k) ^ 2
            / ((1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v) := by
    intro k
    set A1 := (1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v with hA1def
    have h := BogZeroPointLeHalfMul (A1 := A1) (B := ρ * E.W1 k) (ε := ε)
      (hA1pos k) hε0 hε1 (hB k)
    have hBsq : (ρ * E.W1 k) ^ 2 = ρ ^ 2 * (E.W1 k) ^ 2 := by ring
    calc (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (A1 + ρ * E.W1 k) (ρ * E.W1 k)
        ≤ (1 / 2 : ℝ) * ((1 / 2 + 64 * Real.sqrt ε) * (ρ * E.W1 k) ^ 2 / A1) := by
          linarith [h]
      _ = ρ ^ 2 * (1 / 4 + 32 * Real.sqrt ε) * (E.W1 k) ^ 2 / A1 := by
          rw [hBsq]; ring
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => hpt k)
  have hrew : (∑ k : Mode, (1 / 2 : ℝ) *
        Work.BoseB6.bogZeroPoint ((KzEnvAt (farEnv E v μ ρ) ρ).A k)
          ((KzEnvAt (farEnv E v μ ρ) ρ).B k))
      = ∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
          ((1 - ε) * E.tau k + ρ * ε ^ (-(1 / 2 : ℝ)) * a v + ρ * E.W1 k)
          (ρ * E.W1 k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [KzEnvAt_farEnv_A', KzEnvAt_farEnv_B', hεdef]
  rw [hrew]
  refine le_trans hsum ?_
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  ring

end Work.BoseFixR
