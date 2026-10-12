import ChallengeDeps
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3.Arith.b3HAbsorbRoot_holds` — FS `con:eTdK`, the `n₊^H` absorption

This file proves Step 3 of FS §7 (`Work.BoseFixB3.B3HAbsorbRoot`, `Steps.lean`):
the `n₊^H` error `Kℓ⁻²K_ℓ⁴n₊^H` left over by `cl:advQ3sch` is absorbed by the
*positive* half-budget `(b/200)ε_T(dℓ)⁻²n₊^H` of `eq:ReduceQ3`.

Unfolded, the claim is pure arithmetic on FS's parameters at diluteness
`t = μ(a v)³`:

  `∀ C ≥ 0, ∃ ε₀ > 0, ∀ μ, Adm v ε₀ μ → C·d²·K_ℓ⁴ ≤ (b/200)·ε_T`,

with `d = fsXp t 6 = X⁶`, `K_ℓ = fsXp t (−3/2) = X^{−3/2}`,
`ε_T = fsXp t (23/4) = X^{23/4}` and `X = t^{1/323}`.  The content is that
`d²K_ℓ⁴ = X⁶` is *much smaller* than `ε_T = X^{23/4}` at small diluteness:
in `t`-powers the exponent gap is `6/323 − 23/1292 = 1/1292`, i.e.
`d²K_ℓ⁴ = t^{1/1292}·ε_T`, so the required constant is absorbed by taking
`t ≤ ε₀` with `ε₀` an explicit (astronomically small) power of `1/(3200(C+1))`.

The second case is a formal point: `Adm` does *not* by itself force
`t = μ(a v)³ ≥ 0` (it only asks `t ≤ ε₀`), and for `t < 0` the estimate is
false as stated in the shape `C·|t|^{6/323} ≤ (b/200)|t|^{23/1292}`.  But
`Adm` also carries `ParamsOK (fsParams t) t`, and FS's condition
`con:KellKLd : d^{2M-2} ≪ (μa³)^{1/2}` is *incompatible* with `t < 0`:
Mathlib's `rpow` at a negative base is `exp (log t · y)·cos (πy)`, so
`t^{1/2} = exp (log t/2)·cos (π/2) = 0`, and `con:KellKLd` then reads
`d^{2M-2} ≤ 0`, while `d = t^{6/323} = |t|^{6/323} cos (6π/323) > 0`
(equivalently: `X⁶ > 0`).  Hence `t ≥ 0` for every admissible `μ`, and with
`t = 0` both sides are `0`.

Nothing here is specific to the potential `v`: the statement holds for every
`v : ℝ³ → ℝ`, as claimed.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Arith

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseFixB3 Work.BoseBoxFix Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. `Adm` forces `μ(a v)³ ≥ 0` (`con:KellKLd` is violated for `t < 0`) -/

/-- For negative diluteness `t`, FS's parameter block `fsParams t` violates
`con:KellKLd`: at a negative base `t^{1/2} = exp (log t / 2)·cos (π/2) = 0`
(Mathlib's real power uses `cos (π y)`), so `con:KellKLd` would give
`d^{2M−2} ≤ 0`, whereas `d = t^{6/323} = |t|^{6/323} cos (6π/323) > 0` and
`d` occurs with the positive exponent `2M − 2 = 94`. -/
lemma not_paramsOK_of_neg {t : ℝ} (ht : t < 0) :
    ¬ ParamsOK (fsParams t) t := by
  intro h
  rcases h.KellKLd with ⟨e, he0, heslack, hineq⟩
  -- `t ^ (1/2) = 0` for `t < 0`
  have hz : t ^ (1 / 2 : ℝ) = 0 := by
    rw [Real.rpow_def_of_neg ht]
    have h2 : ((1 : ℝ) / 2) * Real.pi = Real.pi / 2 := by ring
    rw [h2, Real.cos_pi_div_two, mul_zero]
  rw [hz, zero_mul] at hineq
  -- while `d ^ (2M-2) = (t^{6/323})^{94} > 0`
  have hpos : 0 < (fsParams t).d ^ (2 * ((fsParams t).M : ℝ) - 2) := by
    have hd : (fsParams t).d = t ^ (6 / 323 : ℝ) := rfl
    have hM : (2 * ((fsParams t).M : ℝ) - 2 : ℝ) = 94 := by
      show (2 * ((48 : ℕ) : ℝ) - 2) = 94
      norm_num
    rw [hd, hM]
    apply Real.rpow_pos_of_pos
    rw [Real.rpow_def_of_neg ht]
    have h1 : 0 < Real.cos ((6 : ℝ) / 323 * Real.pi) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    positivity
  linarith

/-! ## 2. The step -/

theorem b3HAbsorbRoot_holds (v : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseFixB3.B3HAbsorbRoot v := by
  intro C hC
  -- the explicit threshold: `t^{1/1292} ≤ 1/(3200(C+1))` is enough, and it
  -- follows from `t ≤ ε₀` for this `ε₀`
  refine ⟨(1 / (3200 * (C + 1))) ^ (1292 : ℕ), by positivity, ?_⟩
  intro μ hAdm
  obtain ⟨hμ, htε, hPOK⟩ := hAdm
  rw [patAt_b, patAt_d, patAt_Kl, patAt_eT]
  by_cases ht : μ * a v ^ 3 < 0
  · -- not admissible: `con:KellKLd` fails
    exact absurd hPOK (not_paramsOK_of_neg ht)
  · rw [not_lt] at ht
    rcases eq_or_lt_of_le ht with h0 | hpos
    · -- `t = 0`: both sides vanish
      rw [← h0]
      simp [fsXp]
    · -- `t > 0`: `d²K_ℓ⁴ = t^{1/1292}·ε_T`, and `t^{1/1292}` is small
      have hpow1 : (fsXp (μ * a v ^ 3) 6) ^ 2 = fsXp (μ * a v ^ 3) 12 := by
        rw [fsXp_pow hpos.le]; norm_num
      have hpow2 : (fsXp (μ * a v ^ 3) (-(3 / 2))) ^ 4 = fsXp (μ * a v ^ 3) (-6) := by
        rw [fsXp_pow hpos.le]; norm_num
      have hmul : fsXp (μ * a v ^ 3) 12 * fsXp (μ * a v ^ 3) (-6) = fsXp (μ * a v ^ 3) 6 := by
        rw [fsXp_mul hpos]; norm_num
      have hsplit : fsXp (μ * a v ^ 3) (1 / 4) * fsXp (μ * a v ^ 3) (23 / 4)
          = fsXp (μ * a v ^ 3) 6 := by
        rw [fsXp_mul hpos]; norm_num
      rw [hpow1, hpow2, mul_assoc, hmul, ← hsplit,
        show bValue / 200 = 1 / 3200 by norm_num [bValue]]
      have hE : 0 ≤ fsXp (μ * a v ^ 3) (23 / 4) := fsXp_nonneg hpos.le
      have hkey : C * fsXp (μ * a v ^ 3) (1 / 4) ≤ 1 / 3200 := by
        have hq : fsXp (μ * a v ^ 3) (1 / 4) = (μ * a v ^ 3) ^ (1 / 1292 : ℝ) := by
          unfold fsXp
          norm_num
        rw [hq]
        have hKpos : (0 : ℝ) < 1 / (3200 * (C + 1)) := by positivity
        have hle1 : (μ * a v ^ 3) ^ (1 / 1292 : ℝ)
            ≤ ((1 / (3200 * (C + 1)) : ℝ) ^ (1292 : ℕ)) ^ (1 / 1292 : ℝ) :=
          Real.rpow_le_rpow hpos.le htε (by norm_num)
        have hval : ((1 / (3200 * (C + 1)) : ℝ) ^ (1292 : ℕ)) ^ (1 / 1292 : ℝ)
            = 1 / (3200 * (C + 1)) := by
          rw [← Real.rpow_natCast (1 / (3200 * (C + 1))) 1292,
            ← Real.rpow_mul hKpos.le]
          norm_num
        rw [hval] at hle1
        calc C * (μ * a v ^ 3) ^ (1 / 1292 : ℝ)
            ≤ C * (1 / (3200 * (C + 1))) := mul_le_mul_of_nonneg_left hle1 hC
          _ ≤ (C + 1) * (1 / (3200 * (C + 1))) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 1 / 3200 := by field_simp
      calc C * (fsXp (μ * a v ^ 3) (1 / 4) * fsXp (μ * a v ^ 3) (23 / 4))
          = (C * fsXp (μ * a v ^ 3) (1 / 4)) * fsXp (μ * a v ^ 3) (23 / 4) := by ring
        _ ≤ (1 / 3200) * fsXp (μ * a v ^ 3) (23 / 4) :=
            mul_le_mul_of_nonneg_right hkey hE

end Work.BoseFixB3.Arith
