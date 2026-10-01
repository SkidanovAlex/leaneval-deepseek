import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.ZeroDensity.Basic
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.logFreeFamHalfOfNonPrincipal
import Submission.Work.LinnikAreas.logFreeFamHeightOfNonPrincipal
import Submission.Work.LinnikAreas.principalCountIn_le_rpow

/-!
# The log-free family count with exponent `2.61`, from Jutila's and Montgomery's estimates

## Why `2.61`

AREA 6 consumes the family zero count in exactly two shapes,
`Work.ZeroDensity.LogFreeFamHalf c₃` (height `1`, the working region `|Im ρ| ≤ 1` of the
Deuring--Heilbronn argument) and `Work.ZeroDensity.LogFreeFamHeight c₃ c₃'` (general height, the
far-height mass), with

* the **Deuring--Heilbronn** part needing `c₃ + 1/c_r < 49/10` for the repulsion constant
  `c_r = 7/16` of `Work.LinnikAreas.repulsionWithCap_7_16`, i.e. `c₃ < 49/10 - 16/7 = 343/70`;
* the **far-height** part (`RestHighFree`, `RestHighBGTZGenC`) needing `c₃ < 49/10` and
  `c₃' < 2`.

The historical choice `c₃ = 5/2 = 2.5` (with `c₃' = 3/2`) meets this with a comfortable margin,
and `Work.LinnikAreas.logFreeFamHalfOfNonPrincipal` / `...logFreeFamHeightOfNonPrincipal` obtain it
from **Jutila's** theorem on `σ ≥ 4/5` together with **Huxley's** `12/5` family estimate on
`σ ≤ 4/5`.  The value `c₃ = 5/2` is *exactly* `12/5 + 1/10`: Huxley's log-free estimate at
`ε = 1/10` furnishes the whole range `σ ≤ 4/5` with the exponent `(5/2)(1-σ)`, which is precisely
the requirement, and the tight point is `σ = 4/5`, where the required coefficient is exactly `5/2`
while Montgomery's sharp large-sieve estimate `3/(2-σ) + ε` has coefficient `> 5/2` *for every*
`σ < 4/5` once its `ε > 0` (and `= 5/2` only at `σ = 4/5` with `ε = 0`, which is not available).

**This file removes Huxley from that role.**  The point is that the consumers tolerate a *strictly
larger* coefficient `c₃ = 261/100 = 2.61`:

`261/100 + 16/7 = 3427/700 = 4.8957… < 49/10 = 3430/700`  (margin `3/700`),

and `261/100 < 49/10`.  With the target coefficient raised from `2.5` to `2.61`, Montgomery's
sharp estimate *does* cover `σ ≤ 4/5` — at `σ = 4/5` its coefficient is `5/2 + 1/100 = 2.51 < 2.61`,
leaving `0.1·(1/5) = 0.02` of exponent budget for its logarithmic power — and Jutila's theorem
covers `σ ≥ 4/5` as before, while the σ-blind count covers the far range `σ ≤ 3/5`.

## The three ranges

| range | input | exponent of `q` |
|---|---|---|
| `σ ≤ 3/5` | `Work.ZeroDensity.trivial_bound` | `1 + 1/50 = 1.02 ≤ (261/100)(1-σ)` |
| `3/5 ≤ σ ≤ 4/5` | Montgomery `MontgomerySharp (1/1000)` at `ε = 1/100` | `3(1-σ)/(2-σ) + 1/100 + 1/1000 ≤ (261/100)(1-σ)` |
| `σ ≥ 4/5` | Jutila (`FamilyZeroDensityJutilaNP`) + the principal character | `(2 + 1/100)(1-σ) ≤ (261/100)(1-σ)` |

The middle range is the crux: `3(1-σ)/(2-σ) ≤ 5/2` on `σ ≤ 4/5` (equality at `σ = 4/5`), so with
the additive `1/100` of Montgomery and the `1/1000` spent on `(log qT)^{1/1000} ≤ (qT)^{1/1000}`
(which holds since `log x ≤ x` for `x ≥ 1`) one needs `0.011 ≤ (261/100 - 5/2)(1-σ) = 0.11(1-σ)`,
i.e. `1 - σ ≥ 0.1` — true because `σ ≤ 4/5`.

The `T`-exponent never exceeds `3/2`: on the middle range `3(1-σ)/(2-σ) + 0.011 ≤ 1` (because
`σ ≥ 3/5` gives `1-σ ≤ 2/5` and `2-σ ≥ 6/5`), and Jutila's `T`-exponent is
`(201/100)(1-σ) ≤ 201/500 ≤ 3/2` on `σ ≥ 4/5`.

## Consequences

`logFreeFamHalf_of_jutila_montgomery` and `logFreeFamHeight_of_jutila_montgomery` below give
`LogFreeFamHalf (261/100)` and `LogFreeFamHeight (261/100) (3/2)` from Jutila plus Montgomery
**alone** — no Huxley.  The two `↔`-free consequences `..._of_huxley` record that the same
statements follow from the historical pair `(Jutila, Huxley)` as well (a larger coefficient is a
weaker hypothesis, so `LogFreeFamHalf (5/2) → LogFreeFamHalf (261/100)`), which makes every
consumer of this module usable with either input.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.ZeroDensity (famCount)

/-- `x ^ y = exp (y log x)` for `x > 0`, in the factor order used by `LogFreeFamHalf`. -/
theorem rpow_eq_exp' {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = Real.exp (y * Real.log x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

/-- **The family zero count with coefficient `261/100`, from Jutila and Montgomery.**

For every `q ≥ 2`, `0 ≤ σ ≤ 1`, `T ≥ 1`,

`Σ_{χ mod q} N(σ,T,χ) ≤ C·q^{(261/100)(1-σ)}·T^{3/2}`,

with a constant `C` independent of `q`, `σ`, `T`.  The three σ-ranges are
`Work.ZeroDensity.trivial_bound`, `Work.ZeroDensity.MontgomerySharp (1/1000)` (at `ε = 1/100`) and
Jutila's non-principal theorem `FamilyZeroDensityJutilaNP` (at `ε = 1/100`) together with the
`T^{3/2}` bound for the principal character (`principalCountIn_le_rpow`). -/
theorem famCount_le_qpow_of_jutila_montgomery
    (hJ : FamilyZeroDensityJutilaNP) (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ),
      0 ≤ σ → σ ≤ 1 → 1 ≤ T →
        famCount q σ T
          ≤ C * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by
  obtain ⟨Cm, hCm, hM'⟩ := hM (1 / 100) (by norm_num)
  obtain ⟨CJ, hCJ, hJ'⟩ := hJ (1 / 100) (by norm_num)
  obtain ⟨Ct, hCt, ht⟩ := Work.ZeroDensity.trivial_bound (1 / 50) (by norm_num)
  obtain ⟨Cz, hCz, hz⟩ := principalCountIn_le_rpow
  refine ⟨max (max Cm CJ) Ct + Cz + 1, by positivity, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hqTpos : (0 : ℝ) < (q : ℝ) * T := by nlinarith
  have hQnn : (0 : ℝ) ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hqpos.le _) (Real.rpow_nonneg hTpos.le _)
  have hCqpow : (1 : ℝ) ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) :=
    Real.one_le_rpow hq1 (mul_nonneg (by norm_num) (by linarith))
  -- the two inputs at `ε = 1/100`, `T = 1` / general `T`, and the principal character
  have hfinal : ∀ {A : ℝ}, A ≤ max (max Cm CJ) Ct + Cz + 1 →
      A * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2))
        ≤ (max (max Cm CJ) Ct + Cz + 1)
            * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
    fun hA => mul_le_mul_of_nonneg_right hA hQnn
  have hCtle : Ct ≤ max (max Cm CJ) Ct + Cz + 1 := by
    have h1 : Ct ≤ max (max Cm CJ) Ct := le_max_right _ _
    linarith
  have hCmle : Cm ≤ max (max Cm CJ) Ct + Cz + 1 := by
    have h1 : Cm ≤ max Cm CJ := le_max_left _ _
    have h2 : max Cm CJ ≤ max (max Cm CJ) Ct := le_max_left _ _
    linarith
  have hCJzle : CJ + Cz ≤ max (max Cm CJ) Ct + Cz + 1 := by
    have h1 : CJ ≤ max Cm CJ := le_max_right _ _
    have h2 : max Cm CJ ≤ max (max Cm CJ) Ct := le_max_left _ _
    linarith
  rcases le_total σ (3 / 5) with hσtriv | hσtriv
  · -- ## `σ ≤ 3/5`: the σ-blind count
    have h := ht q hq σ T hσ0 hσ1 hT
    have hq58 : (1 - σ) * (261 / 100) ≥ 51 / 50 := by nlinarith [hσtriv]
    have hqle : (q : ℝ) ^ ((51 : ℝ) / 50) ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hTle : T ^ ((51 : ℝ) / 50) ≤ T ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    rw [show (1 : ℝ) + 1 / 50 = (51 : ℝ) / 50 by norm_num] at h
    rw [Real.mul_rpow hqpos.le hTpos.le] at h
    refine le_trans h ?_
    have hstep : ((q : ℝ) ^ ((51 : ℝ) / 50) * T ^ ((51 : ℝ) / 50))
        ≤ ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
      mul_le_mul hqle hTle (Real.rpow_nonneg hTpos.le _) (Real.rpow_nonneg hqpos.le _)
    calc Ct * ((q : ℝ) ^ ((51 : ℝ) / 50) * T ^ ((51 : ℝ) / 50))
        ≤ Ct * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hCt)
      _ ≤ _ := hfinal hCtle
  rcases le_total σ (4 / 5) with hσmid | hσmid
  · -- ## `3/5 ≤ σ ≤ 4/5`: Montgomery's sharp large-sieve estimate at `ε = 1/100`
    have h := hM' q hq σ T (by linarith) hσ1 hT
    have hlogpow : (Real.log ((q : ℝ) * T)) ^ ((1 : ℝ) / 1000)
        ≤ ((q : ℝ) * T) ^ ((1 : ℝ) / 1000) :=
      Real.rpow_le_rpow (x := Real.log ((q : ℝ) * T)) (y := (q : ℝ) * T) (z := (1 : ℝ) / 1000)
        (Real.log_nonneg hqT1) (Real.log_le_self hqTpos.le) (by norm_num)
    have hden : (0 : ℝ) < 2 - σ := by linarith
    -- exponent bookkeeping: `3/(2-σ) ≤ 5/2` (equality at `σ = 4/5`), hence
    -- `3(1-σ)/(2-σ) + 1/100 + 1/1000 ≤ (261/100)(1-σ)`
    have hcoef : 3 / (2 - σ) ≤ 5 / 2 := by
      rw [div_le_iff₀ hden]
      linarith
    have hexp1 : 3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000
        ≤ ((261 : ℝ) / 100) * (1 - σ) := by
      have h1 : 3 * (1 - σ) / (2 - σ) = (3 / (2 - σ)) * (1 - σ) := by ring
      have h1m : (0 : ℝ) ≤ 1 - σ := by linarith
      have hcf : (3 / (2 - σ)) * (1 - σ) ≤ (5 / 2) * (1 - σ) :=
        mul_le_mul_of_nonneg_right hcoef h1m
      have h2 : (5 / 2 : ℝ) * (1 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000
          ≤ ((261 : ℝ) / 100) * (1 - σ) := by
        have h3 : (1 : ℝ) ≤ 10 * (1 - σ) := by linarith
        nlinarith
      rw [h1]
      linarith
    have hexp2 : 3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000 ≤ (3 : ℝ) / 2 := by
      have h1 : 3 * (1 - σ) / (2 - σ) ≤ 1 := by
        rw [div_le_one hden]
        linarith
      linarith
    -- absorb the logarithmic power into the `1/1000` of slack
    have hmain : Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100)
          * (Real.log ((q : ℝ) * T)) ^ ((1 : ℝ) / 1000)
        ≤ Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000) := by
      have hAX : (0 : ℝ) ≤ Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100) :=
        mul_nonneg (le_of_lt hCm) (Real.rpow_nonneg (le_of_lt hqTpos) _)
      have h1 := mul_le_mul_of_nonneg_left hlogpow hAX
      calc Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100)
            * (Real.log ((q : ℝ) * T)) ^ ((1 : ℝ) / 1000)
          ≤ Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100)
            * ((q : ℝ) * T) ^ ((1 : ℝ) / 1000) := h1
        _ = Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000) := by
              rw [mul_assoc, ← Real.rpow_add hqTpos]
    -- compare the two exponents with the target ones
    have hqle : (q : ℝ) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000)
        ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp1
    have hTle : T ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000)
        ≤ T ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hT hexp2
    have hstep : ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000)
        ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hTpos)]
      exact mul_le_mul hqle hTle (Real.rpow_nonneg (le_of_lt hTpos) _)
        (Real.rpow_nonneg (le_of_lt hqpos) _)
    calc famCount q σ T
        ≤ Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100)
          * (Real.log ((q : ℝ) * T)) ^ ((1 : ℝ) / 1000) := h
      _ ≤ Cm * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000) := hmain
      _ ≤ Cm * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hstep (le_of_lt hCm)
      _ ≤ _ := hfinal hCmle
  · -- ## `σ ≥ 4/5`: Jutila for the non-principal characters, `T^{3/2}` for the principal one
    have hsplit := famCount_eq_erase_add (q := q) σ T
    rw [hsplit]
    have hnp := hJ' q hq σ T (by linarith) hσ1 hT
    have hpr := hz q hq σ T hσ0 hσ1 hT
    have hexp : (2 : ℝ) + 1 / 100 = (201 : ℝ) / 100 := by norm_num
    rw [hexp] at hnp
    -- the non-principal part
    have hnpQ : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
        ≤ CJ * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by
      refine le_trans hnp ?_
      rw [Real.mul_rpow hqpos.le hTpos.le]
      have hexp1 : (201 : ℝ) / 100 * (1 - σ) ≤ ((261 : ℝ) / 100) * (1 - σ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
      have hexp2 : (201 : ℝ) / 100 * (1 - σ) ≤ (3 : ℝ) / 2 := by
        have h : (1 - σ) ≤ 1 / 5 := by linarith
        nlinarith
      have hqle : (q : ℝ) ^ ((201 : ℝ) / 100 * (1 - σ))
          ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hexp1
      have hTle : T ^ ((201 : ℝ) / 100 * (1 - σ)) ≤ T ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hT hexp2
      have hstep : (q : ℝ) ^ ((201 : ℝ) / 100 * (1 - σ)) * T ^ ((201 : ℝ) / 100 * (1 - σ))
          ≤ (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2) :=
        mul_le_mul hqle hTle (Real.rpow_nonneg hTpos.le _) (Real.rpow_nonneg hqpos.le _)
      exact mul_le_mul_of_nonneg_left hstep (le_of_lt hCJ)
    have hprQ : zeroCountIn (1 : DirichletCharacter ℂ q) σ T
        ≤ Cz * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by
      refine le_trans hpr (mul_le_mul_of_nonneg_left ?_ (le_of_lt hCz))
      exact le_mul_of_one_le_left (Real.rpow_nonneg hTpos.le _) hCqpow
    calc (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
          + zeroCountIn (1 : DirichletCharacter ℂ q) σ T
        ≤ CJ * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2))
          + Cz * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          add_le_add hnpQ hprQ
      _ = (CJ + Cz) * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ _ := hfinal hCJzle

/-- `LogFreeFamHeight` is monotone in its two exponents. -/
theorem LogFreeFamHeight_mono {e1 e2 e3 e4 : ℝ} (h12 : e1 ≤ e2) (h34 : e3 ≤ e4)
    (h : Work.ZeroDensity.LogFreeFamHeight e1 e3) :
    Work.ZeroDensity.LogFreeFamHeight e2 e4 := by
  obtain ⟨C, hC, q₀, hh⟩ := h
  refine ⟨C, hC, max q₀ 2, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  haveI := hqne
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith
  have hlog : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have h1m : (0 : ℝ) ≤ (1 - σ) * Real.log (q : ℝ) := mul_nonneg (by linarith) hlog
  have hTnn : (0 : ℝ) < T := by linarith
  have hexp : Real.exp (e1 * ((1 - σ) * Real.log (q : ℝ)))
      ≤ Real.exp (e2 * ((1 - σ) * Real.log (q : ℝ))) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h12 h1m)
  have hpow : T ^ e3 ≤ T ^ e4 := Real.rpow_le_rpow_of_exponent_le hT h34
  calc famCount q σ T ≤ C * Real.exp (e1 * ((1 - σ) * Real.log (q : ℝ))) * T ^ e3 :=
        hh q hq₀ σ T hσ0 hσ1 hT
    _ ≤ C * Real.exp (e2 * ((1 - σ) * Real.log (q : ℝ))) * T ^ e4 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hexp (le_of_lt hC)) hpow
          (Real.rpow_nonneg (le_of_lt hTnn) _)
          (mul_nonneg (le_of_lt hC) (Real.exp_nonneg _))

/-- **`LogFreeFamHalf (261/100)` from Jutila's non-principal theorem and Montgomery's sharp
large-sieve estimate** — no Huxley. -/
theorem logFreeFamHalf_of_jutila_montgomery
    (hJ : FamilyZeroDensityJutilaNP) (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.ZeroDensity.LogFreeFamHalf ((261 : ℝ) / 100) := by
  obtain ⟨C, hC, h⟩ := famCount_le_qpow_of_jutila_montgomery hJ hM
  refine ⟨C, hC, 2, ?_⟩
  intro q hq hqne σ hσ0 hσ1
  haveI := hqne
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hb := h q hq σ 1 hσ0 hσ1 le_rfl
  rw [Real.one_rpow, mul_one] at hb
  have hexp : (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ))
      = Real.exp (((261 : ℝ) / 100) * ((1 - σ) * Real.log (q : ℝ))) := by
    rw [rpow_eq_exp' hqpos]
    ring
  calc famCount q σ 1 ≤ C * (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) := hb
    _ = C * Real.exp (((261 : ℝ) / 100) * ((1 - σ) * Real.log (q : ℝ))) := by rw [hexp]

/-- **`LogFreeFamHeight (261/100) (3/2)` from Jutila's non-principal theorem and Montgomery's sharp
large-sieve estimate** — no Huxley. -/
theorem logFreeFamHeight_of_jutila_montgomery
    (hJ : FamilyZeroDensityJutilaNP) (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.ZeroDensity.LogFreeFamHeight ((261 : ℝ) / 100) (3 / 2) := by
  obtain ⟨C, hC, h⟩ := famCount_le_qpow_of_jutila_montgomery hJ hM
  refine ⟨C, hC, 2, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  haveI := hqne
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hb := h q hq σ T hσ0 hσ1 hT
  have hexp : (q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ))
      = Real.exp (((261 : ℝ) / 100) * ((1 - σ) * Real.log (q : ℝ))) := by
    rw [rpow_eq_exp' hqpos]
    ring
  calc famCount q σ T ≤ C * ((q : ℝ) ^ (((261 : ℝ) / 100) * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := hb
    _ = C * Real.exp (((261 : ℝ) / 100) * ((1 - σ) * Real.log (q : ℝ))) * T ^ ((3 : ℝ) / 2) := by
        rw [hexp]; ring

/-- **`LogFreeFamHalf (261/100)` from the historical pair (Jutila, Huxley)** — the statement with a
larger coefficient is weaker, so `LogFreeFamHalf (5/2)` (Huxley's `12/5` at `ε = 1/10`) gives it. -/
theorem logFreeFamHalf_of_jutila_huxley
    (hJ : FamilyZeroDensityJutilaNP) (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.ZeroDensity.LogFreeFamHalf ((261 : ℝ) / 100) :=
  Work.ZeroDensity.LogFreeFamHalf.mono (by norm_num) (logFreeFamHalfOfNonPrincipal hJ hH)

/-- **`LogFreeFamHeight (261/100) (3/2)` from the historical pair (Jutila, Huxley)**. -/
theorem logFreeFamHeight_of_jutila_huxley
    (hJ : FamilyZeroDensityJutilaNP) (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.ZeroDensity.LogFreeFamHeight ((261 : ℝ) / 100) (3 / 2) :=
  LogFreeFamHeight_mono (by norm_num) le_rfl (logFreeFamHeightOfNonPrincipal hJ hH)

end

end Work.LinnikAreas
