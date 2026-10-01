import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.ZeroDensity.Basic
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.principalCountIn_le_rpow
import Submission.Work.LinnikAreas.logFreeFamHalfOfNonPrincipal
import Submission.Work.LinnikAreas.boxMaxZero

/-!
# AREA 6's family counts from the LogFree chapter's two nodes plus Montgomery

The exponent `5/2` that the AREA 6 chain consumes (`LogFreeFamHalf (5/2)`,
`LogFreeFamHeight (5/2) (3/2)`) is `12/5 + 1/10`: it is *exactly* Huxley's `12/5` at `ε = 1/10`.
This file shows that the same exponent is reached from the **LogFree chapter's nodes plus
Montgomery**, with no use of the all-character Huxley estimate and no use of Jutila's sharp
non-principal theorem:

| `σ`-range | input | coefficient | reference |
|---|---|---|---|
| `[0, 29/50]` | the σ-blind count (`trivial_bound`, `ε = 1/50`) | `1.02 ≤ 5/2(1-σ)` | `ZeroDensity.trivial_bound` |
| `[1/2, 3/4]` | `MontgomerySharp (1/1000)` at `ε = 1/100` | `3/(2-σ) + 0.011 ≤ 5/2(1-σ)` | `ZeroDensity.MontgomerySharp` |
| `[3/4, 93/100]` | `HuxleyNPWide` at `ε = 1/100` | `(12/5+1/100)(1-σ) + 0.0025 ≤ 5/2(1-σ)` | `ZeroDensity.LogFree.HuxleyNPWide` |
| `[93/100, 1]` | `logFreeNP (93/100) (12/5)` | `12/5 ≤ 5/2` | `ZeroDensity.LogFree.logFreeNP` |

and the *principal* character is carried by absolute bounds alone (`zeroCountIn_one_height_one_bound`
at height `1` — σ-free, see `zeroCountIn_one_height_one_bound'` below — and
`principalCountIn_le_rpow` for general height).  The logarithmic powers of Montgomery
(`(log qT)^{1/1000}`) and of `HuxleyNPWide` (`log qT`) are absorbed via
`(log x)^B ≤ (2B/δ)^B x^{δ/2}` (`log_pow_le_const_mul_rpow`), the `δ/2` of excess exponent being
well inside the available slack (`0.011 ≤ 0.014` on the Montgomery range, `0.0025 ≤ 0.0063` on the
`HuxleyNPWide` range, the worst point being `σ = 3/4` resp. `σ = 93/100`).

The `T`-exponent of every piece is `≤ 3/2`, so the single estimate proved below
`famCount q σ T ≤ C·q^{(5/2)(1-σ)}T^{3/2}` yields both `LogFreeFamHalf (5/2)` (take `T = 1`) and
`LogFreeFamHeight (5/2) (3/2)`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
open Work.ZeroDensity.LogFree
noncomputable section

open Work.LinnikContract
open Work.ZeroDensity (famCount)

/-- **`log x ^ B ≤ C x ^ (δ/2)`** for `x ≥ 1`, `B, δ > 0`, with the explicit constant
`(2B/δ)^B`; used to absorb the logarithmic powers of `MontgomerySharp` and `HuxleyNPWide` into a
few thousandths of exponent budget. -/
lemma log_pow_le_const_mul_rpow {x B δ : ℝ} (hx : 1 ≤ x) (hB : 0 < B) (hδ : 0 < δ) :
    Real.log x ^ B ≤ (2 * B / δ) ^ B * x ^ (δ / 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  set a : ℝ := δ / (2 * B) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hlog : Real.log x ≤ (2 * B / δ) * x ^ a := by
    have h := Real.log_le_rpow_div hx0.le hapos
    have h2 : x ^ a / a = (2 * B / δ) * x ^ a := by
      rw [div_eq_mul_inv, ha]
      field_simp
    rwa [h2] at h
  have h0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ^ B ≤ ((2 * B / δ) * x ^ a) ^ B :=
    Real.rpow_le_rpow h0 hlog hB.le
  have h2 : ((2 * B / δ) * x ^ a) ^ B = (2 * B / δ) ^ B * x ^ (δ / 2) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hx0.le a), ← Real.rpow_mul hx0.le]
    have h3 : a * B = δ / 2 := by rw [ha]; field_simp
    rw [h3]
  rwa [h2] at h1

/-- **The principal character at height `1` is bounded absolutely, uniformly in `σ ∈ [0,1]`.**
The proof is that of `zeroCountIn_one_height_one_bound`, but the divisor-sum bound
`zeroCountIn_one_le_divisorSum` is blind in `σ`, so the range hypothesis `4/5 ≤ σ` of that
statement can be dropped. -/
theorem zeroCountIn_one_height_one_bound' :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q] (σ : ℝ), 0 ≤ σ → σ ≤ 1 →
      zeroCountIn (1 : DirichletCharacter ℂ q) σ 1 ≤ C := by
  refine ⟨|(∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiC
      (Metric.closedBall (0 : ℂ) ((1 : ℝ) + 2))) u : ℤ) : ℝ))| + 1, by positivity, ?_⟩
  intro q hqne σ h0 h1
  have hD := zeroCountIn_one_le_divisorSum q σ 1 h0 h1 le_rfl
  refine le_trans hD (le_trans (le_abs_self _) (by linarith))

/-- **The family zero count with coefficient `5/2`, from the LogFree chapter's two nodes and
Montgomery.**  For every `q ≥ 2`, `0 ≤ σ ≤ 1`, `T ≥ 1`,
`Σ_χ N(σ,T,χ) ≤ C·q^{(5/2)(1-σ)}·T^{3/2}` with `C` independent of `q`, `σ`, `T`. -/
theorem famCount_le_qpow_of_coreNodes
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ),
      0 ≤ σ → σ ≤ 1 → 1 ≤ T →
        famCount q σ T ≤ C * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by
  obtain ⟨Clog, hClog, hlog'⟩ := hlog
  obtain ⟨Chux, hChux, hhux'⟩ := hhux (1 / 100) (by norm_num)
  obtain ⟨Cm, hCm, hM'⟩ := hM (1 / 100) (by norm_num)
  obtain ⟨Ct, hCt, ht⟩ := Work.ZeroDensity.trivial_bound (1 / 50) (by norm_num)
  obtain ⟨Cz, hCz, hz⟩ := principalCountIn_le_rpow
  refine ⟨max (max (max Ct (400 * Chux)) Cm) Clog + Cz + 1, by positivity, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  haveI := hqne
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hqTpos : (0 : ℝ) < (q : ℝ) * T := by nlinarith
  have hPnn : (0 : ℝ) ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hqpos.le _) (Real.rpow_nonneg hTpos.le _)
  have hP1 : (1 : ℝ) ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
    Real.one_le_rpow hq1 (mul_nonneg (by norm_num) (by linarith))
  have hsplit : famCount q σ T
      = famCountNP q σ T + zeroCountIn (1 : DirichletCharacter ℂ q) σ T := by
    rw [famCount_eq_erase_add]
    simp only [Work.ZeroDensity.LogFree.famCountNP, Work.ZeroDensity.zCount]
  have hprin : zeroCountIn (1 : DirichletCharacter ℂ q) σ T
      ≤ Cz * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
    le_trans (hz q hq σ T hσ0 hσ1 hT)
      (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (Real.rpow_nonneg hTpos.le _) hP1) (le_of_lt hCz))
  have hCtle : Ct ≤ max (max (max Ct (400 * Chux)) Cm) Clog := by
    refine le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hChuxle : 400 * Chux ≤ max (max (max Ct (400 * Chux)) Cm) Clog := by
    refine le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCmle : Cm ≤ max (max (max Ct (400 * Chux)) Cm) Clog := by
    refine le_trans (le_max_right _ _) (le_max_left _ _)
  have hClogle : Clog ≤ max (max (max Ct (400 * Chux)) Cm) Clog := le_max_right _ _
  rcases le_total σ (29 / 50) with hσtriv | hσtriv
  · -- ## `σ ≤ 29/50`: the σ-blind count (it bounds every character, hence also the non-principal ones)
    have h := ht q hq σ T hσ0 hσ1 hT
    have hb : (1 : ℝ) + 1 / 50 = (51 : ℝ) / 50 := by norm_num
    rw [hb] at h
    rw [Real.mul_rpow hqpos.le hTpos.le] at h
    have hqle : (q : ℝ) ^ ((51 : ℝ) / 50) ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith [hσtriv])
    have hTle : T ^ ((51 : ℝ) / 50) ≤ T ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    have hstep : (q : ℝ) ^ ((51 : ℝ) / 50) * T ^ ((51 : ℝ) / 50)
        ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2) :=
      mul_le_mul hqle hTle (Real.rpow_nonneg hTpos.le _) (Real.rpow_nonneg hqpos.le _)
    have hFam : famCountNP q σ T
        ≤ Ct * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
      le_trans (le_trans (famCountNP_le_famCount q σ T) h)
        (mul_le_mul_of_nonneg_left hstep (le_of_lt hCt))
    rw [hsplit]
    calc famCountNP q σ T + zeroCountIn (1 : DirichletCharacter ℂ q) σ T
        ≤ Ct * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2))
          + Cz * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          add_le_add hFam hprin
      _ = (Ct + Cz) * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ (max (max (max Ct (400 * Chux)) Cm) Clog + Cz + 1)
            * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith [hCtle]) hPnn
  rcases le_total σ (3 / 4) with hσmid | hσmid
  · -- ## `1/2 ≤ σ ≤ 3/4`: Montgomery's sharp estimate (`ε = 1/100`, logarithmic power absorbed)
    have h := hM' q hq σ T (by linarith) hσ1 hT
    have hden : (0 : ℝ) < 2 - σ := by linarith
    have hlogpow := log_pow_le_const_mul_rpow (x := (q : ℝ) * T) (B := (1 : ℝ) / 1000)
      (δ := 1 / 500) hqT1 (by norm_num) (by norm_num)
    have hconst : (2 * ((1 : ℝ) / 1000) / (1 / 500)) ^ ((1 : ℝ) / 1000) = 1 := by
      rw [show 2 * ((1 : ℝ) / 1000) / (1 / 500) = 1 by norm_num, Real.one_rpow]
    rw [hconst, one_mul] at hlogpow
    rw [show ((1 : ℝ) / 500) / 2 = (1 : ℝ) / 1000 by norm_num] at hlogpow
    have hexp1 : 3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000
        ≤ (5 : ℝ) / 2 * (1 - σ) := by
      have h1 : 3 * (1 - σ) / (2 - σ) = (3 / (2 - σ)) * (1 - σ) := by ring
      have hcoef : 3 / (2 - σ) ≤ 12 / 5 := by rw [div_le_iff₀ hden]; linarith
      have h1m : (0 : ℝ) ≤ 1 - σ := by linarith
      have hcf := mul_le_mul_of_nonneg_right hcoef h1m
      have h2 : (1 - σ) ≥ 1 / 4 := by linarith
      rw [h1]
      nlinarith
    have hexp2 : 3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000 ≤ (3 : ℝ) / 2 := by
      have h1 : 3 * (1 - σ) / (2 - σ) ≤ 1 := by rw [div_le_one hden]; linarith
      linarith
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
    have hqle : (q : ℝ) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000)
        ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp1
    have hTle : T ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000)
        ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hT hexp2
    have hstep : ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + (1 : ℝ) / 100 + (1 : ℝ) / 1000)
        ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hTpos)]
      exact mul_le_mul hqle hTle (Real.rpow_nonneg (le_of_lt hTpos) _)
        (Real.rpow_nonneg (le_of_lt hqpos) _)
    have hFam : famCountNP q σ T
        ≤ Cm * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
      le_trans (le_trans (famCountNP_le_famCount q σ T) h)
        (le_trans hmain (mul_le_mul_of_nonneg_left hstep (le_of_lt hCm)))
    rw [hsplit]
    calc famCountNP q σ T + zeroCountIn (1 : DirichletCharacter ℂ q) σ T
        ≤ Cm * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2))
          + Cz * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          add_le_add hFam hprin
      _ = (Cm + Cz) * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ (max (max (max Ct (400 * Chux)) Cm) Clog + Cz + 1)
            * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hPnn
  rcases le_total σ ((93 : ℝ) / 100) with hσhux | hσhux
  · -- ## `3/4 ≤ σ ≤ 93/100`: Huxley's non-principal `12/5` widened (logarithmic power absorbed)
    have h := hhux' q hq σ T (by linarith) hσhux hT
    have hlogpow := log_pow_le_const_mul_rpow (x := (q : ℝ) * T) (B := 1) (δ := 1 / 200) hqT1
      (by norm_num) (by norm_num)
    have hconst : (2 * (1 : ℝ) / (1 / 200)) ^ (1 : ℝ) = 400 := by norm_num
    rw [hconst] at hlogpow
    rw [show ((1 : ℝ) / 200) / 2 = (1 : ℝ) / 400 by norm_num] at hlogpow
    have hexp1 : ((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400 ≤ (5 : ℝ) / 2 * (1 - σ) := by
      have h2 : (1 - σ) ≥ 7 / 100 := by linarith
      nlinarith
    have hexp2 : ((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400 ≤ (3 : ℝ) / 2 := by
      have h2 : (1 - σ) ≤ 1 / 4 := by linarith
      nlinarith
    have hmain : Chux * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ))
          * Real.log ((q : ℝ) * T)
        ≤ (400 * Chux) * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400) := by
      have hAX : (0 : ℝ) ≤ Chux * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ)) :=
        mul_nonneg (le_of_lt hChux) (Real.rpow_nonneg (le_of_lt hqTpos) _)
      have h1 := mul_le_mul_of_nonneg_left hlogpow hAX
      rw [Real.rpow_one] at h1
      calc Chux * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ))
            * Real.log ((q : ℝ) * T)
          ≤ Chux * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ))
            * (400 * ((q : ℝ) * T) ^ ((1 : ℝ) / 400)) := h1
        _ = (400 * Chux) * (((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ))
              * ((q : ℝ) * T) ^ ((1 : ℝ) / 400)) := by ring
        _ = (400 * Chux) * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400) := by
              rw [Real.rpow_add hqTpos]
    have hqle : (q : ℝ) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400)
        ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp1
    have hTle : T ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400) ≤ T ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hT hexp2
    have hstep : ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + 1 / 100) * (1 - σ) + 1 / 400)
        ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hTpos)]
      exact mul_le_mul hqle hTle (Real.rpow_nonneg (le_of_lt hTpos) _)
        (Real.rpow_nonneg (le_of_lt hqpos) _)
    have hFam : famCountNP q σ T
        ≤ (400 * Chux) * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
      le_trans h (le_trans hmain (mul_le_mul_of_nonneg_left hstep (by positivity)))
    rw [hsplit]
    calc famCountNP q σ T + zeroCountIn (1 : DirichletCharacter ℂ q) σ T
        ≤ (400 * Chux) * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2))
          + Cz * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          add_le_add hFam hprin
      _ = (400 * Chux + Cz) * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ (max (max (max Ct (400 * Chux)) Cm) Clog + Cz + 1)
            * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hPnn
  · -- ## `σ ≥ 93/100`: the log-free non-principal estimate
    have hσ93 : (93 : ℝ) / 100 ≤ σ := hσhux
    have h := hlog' q hq σ T hσ93 hσ1 hT
    have hexp : (12 : ℝ) / 5 * (1 - σ) ≤ (5 : ℝ) / 2 * (1 - σ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
    have hTexp : (12 : ℝ) / 5 * (1 - σ) ≤ (3 : ℝ) / 2 := by
      have h1 : (1 - σ) ≤ 7 / 100 := by linarith
      nlinarith
    have hqle : (q : ℝ) ^ ((12 : ℝ) / 5 * (1 - σ)) ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp
    have hTle : T ^ ((12 : ℝ) / 5 * (1 - σ)) ≤ T ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hT hTexp
    have hstep : ((q : ℝ) * T) ^ ((12 : ℝ) / 5 * (1 - σ))
        ≤ (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hTpos)]
      exact mul_le_mul hqle hTle (Real.rpow_nonneg (le_of_lt hTpos) _)
        (Real.rpow_nonneg (le_of_lt hqpos) _)
    have hFam : famCountNP q σ T
        ≤ Clog * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
      le_trans h (mul_le_mul_of_nonneg_left hstep (le_of_lt hClog))
    rw [hsplit]
    calc famCountNP q σ T + zeroCountIn (1 : DirichletCharacter ℂ q) σ T
        ≤ Clog * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2))
          + Cz * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          add_le_add hFam hprin
      _ = (Clog + Cz) * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ (max (max (max Ct (400 * Chux)) Cm) Clog + Cz + 1)
            * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hPnn

/-- **`LogFreeFamHalf (5/2)` from the LogFree chapter's two nodes and Montgomery** — the exponent
`5/2` is unchanged, so the whole AREA 6 chain below this statement is reused verbatim. -/
theorem logFreeFamHalf_of_coreNodes
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.ZeroDensity.LogFreeFamHalf (5 / 2) := by
  obtain ⟨C, hC, h⟩ := famCount_le_qpow_of_coreNodes hlog hhux hM
  refine ⟨C, hC, 2, ?_⟩
  intro q hq hqne σ hσ0 hσ1
  haveI := hqne
  have hb := h q hq σ 1 hσ0 hσ1 le_rfl
  rw [Real.one_rpow, mul_one] at hb
  have hexp : (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ))
      = Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := rpow_half_eq_exp q hq σ
  calc famCount q σ 1 ≤ C * (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) := hb
    _ = C * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := by rw [hexp]

/-- **`LogFreeFamHeight (5/2) (3/2)` from the LogFree chapter's two nodes and Montgomery.** -/
theorem logFreeFamHeight_of_coreNodes
    (hlog : Work.ZeroDensity.LogFree.logFreeNP (93 / 100) (12 / 5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide)
    (hM : Work.ZeroDensity.MontgomerySharp (1 / 1000)) :
    Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2) := by
  obtain ⟨C, hC, h⟩ := famCount_le_qpow_of_coreNodes hlog hhux hM
  refine ⟨C, hC, 2, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  haveI := hqne
  have hb := h q hq σ T hσ0 hσ1 hT
  have hexp : (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ))
      = Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := rpow_half_eq_exp q hq σ
  calc famCount q σ T ≤ C * ((q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ)) * T ^ ((3 : ℝ) / 2)) := hb
    _ = C * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ ((3 : ℝ) / 2) := by
        rw [hexp]; ring

end

end Work.LinnikAreas
