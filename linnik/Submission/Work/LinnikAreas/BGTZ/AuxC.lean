/-
# Auxiliaries for the `C₀`-generalised high-zero bound `RestHighBGTZGenC`

The two constants-of-the-proof lemmas that the sibling `Submission/Work/LinnikAreas/RestHighBGTZ.lean`
proves for the additive constant `24` (`algPow_own`, `repulsionFloorHi_own`), restated for an
arbitrary additive constant `C₀ > 0`, together with the two dyadic-layer helpers (`jjC`,
`kernel_leC`, `dyadic_key_freeC`) that its private `highMassRep` uses, and the height-separation
lemma that lets the *restricted* repulsion of `RepulsionGenC` replace the unlimited one.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.siegelRestHigh

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
open Work.LinnikContract

/-- **The `(C₀ u)^{12/(5u)}` bound, with an arbitrary additive constant.**  For `u ≥ 4/3 + 1/100`
and `C₀ > 0`,
`exp(-(12/5)·(A - log(C₀ u))/u) ≤ exp(12·C₀/5)·(exp(-A))^{12/(5u)}`.

This is `Work.LinnikAreas.algPow_own` with `24` replaced by `C₀`: the extra factor is
`(C₀ u)^{12/(5u)} = exp((12/(5u))·log(C₀ u)) ≤ exp((12/(5u))·C₀ u) = exp(12·C₀/5)`. -/
theorem algPowC {C₀ u A : ℝ} (hC₀ : 0 < C₀) (hu : 4 / 3 + 1 / 100 ≤ u) :
    Real.exp (-(12 / 5) * ((A - Real.log (C₀ * u)) / u))
      ≤ Real.exp (12 * C₀ / 5) * (Real.exp (-A)) ^ (12 / (5 * u)) := by
  have hu0 : 0 < u := by linarith
  have hCu : 0 < C₀ * u := mul_pos hC₀ hu0
  have hsplit : Real.exp (-(12 / 5) * ((A - Real.log (C₀ * u)) / u))
      = Real.exp (-(12 / (5 * u) * A)) * Real.exp (12 / (5 * u) * Real.log (C₀ * u)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h3 : Real.exp (-(12 / (5 * u) * A)) = (Real.exp (-A)) ^ (12 / (5 * u)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have h4 : Real.exp (12 / (5 * u) * Real.log (C₀ * u)) ≤ Real.exp (12 * C₀ / 5) := by
    rw [Real.exp_le_exp]
    have h5 : Real.log (C₀ * u) ≤ C₀ * u := by
      have h6 := Real.log_le_sub_one_of_pos hCu
      linarith
    have h7 : 0 ≤ 12 / (5 * u) := by positivity
    have h8 := mul_le_mul_of_nonneg_left h5 h7
    have h9 : 12 / (5 * u) * (C₀ * u) = 12 * C₀ / 5 := by field_simp; try ring
    linarith
  calc Real.exp (-(12 / 5) * ((A - Real.log (C₀ * u)) / u))
      = (Real.exp (-A)) ^ (12 / (5 * u)) * Real.exp (12 / (5 * u) * Real.log (C₀ * u)) := by
        rw [hsplit, h3]
    _ ≤ (Real.exp (-A)) ^ (12 / (5 * u)) * Real.exp (12 * C₀ / 5) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp (12 * C₀ / 5) * (Real.exp (-A)) ^ (12 / (5 * u)) := by ring

/-- **The repulsion floor at a bounded height window, with arbitrary additive constant *and*
arbitrary parameters `(u,v)`.**  This is `repulsionFloorHi_own` with `24` replaced by `C₀` and the
constants `4/3+1/100`, `2/3+1/100` replaced by `u`, `v`; the extra hypothesis `λ₁ ≤ λ(ρ)` is what
the restricted repulsion `RepulsionGenC` supplies. -/
theorem repulsionFloorHiC {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ)
    {C₀ H u v : ℝ} (hC₀ : 0 < C₀) (hu : 0 < u) (hv : 0 ≤ v) (hH : 1 ≤ H)
    (hUpos : 0 < u + v * (Real.log (5 + H) / Real.log q))
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → lamOf q (β₁ : ℂ) ≤ lamOf q ρ →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (C₀ * (u + v * (Real.log (5 + |ρ.im|) / Real.log q))))
        / (u + v * (Real.log (5 + |ρ.im|) / Real.log q)) ≤ lamOf q ρ)
    (hfloor0 : C₀ * (u + v * (Real.log (5 + H) / Real.log q)) ≤ 1 / lamOf q (β₁ : ℂ))
    (hq1 : 1 < q) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hzm : zeroMult χ ρ ≠ 0) (him : |ρ.im| ≤ H)
    (hne : ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)))
    (hlam : lamOf q (β₁ : ℂ) ≤ lamOf q ρ) :
    (Real.log (1 / lamOf q (β₁ : ℂ))
        - Real.log (C₀ * (u + v * (Real.log (5 + H) / Real.log q))))
      / (u + v * (Real.log (5 + H) / Real.log q)) ≤ lamOf q ρ := by
  set U : ℝ := u + v * (Real.log (5 + H) / Real.log q) with hUdef
  set Uρ : ℝ := u + v * (Real.log (5 + |ρ.im|) / Real.log q) with hUρdef
  have him5 : (0 : ℝ) < 5 + |ρ.im| := by positivity
  have hH5 : (0 : ℝ) < 5 + H := by linarith
  have hlogρ : Real.log (5 + |ρ.im|) ≤ Real.log (5 + H) := Real.log_le_log him5 (by linarith)
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hUρleU : Uρ ≤ U := by
    rw [hUdef, hUρdef]
    have h1 : Real.log (5 + |ρ.im|) / Real.log (q : ℝ)
        ≤ Real.log (5 + H) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right hlogρ hlogq_pos.le
    have h2 := mul_le_mul_of_nonneg_left h1 hv
    linarith
  have hUρpos : 0 < Uρ := by
    rw [hUρdef]
    have h2 : 0 ≤ Real.log (5 + |ρ.im|) := by
      refine Real.log_nonneg ?_
      have := abs_nonneg ρ.im; linarith
    have h3 : 0 ≤ Real.log (5 + |ρ.im|) / Real.log (q : ℝ) := div_nonneg h2 hlogq_pos.le
    have h4 := mul_nonneg hv h3
    linarith
  have hUpos' : 0 < U := by rw [hUdef]; exact hUpos
  have hlampos : 0 < lamOf q (β₁ : ℂ) := by
    have h1 : 0 < 1 / lamOf q (β₁ : ℂ) :=
      lt_of_lt_of_le (mul_pos hC₀ hUpos') hfloor0
    exact one_div_pos.mp h1
  set A : ℝ := Real.log (1 / lamOf q (β₁ : ℂ)) with hAdef
  have hCU : Real.log (C₀ * U) ≤ A := by
    rw [hAdef]
    rw [Real.log_le_iff_le_exp (mul_pos hC₀ hUpos'), Real.exp_log (by positivity)]
    exact hfloor0
  have hrepρ := hrep χ ρ hzm hne hlam
  have hmono : (A - Real.log (C₀ * U)) / U ≤ (A - Real.log (C₀ * Uρ)) / Uρ := by
    rw [div_le_div_iff₀ hUpos' hUρpos]
    have h1 : Real.log (C₀ * Uρ) ≤ Real.log (C₀ * U) :=
      Real.log_le_log (mul_pos hC₀ hUρpos) (mul_le_mul_of_nonneg_left hUρleU hC₀.le)
    calc (A - Real.log (C₀ * U)) * Uρ ≤ (A - Real.log (C₀ * U)) * U :=
          mul_le_mul_of_nonneg_left hUρleU (by linarith)
      _ ≤ (A - Real.log (C₀ * Uρ)) * U :=
          mul_le_mul_of_nonneg_right (by linarith) hUpos'.le
  rw [hUρdef] at hmono
  rw [hAdef] at hmono
  exact hmono.trans hrepρ

/-- **The layer-gap estimate.**  With `ξ_j = log(5+2^{j+1})/𝓛`, `U_j = 11/5 + (11/10)ξ_j`, `α > 0`
and `α ≤ 𝓛/2`, the "gap" `h_j = (j/2)log 2 + α(12/(5U_j) - 1)` is at least
`(log 2/4)(j - 1 - log 9/log 2)`.  This is the quantitative form of "the repulsion with
`u = 11/5`, `v = 11/10` still saves a fixed exponential amount per dyadic layer". -/
lemma layer_gap {𝓛 α : ℝ} (h𝓛 : 20 ≤ 𝓛) (hα0 : 0 < α) (hα : α ≤ 𝓛 / 2) (j : ℕ) :
    (Real.log 2 / 4) * ((j : ℝ) - 1 - Real.log 9 / Real.log 2)
      ≤ (j : ℝ) / 2 * Real.log 2
        + α * (12 / (5 * (11 / 5 + (11 / 10)
            * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛))) - 1) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h𝓛pos : 0 < 𝓛 := by linarith
  set ξ : ℝ := Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛 with hξdef
  set U : ℝ := 11 / 5 + (11 / 10) * ξ with hUdef
  have hξnn : 0 ≤ ξ := by
    rw [hξdef]
    refine div_nonneg ?_ h𝓛pos.le
    refine Real.log_nonneg ?_
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hUpos : 0 < U := by
    have h2 : 0 ≤ (11 / 10) * ξ := mul_nonneg (by norm_num) hξnn
    rw [hUdef]; linarith
  have h5U : 5 * U = 11 + (11 / 2) * ξ := by rw [hUdef]; ring
  have hkey : α * (12 / (5 * U) - 1) ≥ -(𝓛 * ξ) / 4 := by
    have h5Upos : 0 < 5 * U := by positivity
    have h12 : α * (12 / (5 * U) - 1) = α * (1 - (11 / 2) * ξ) / (5 * U) := by
      rw [div_sub_one (ne_of_gt h5Upos), h5U]
      field_simp
      ring
    rw [h12]
    by_cases hcase : (11 / 2) * ξ ≤ 1
    · have h1 : 0 ≤ 1 - (11 / 2) * ξ := by linarith
      have h2 : 0 ≤ α * (1 - (11 / 2) * ξ) / (5 * U) :=
        div_nonneg (mul_nonneg hα0.le h1) h5Upos.le
      have h3 : -(𝓛 * ξ) / 4 ≤ 0 := by
        have : 0 ≤ 𝓛 * ξ := mul_nonneg h𝓛pos.le hξnn
        linarith
      linarith
    · push_neg at hcase
      have hneg : 1 - (11 / 2) * ξ ≤ 0 := by linarith
      rw [ge_iff_le, le_div_iff₀ h5Upos, h5U]
      nlinarith [hα, hcase, hneg, h𝓛pos, sq_nonneg ξ, mul_nonneg h𝓛pos.le (sq_nonneg ξ)]
  have hξlog : 𝓛 * ξ = Real.log (5 + (2 : ℝ) ^ (j + 1)) := by
    rw [hξdef, mul_div_cancel₀ _ (ne_of_gt h𝓛pos)]
  have hlogpow : Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log 9 + ((j : ℝ) + 1) * Real.log 2 := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    have h4 : (5 : ℝ) + (2 : ℝ) ^ (j + 1) ≤ 9 * (2 : ℝ) ^ (j + 1) := by linarith
    calc Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log (9 * (2 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by positivity) h4
      _ = Real.log 9 + ((j : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast; ring
  have hmain : (j : ℝ) / 2 * Real.log 2 + α * (12 / (5 * U) - 1)
      ≥ (j : ℝ) / 2 * Real.log 2 - (Real.log 9 + ((j : ℝ) + 1) * Real.log 2) / 4 := by
    have h1 : -(𝓛 * ξ) / 4 ≥ -(Real.log 9 + ((j : ℝ) + 1) * Real.log 2) / 4 := by
      rw [hξlog]; linarith [hlogpow]
    linarith
  have hgoal : (Real.log 2 / 4) * ((j : ℝ) - 1 - Real.log 9 / Real.log 2)
      = (j : ℝ) / 2 * Real.log 2
        - (Real.log 9 + ((j : ℝ) + 1) * Real.log 2) / 4 := by
    field_simp
    ring
  rw [hgoal, hUdef] at *
  linarith [hmain]

/-- **The layer-gap estimate in exponential form.**  With `U_j = 11/5 + (11/10)ξ_j`,
`ξ_j = log(5+2^{j+1})/𝓛`, `α > 0` and `α ≤ 𝓛/2`,
`2^{-j/2}·(e^{-α})^{12/(5U_j)} ≤ e^{-α}·2^{5/4}·2^{-j/4}`.
This says that the kernel saving produced by the repulsion in the `j`-th dyadic height layer is, on
top of the geometric decay `2^{-j/4}`, a full factor `λ₁ = e^{-α}` — with the same factor `2^{-j/2}`
that the dyadic summation produces. -/
lemma layer_gap2 {𝓛 α : ℝ} (h𝓛 : 20 ≤ 𝓛) (hα0 : 0 < α) (hα : α ≤ 𝓛 / 2) (j : ℕ) :
    ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j
        * (Real.exp (-α)) ^ (12 / (5 * (11 / 5 + (11 / 10)
            * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛))))
      ≤ Real.exp (-α) * (2 : ℝ) ^ (5 / 4 : ℝ) * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ : Real.log 9 / Real.log 2 ≤ 4 := by
    rw [div_le_iff₀ hlog2pos]
    have h1 : Real.log 9 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  have hgap := layer_gap h𝓛 hα0 hα j
  have hL : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j
        * (Real.exp (-α)) ^ (12 / (5 * (11 / 5 + (11 / 10)
            * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛))))
      = Real.exp (-α) * Real.exp (-((j : ℝ) / 2 * Real.log 2
          + α * (12 / (5 * (11 / 5 + (11 / 10)
            * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛))) - 1))) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (Real.exp_pos (-α)), Real.log_exp]
    conv_lhs => rw [← Real.exp_add]
    conv_rhs => rw [← Real.exp_add]
    congr 1
    push_cast
    ring_nf
  have hR : Real.exp (-α) * (2 : ℝ) ^ (5 / 4 : ℝ) * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j
      = Real.exp (-α) * Real.exp ((5 : ℝ) / 4 * Real.log 2 - ((j : ℝ) / 4 * Real.log 2)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 4) : ℝ)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    conv_lhs => rw [← Real.exp_add, ← Real.exp_add]
    conv_rhs => rw [← Real.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [Real.exp_le_exp]
  have h1 : (Real.log 2 / 4) * ((j : ℝ) - 5)
      ≤ (j : ℝ) / 2 * Real.log 2 + α * (12 / (5 * (11 / 5 + (11 / 10)
          * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛))) - 1) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hgap
    linarith [hκ]
  have hgoal : (5 : ℝ) / 4 * Real.log 2 - ((j : ℝ) / 4 * Real.log 2)
      = -((Real.log 2 / 4) * ((j : ℝ) - 5)) := by
    push_cast; ring
  rw [hgoal]
  linarith [h1]

/-- The dyadic height layer index of a zero pair, `⌊log₂ ⌊|Im ρ|⌋⌋`. -/
noncomputable def jjC {q : ℕ} (z : DirichletCharacter ℂ q × ℂ) : ℕ :=
  Nat.log 2 (Nat.floor |z.2.im|)

/-- The elementary geometric identity behind the dyadic-layer summation. -/
lemma dyadic_key_freeC (j : ℕ) :
    ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * ((4 : ℝ) ^ j)⁻¹
      = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
  have h4 : ((4 : ℝ) ^ j)⁻¹ = (2 : ℝ) ^ (-(2 * (j : ℝ))) := by
    rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * (j : ℝ)) by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
            ← Real.rpow_natCast 2 (2 * j)]
          push_cast; ring]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
      = (2 : ℝ) ^ ((3 / 2 : ℝ) * (1 + (j : ℝ))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (j + 1), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  calc ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * ((4 : ℝ) ^ j)⁻¹
      = (2 : ℝ) ^ ((3 / 2 : ℝ) * (1 + (j : ℝ))) * (2 : ℝ) ^ (-(2 * (j : ℝ))) := by
        rw [h2, h4]
    _ = (2 : ℝ) ^ ((3 / 2 : ℝ) * (1 + (j : ℝ)) + -(2 * (j : ℝ))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ ((3 / 2 : ℝ) + (j : ℝ) * (-(1 / 2))) := by
        congr 1; ring
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) * (-(1 / 2))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
        congr 1
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) j,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring

/-- Termwise kernel bound with the dyadic height index. -/
lemma kernel_leC {q : ℕ} [NeZero q] (hq : 1 < q) (z : DirichletCharacter ℂ q × ℂ)
    (hzm : zeroMult z.1 z.2 ≠ 0) (hhigh : 1 < |z.2.im|) :
    (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
      ≤ 4 / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2)
        * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hker := high_kernel_le hq z hzm hhigh
  have himpos : 0 < |z.2.im| := by linarith
  have h4 : (4 : ℝ) ^ (jjC z) ≤ |z.2.im| ^ 2 := by
    have hle : (2 : ℝ) ^ (jjC z) ≤ |z.2.im| := by
      have hn1 : 1 ≤ Nat.floor |z.2.im| := Nat.floor_pos.mpr hhigh.le
      have hn : Nat.floor |z.2.im| ≠ 0 := by omega
      have hh := Nat.pow_log_le_self 2 hn
      have h1 : (2 : ℝ) ^ (jjC z) ≤ (Nat.floor |z.2.im| : ℝ) := by
        have h2 : (((2 : ℕ) ^ (Nat.log 2 (Nat.floor |z.2.im|)) : ℕ) : ℝ)
            ≤ (Nat.floor |z.2.im| : ℝ) := Nat.cast_le.mpr hh
        push_cast at h2
        simpa [jjC] using h2
      have h3 : (Nat.floor |z.2.im| : ℝ) ≤ |z.2.im| := Nat.floor_le (abs_nonneg _)
      linarith
    have h3 : (4 : ℝ) ^ (jjC z) = ((2 : ℝ) ^ (jjC z)) ^ 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
      exact (pow_mul (2 : ℝ) 2 (jjC z)).symm.trans (pow_mul' (2 : ℝ) 2 (jjC z))
    rw [h3]
    exact pow_le_pow_left₀ (by positivity) hle 2
  have hpos : 0 < (4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2 := by positivity
  have hle2 : (4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2
      ≤ |z.2.im| ^ 2 * (Real.log (q : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  calc (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
      ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log (q : ℝ)) ^ 2 := hker
    _ = 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| ^ 2 * (Real.log (q : ℝ)) ^ 2) := by rw [mul_pow]
    _ ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hpos hle2
    _ = 4 / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2)
          * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by field_simp

/-- **Zeros below `λ₁` are high.**  If the zero-free region `ZFRInput cZ` holds, `λ₁ < 1/10` and
`λ₁ < cZ/4`, then every zero `ρ ≠ β₁` of any `L(s,χ)` mod `q` (`q ≥ 16`) with `λ(ρ) < λ₁` has
`|Im ρ| ≥ 4q²`.  This is what makes the dyadic layers of bounded height `j ≤ J` (`|Im ρ| < 2^{J+1}
≤ 4q²`) safe for the *restricted* repulsion, which only says something about zeros with
`λ(ρ) ≥ λ₁`. -/
theorem height_sep_of_ZFR {cZ : ℝ} {q : ℕ} [NeZero q] (hq : 16 ≤ q)
    (hZFR : ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β₁ →
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
        (1 / 2 : ℝ) < ρ.re → ρ ≠ (β₁ : ℂ) →
        cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re)
    {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ}
    (hχ : χ₁ ≠ 1) (hsq : χ₁ ^ 2 = 1) (hβ : β₁ < 1) (hz : zeroMult χ₁ (β₁ : ℂ) ≠ 0)
    (hlam10 : lamOf q (β₁ : ℂ) < 1 / 10) (hε : lamOf q (β₁ : ℂ) < cZ / 4)
    {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hzm : zeroMult χ ρ ≠ 0)
    (hlt : lamOf q ρ < lamOf q (β₁ : ℂ)) :
    4 * (q : ℝ) ^ 2 ≤ |ρ.im| := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlam1pos : 0 < lamOf q (β₁ : ℂ) := Siegel.lamOf_pos hχ hβ hz
  have hcZ : 0 < cZ := by linarith
  have hq16 : (16 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog16 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    have h2 : Real.log 16 ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by norm_num) hq16
    have h3 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
      push_cast; ring
    have h4 : (1 : ℝ) < Real.log 16 := by
      rw [h3]; have := Real.log_two_gt_d9; linarith
    linarith
  -- `1 - 1/(10𝓛) < β₁`
  have hβ1 : 1 - 1 / (10 * Real.log q) < β₁ := by
    have h2 : (1 - β₁) * Real.log (q : ℝ) = lamOf q (β₁ : ℂ) := by
      rw [lamOf, Complex.ofReal_re]
    have h3 : (1 - β₁) * Real.log (q : ℝ) < 1 / 10 := by rw [h2]; exact hlam10
    have h4 : 1 - β₁ < 1 / (10 * Real.log q) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 10 * Real.log q)]
      linarith
    linarith
  -- `1/2 < Re ρ`
  have hre : (1 / 2 : ℝ) < ρ.re := by
    by_contra hcon
    push_neg at hcon
    have h2 : lamOf q ρ = (1 - ρ.re) * Real.log (q : ℝ) := rfl
    have h3 : (1 / 2 : ℝ) * Real.log (q : ℝ) ≤ lamOf q ρ := by
      rw [h2]
      exact mul_le_mul_of_nonneg_right (by linarith) hlog.le
    have h4 : (1 / 10 : ℝ) < (1 / 2 : ℝ) * Real.log (q : ℝ) := by
      nlinarith [hlog16]
    linarith [hlt, hlam10]
  have hne : ρ ≠ (β₁ : ℂ) := by
    intro h0
    rw [h0] at hlt
    exact lt_irrefl _ hlt
  have hZ := hZFR χ₁ β₁ hχ hsq hβ hz hβ1 χ ρ hzm hre hne
  -- `M = max 4 |ρ.im|`
  set M : ℝ := max 4 |ρ.im| with hMdef
  have hM4 : (4 : ℝ) ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  have hqM : (1 : ℝ) < (q : ℝ) * M := by
    have : (1 : ℝ) * 1 < (q : ℝ) * M := by
      refine mul_lt_mul ?_ ?_ ?_ ?_ <;> linarith [hq1, hM4]
    linarith
  have hlogqM : 0 < Real.log ((q : ℝ) * M) := Real.log_pos hqM
  -- multiply the ZFR bound by `log q`
  have h1 : cZ * Real.log (q : ℝ) / Real.log ((q : ℝ) * M) ≤ lamOf q ρ := by
    have h3 := mul_le_mul_of_nonneg_right hZ hlog.le
    rw [div_mul_eq_mul_div] at h3
    rwa [show lamOf q ρ = (1 - ρ.re) * Real.log (q : ℝ) from rfl]
  have h2 : cZ * Real.log (q : ℝ) / Real.log ((q : ℝ) * M) < cZ / 4 := by
    have h3 : lamOf q ρ < cZ / 4 := lt_trans hlt hε
    linarith [h1, h3]
  -- `4𝓛 < log (q M)`
  have h4 : 4 * Real.log (q : ℝ) < Real.log ((q : ℝ) * M) := by
    have h2' : cZ * Real.log (q : ℝ) * 4 < cZ * Real.log ((q : ℝ) * M) :=
      (div_lt_div_iff₀ hlogqM (by norm_num : (0 : ℝ) < 4)).mp h2
    have h2'' : cZ * (4 * Real.log (q : ℝ)) < cZ * Real.log ((q : ℝ) * M) := by
      nlinarith [h2']
    exact lt_of_mul_lt_mul_left h2'' hcZ.le
  have h5 : Real.log M > 3 * Real.log (q : ℝ) := by
    have hmul : Real.log ((q : ℝ) * M) = Real.log (q : ℝ) + Real.log M :=
      Real.log_mul (ne_of_gt hqpos) (ne_of_gt hMpos)
    rw [hmul] at h4
    linarith
  have h6 : M > (q : ℝ) ^ 3 := by
    have hexp : Real.exp (3 * Real.log (q : ℝ)) = (q : ℝ) ^ 3 := by
      rw [show (3 : ℝ) * Real.log (q : ℝ) = Real.log ((q : ℝ) ^ 3) by
        rw [Real.log_pow]; push_cast; ring]
      exact Real.exp_log (by positivity)
    have h7 : Real.exp (3 * Real.log (q : ℝ)) < Real.exp (Real.log M) :=
      Real.exp_lt_exp.mpr h5
    rw [Real.exp_log hMpos, hexp] at h7
    exact h7
  have h4le : (4 : ℝ) < (q : ℝ) ^ 3 := by
    have h1 : (4 : ℝ) < (16 : ℝ) ^ 3 := by norm_num
    have h2 : (16 : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hq16 3
    linarith
  have hmax : M = |ρ.im| := by
    rcases le_total 4 |ρ.im| with h | h
    · rw [hMdef]; exact max_eq_right h
    · have hh : M = 4 := by rw [hMdef]; exact max_eq_left h
      rw [hh] at h6; linarith
  have h7 : |ρ.im| > (q : ℝ) ^ 3 := by rw [← hmax]; exact h6
  have h8 : 4 * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    nlinarith [hqpos, hq16]
  linarith [h7, h8]

end
end Work.LinnikAreas.BGTZ
