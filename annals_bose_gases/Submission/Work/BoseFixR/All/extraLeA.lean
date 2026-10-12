import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.All.epsFar_le_inv_eight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.All.extraLeA` — the far-leg "extra" row

The far leg of the `R`-subproject (`FarZPSlotWProv`, `FarEnvPos`) compares a lattice
sum, weighted by `τ' = (1−ε)τ + ρε^{-1/2}a`, with its continuum integral.  Both the
`(1+64√ε)` of the lattice/continuum bookkeeping and the `(1+100√ε)` of the `τ'`
denominator inflate the mass `½ρ²ℓ³ĝ(0)` of the far bound by the factor
`(1+64√ε)(1+100√ε)`, while the `χ⋆χ`-deficit of the kernel contributes the
`(1+S(R/ℓ)²)` of `massDeficit_taylor`.  The present file shows that *all* of this
inflation, minus the leading `1`, is covered by the margin `4a(ρ−μ)²ℓ³` of the far
region — i.e. that the bracket

`(1+64√ε)(1+100√ε)(1+S(R/ℓ)²) − 1`

is small enough against `((ρ−μ)/ρ)²`.  The hypotheses are FS's: admissible box data
`Adm`, diluteness `ε₀ ≤ 10^{-4000}`, the far condition `FarCondFS`
(`|ρ−μ| ≥ μK_ℓ^{-2}/(2¹⁴π) = μt^{3/323}/(2¹⁴π)`), `g ≤ 16πa`, and the Taylor
constant `S` tied to `R` by `ε₀ ≤ (a²/((S+1)R²10^{15}))^{323/320}`.

Everything is a monomial comparison in `t = μ(a v)³ ≤ 10^{-4000}`:

* `√ε ≤ t^{1/16}`  (`bigMV_div_ell_cube_le_quarter` of `epsFar_le_inv_eight`);
* `ε₀ ≤ (a²/((S+1)R²10^{15}))^{323/320}` gives `S(R/ℓ)² ≤ t^{6/323}/10^{15}`
  (the exponent `323/320` and the `10^{15}` are exactly what converts
  `a^{-3·320/323}` into `a^{-2}`, i.e. what cancels `ℓ² = a²t^{-326/323}`);
* `t ≤ 10^{-4000}` gives `t^{1/16} ≤ t^{6/323}·10^{-15}`.

Hence the bracket is `≤ 457·10^{-15}·t^{6/323} ≤ t^{6/323}/(2^{31}π³)`; on the far
region `(ρ−μ)² ≥ μ²t^{6/323}/(2^{28}π²)`, so `2πρ²·bracket ≤ (ρ−μ)²` (with the
`ρ ≥ 2μ` case paying the much easier `bracket ≤ 1/(8π)`), which after
`g ≤ 16πa` and multiplication by `ℓ³` is the claim.
-/

namespace Work.BoseFixR.All

open Work.BoseBox

set_option linter.unusedVariables false

/-! ## 1. The three monomial rows -/

/-- **`t^{1/16} ≤ t^{6/323}·10^{-15}` for `0 < t ≤ 10^{-4000}`.**  Use
`1/16 = 6/323 + 227/5168` with `227/5168 ≥ 1/23`, so it suffices that
`t^{1/23} ≤ 10^{-15}`, i.e. (raising to the `23`rd power)
`t ≤ 10^{-345}`, which `t ≤ 10^{-4000} ≤ 10^{-345}` gives. -/
private lemma rpow_sixteenth_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (ht : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    t ^ (1 / 16 : ℝ) ≤ t ^ (6 / 323 : ℝ) * ((10 : ℝ) ^ 15)⁻¹ := by
  have ht' : t ≤ ((10 : ℝ) ^ 4000)⁻¹ := by rwa [zpow_neg] at ht
  have h1 : t ^ (1 / 16 : ℝ) = t ^ (6 / 323 : ℝ) * t ^ (1 / 16 - 6 / 323 : ℝ) := by
    rw [← Real.rpow_add ht0]
    congr 1
    norm_num
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht0.le _)
  have h2 : t ^ (1 / 16 - 6 / 323 : ℝ) ≤ t ^ (1 / 23 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
  refine le_trans h2 ?_
  have hx : (t ^ (1 / 23 : ℝ)) ^ 23 = t := by
    rw [← Real.rpow_natCast (t ^ (1 / 23 : ℝ)) 23, ← Real.rpow_mul ht0.le]
    have hcast : (1 / 23 : ℝ) * ((23 : ℕ) : ℝ) = 1 := by norm_num
    rw [hcast, Real.rpow_one]
  have hy : (((10 : ℝ) ^ 15)⁻¹) ^ 23 = ((10 : ℝ) ^ 345)⁻¹ := by
    rw [inv_pow, ← pow_mul]
  have h345 : t ≤ ((10 : ℝ) ^ 345)⁻¹ := by
    calc t ≤ ((10 : ℝ) ^ 4000)⁻¹ := ht'
      _ ≤ ((10 : ℝ) ^ 345)⁻¹ := by
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 345)
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (345 : ℕ) ≤ 4000))
  have hz : t ≤ ((10 : ℝ) ^ 15)⁻¹ ^ 23 := by
    rw [hy]; exact h345
  have hmain : (t ^ (1 / 23 : ℝ)) ^ 23 ≤ (((10 : ℝ) ^ 15)⁻¹) ^ 23 := by
    rw [hx]; exact hz
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg ht0.le _) (by positivity)
    (by norm_num : (23 : ℕ) ≠ 0)).mp hmain

/-- **The far threshold in `X`-form**: `closeThresholdFS v μ = μt^{3/323}/(2¹⁴π)`
for `t = μ(a v)³` (the definition is `μK_ℓ^{-2}/(2¹⁴π)` and `K_ℓ = t^{-3/646}`). -/
private lemma closeThresholdFS_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    Work.BoseBoxFock.closeThresholdFS v μ
      = μ * (μ * (BoseGases.a v) ^ 3) ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi) := by
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hKl : (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
      = fsXp (μ * (BoseGases.a v) ^ 3) (-(3 / 2)) := rfl
  unfold Work.BoseBoxFock.closeThresholdFS
  rw [hKl]
  have hrpow : (fsXp (μ * (BoseGases.a v) ^ 3) (-(3 / 2))) ^ (-(2 : ℝ))
      = (μ * (BoseGases.a v) ^ 3) ^ (3 / 323 : ℝ) := by
    rw [fsXp_rpow ht0.le]
    rw [fsXp]
    congr 1
    norm_num
  rw [hrpow]

/-- **`ℓ² = a²t^{-326/323}`** (`ℓ = a·t^{-163/323}` squared). -/
private lemma ell_sq_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (Work.BoseFixR.ell v μ) ^ 2
      = (BoseGases.a v) ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (-(326 / 323) : ℝ) := by
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have h1 : Work.BoseFixR.ell v μ
      = BoseGases.a v * fsXp (μ * (BoseGases.a v) ^ 3) (-163) := by
    rw [Work.BoseFixR.ell]
    exact Work.BoseFixB1.sideAt_eq_fsXp hav hμ
  rw [h1, mul_pow, fsXp_pow ht0.le]
  congr 1
  rw [fsXp]
  congr 1
  norm_num

/-- **`√ε ≤ t^{1/16}`** from `ε ≤ t^{1/8}` (`bigMV_div_ell_cube_le_quarter`). -/
private lemma epsFar_sqrt_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hρ : 0 ≤ ρ)
    (ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1) :
    Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
      ≤ (μ * (BoseGases.a v) ^ 3) ^ (1 / 16 : ℝ) := by
  have h1 : Work.BoseFixR.All.epsFar v μ ρ ≤ (μ * (BoseGases.a v) ^ 3) ^ (1 / 8 : ℝ) := by
    rw [Work.BoseFixR.All.epsFar]
    have h2 := Work.BoseFixR.All.FarResidBaux.bigMV_div_ell_cube_le_quarter hav hμ hρ ht1
    have h3 : Real.sqrt (Work.BoseFixR.bigMV v μ / ((ρ + μ) * Work.BoseFixR.ell v μ ^ 3))
        ≤ Real.sqrt ((μ * (BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)) := Real.sqrt_le_sqrt h2
    have h4 : Real.sqrt ((μ * (BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ))
        = (μ * (BoseGases.a v) ^ 3) ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ μ * (BoseGases.a v) ^ 3)]
      congr 1
      norm_num
    rw [h4] at h3
    exact h3
  have h5 : Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
      ≤ Real.sqrt ((μ * (BoseGases.a v) ^ 3) ^ (1 / 8 : ℝ)) := Real.sqrt_le_sqrt h1
  have h6 : Real.sqrt ((μ * (BoseGases.a v) ^ 3) ^ (1 / 8 : ℝ))
      = (μ * (BoseGases.a v) ^ 3) ^ (1 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ μ * (BoseGases.a v) ^ 3)]
    congr 1
    norm_num
  rwa [h6] at h5

/-- **The `S`-row**: `ε₀ ≤ (a²/((S+1)R²10^{15}))^{323/320}` gives
`S R² ≤ a²t^{-320/323}/10^{15}`. -/
private lemma S_R2_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R S μ ε₀ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hR : 0 < R) (hS : 0 ≤ S)
    (htε : μ * (BoseGases.a v) ^ 3 ≤ ε₀)
    (hεS : ε₀ ≤ ((BoseGases.a v) ^ 2 / ((S + 1) * R ^ 2 * 10 ^ 15)) ^ (323 / 320 : ℝ)) :
    S * R ^ 2
      ≤ (BoseGases.a v) ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (-(320 / 323) : ℝ)
        * ((10 : ℝ) ^ 15)⁻¹ := by
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hX0 : 0 ≤ (BoseGases.a v) ^ 2 / ((S + 1) * R ^ 2 * 10 ^ 15) := by positivity
  have h1 : (μ * (BoseGases.a v) ^ 3) ^ (320 / 323 : ℝ)
      ≤ (BoseGases.a v) ^ 2 / ((S + 1) * R ^ 2 * 10 ^ 15) := by
    refine le_trans (Real.rpow_le_rpow ht0.le (le_trans htε hεS) (by norm_num)) ?_
    rw [← Real.rpow_mul hX0]
    norm_num
  have hD : (0 : ℝ) < (S + 1) * R ^ 2 * 10 ^ 15 := by positivity
  have h2 : (μ * (BoseGases.a v) ^ 3) ^ (320 / 323 : ℝ) * ((S + 1) * R ^ 2 * 10 ^ 15)
      ≤ (BoseGases.a v) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 hD.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hD)] at this
  have h3 : S * R ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (320 / 323 : ℝ) * (10 : ℝ) ^ 15
      ≤ (BoseGases.a v) ^ 2 := by
    have hSR : S * R ^ 2 ≤ (S + 1) * R ^ 2 := by nlinarith [hS, hR]
    have hnn : (0 : ℝ) ≤ (μ * (BoseGases.a v) ^ 3) ^ (320 / 323 : ℝ) * (10 : ℝ) ^ 15 :=
      by positivity
    have := mul_le_mul_of_nonneg_right hSR hnn
    nlinarith [this, h2]
  have h4 : S * R ^ 2
      ≤ (BoseGases.a v) ^ 2 / (10 ^ 15 * (μ * (BoseGases.a v) ^ 3) ^ (320 / 323 : ℝ)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 10 ^ 15)
      (Real.rpow_pos_of_pos ht0 _))]
    nlinarith [h3]
  calc S * R ^ 2
      ≤ (BoseGases.a v) ^ 2 / (10 ^ 15 * (μ * (BoseGases.a v) ^ 3) ^ (320 / 323 : ℝ)) := h4
    _ = (BoseGases.a v) ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (-(320 / 323) : ℝ)
          * ((10 : ℝ) ^ 15)⁻¹ := by
        rw [Real.rpow_neg ht0.le]
        field_simp

/-! ## 2. The scalar core -/

/-- **The scalar core of `extraLeA`.**  With `q = t^{6/323}`, `c = 10^{-15}`,
`r = √ε ≤ qc` and `z = S(R/ℓ)² ≤ qc`, the correction
`C = (1+64r)(1+100r)(1+z) − 1` is at most `q/(2³¹π³)`, and the far condition
`μt^{3/323}/(2¹⁴π) ≤ |ρ−μ|` turns that into `2πρ²C ≤ (ρ−μ)²`. -/
private lemma extraLeA_arith {A μ ρ R S g ε ℓ t : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hS : 0 ≤ S) (hℓ : 0 < ℓ) (hR : 0 < R)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hr : Real.sqrt ε ≤ t ^ (6 / 323 : ℝ) * ((10 : ℝ) ^ 15)⁻¹)
    (hg0 : 0 ≤ g) (hg : g ≤ 16 * Real.pi * A)
    (hz : S * (R / ℓ) ^ 2 ≤ t ^ (6 / 323 : ℝ) * ((10 : ℝ) ^ 15)⁻¹)
    (hfar : μ * t ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi) ≤ |ρ - μ|) :
    (1 / 2) * ρ ^ 2 * ℓ ^ 3 * g
        * ((1 + 64 * Real.sqrt ε) * (1 + 100 * Real.sqrt ε) * (1 + S * (R / ℓ) ^ 2) - 1)
      ≤ 4 * A * (ρ - μ) ^ 2 * ℓ ^ 3 := by
  set r := Real.sqrt ε with hrdef
  set z := S * (R / ℓ) ^ 2 with hzdef
  set q := t ^ (6 / 323 : ℝ) with hqdef
  set c := ((10 : ℝ) ^ 15)⁻¹ with hcdef
  set K := (2 : ℝ) ^ 31 * Real.pi ^ 3 with hKdef
  set C := (1 + 64 * r) * (1 + 100 * r) * (1 + z) - 1 with hCdef
  have hq0 : 0 < q := by rw [hqdef]; exact Real.rpow_pos_of_pos ht0 _
  have hq1 : q ≤ 1 := by rw [hqdef]; exact Real.rpow_le_one ht0.le ht1 (by norm_num)
  have hc0 : 0 ≤ c := by rw [hcdef]; exact inv_nonneg.mpr (by norm_num)
  have hc1 : c ≤ 1 := by rw [hcdef]; exact inv_le_one_of_one_le₀ (by norm_num)
  have hK0 : 0 < K := by
    rw [hKdef]
    exact mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) 31) (pow_pos Real.pi_pos 3)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := by rw [hzdef]; exact mul_nonneg hS (sq_nonneg _)
  have hrc : r ≤ q * c := by rw [hrdef, hqdef, hcdef]; exact hr
  have hzc : z ≤ q * c := by rw [hzdef, hqdef, hcdef]; exact hz
  have hrq : r ≤ q := by
    calc r ≤ q * c := hrc
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left hc1 hq0.le
      _ = q := by ring
  have hzq : z ≤ q := by
    calc z ≤ q * c := hzc
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left hc1 hq0.le
      _ = q := by ring
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ 64 * r := by positivity
    have h2 : (0 : ℝ) ≤ 100 * r := by positivity
    have h4 : (1 : ℝ) ≤ (1 + 64 * r) * (1 + 100 * r) := by nlinarith [h1, h2, sq_nonneg r]
    have hz1 : (1 : ℝ) ≤ 1 + z := by linarith
    have hmul := mul_le_mul_of_nonneg_right h4 (by linarith : (0 : ℝ) ≤ 1 + z)
    linarith [hmul, hz1]
  have h100 : 100 * r ≤ q := by
    have h100c : 100 * c ≤ 1 := by rw [hcdef]; norm_num
    calc 100 * r ≤ 100 * (q * c) := by linarith
      _ = q * (100 * c) := by ring
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left h100c (le_of_lt hq0)
      _ = q := by ring
  have hfac : (1 + 100 * r) * (1 + z) ≤ 4 := by
    have h1 : 1 + 100 * r ≤ 2 := by linarith
    have h2 : 1 + z ≤ 2 := by linarith
    have h3 : (0 : ℝ) ≤ 1 + z := by linarith
    have h4 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have := mul_le_mul h1 h2 h3 h4
    linarith [this]
  have hCb : C ≤ q * K⁻¹ := by
    have hexp : C = 64 * r * (1 + 100 * r) * (1 + z) + 100 * r * (1 + z) + z := by
      rw [hCdef]; ring
    rw [hexp]
    have hstep1 : 64 * r * (1 + 100 * r) * (1 + z) ≤ 256 * r := by
      have h := mul_le_mul_of_nonneg_left hfac (by positivity : (0 : ℝ) ≤ 64 * r)
      linarith [h]
    have hstep2 : 100 * r * (1 + z) ≤ 200 * r := by
      have hz2 : (1 : ℝ) + z ≤ 2 := by linarith [hzq, hq1]
      have h := mul_le_mul_of_nonneg_left hz2 (by positivity : (0 : ℝ) ≤ 100 * r)
      linarith [h]
    have hstep3 : 456 * r + z ≤ 457 * (c * q) := by linarith [hrc, hzc]
    have hfin : 457 * (c * q) ≤ q * K⁻¹ := by
      have hnum : (457 : ℝ) * c * K ≤ 1 := by
        have hpi : Real.pi ^ 3 ≤ 64 := by
          have h := pow_le_pow_left₀ (le_of_lt Real.pi_pos) (le_of_lt Real.pi_lt_four) 3
          norm_num at h
          exact h
        have h1 : (2 : ℝ) ^ 31 * Real.pi ^ 3 ≤ (2 : ℝ) ^ 31 * 64 :=
          mul_le_mul_of_nonneg_left hpi (by positivity)
        have h2 : (457 : ℝ) * c * K ≤ (457 : ℝ) * c * ((2 : ℝ) ^ 31 * 64) := by
          rw [hKdef]
          exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hc0)
        have h3 : (457 : ℝ) * c * ((2 : ℝ) ^ 31 * 64) ≤ 1 := by
          rw [hcdef]
          norm_num
        linarith [h2, h3]
      have h5 : 457 * (c * q) * K ≤ q := by
        calc 457 * (c * q) * K = ((457 : ℝ) * c * K) * q := by ring
          _ ≤ 1 * q := mul_le_mul_of_nonneg_right hnum hq0.le
          _ = q := by ring
      have h6 : 457 * (c * q) ≤ q / K := (le_div_iff₀ hK0).mpr h5
      simpa [div_eq_mul_inv] using h6
    calc 64 * r * (1 + 100 * r) * (1 + z) + 100 * r * (1 + z) + z
        ≤ 256 * r + 200 * r + z := by linarith [hstep1, hstep2]
      _ = 456 * r + z := by ring
      _ ≤ 457 * (c * q) := hstep3
      _ ≤ q * K⁻¹ := hfin
  have key : (1 / 2) * ρ ^ 2 * g * C ≤ 4 * A * (ρ - μ) ^ 2 := by
    rcases lt_or_ge ρ (2 * μ) with hcase | hcase
    · have hρ2 : ρ ^ 2 ≤ 4 * μ ^ 2 := by nlinarith [hρ, hcase, hμ]
      have hδ0 : 0 ≤ μ * t ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi) := by positivity
      have hsq : (μ * t ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2 ≤ (ρ - μ) ^ 2 :=
        sq_le_sq.mpr (by rw [abs_of_nonneg hδ0]; exact hfar)
      have hq3 : (t ^ (3 / 323 : ℝ)) ^ 2 = q := by
        rw [hqdef, ← Real.rpow_natCast (t ^ (3 / 323 : ℝ)) 2, ← Real.rpow_mul ht0.le]
        have hcast : (3 / 323 : ℝ) * ((2 : ℕ) : ℝ) = 6 / 323 := by norm_num
        rw [hcast]
      have hδ2 : (μ * t ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
          = μ ^ 2 * q / ((2 : ℝ) ^ 28 * Real.pi ^ 2) := by
        rw [div_pow, mul_pow, hq3]
        norm_num
        field_simp
        ring
      have e1 : (1 / 2) * ρ ^ 2 * g * C ≤ (1 / 2) * (4 * μ ^ 2) * (16 * Real.pi * A) * C := by
        have ha : (1 / 2) * ρ ^ 2 ≤ (1 / 2) * (4 * μ ^ 2) :=
          mul_le_mul_of_nonneg_left hρ2 (by norm_num)
        have hb : (1 / 2) * ρ ^ 2 * (16 * Real.pi * A)
            ≤ (1 / 2) * (4 * μ ^ 2) * (16 * Real.pi * A) :=
          mul_le_mul_of_nonneg_right ha (by positivity)
        have hc : (1 / 2) * ρ ^ 2 * g ≤ (1 / 2) * ρ ^ 2 * (16 * Real.pi * A) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
        calc (1 / 2) * ρ ^ 2 * g * C ≤ (1 / 2) * ρ ^ 2 * (16 * Real.pi * A) * C :=
              mul_le_mul_of_nonneg_right hc hC0
          _ ≤ (1 / 2) * (4 * μ ^ 2) * (16 * Real.pi * A) * C :=
              mul_le_mul_of_nonneg_right hb hC0
      have e2 : (1 / 2) * (4 * μ ^ 2) * (16 * Real.pi * A) * C
          ≤ 4 * A * (μ ^ 2 * q / ((2 : ℝ) ^ 28 * Real.pi ^ 2)) := by
        have ha : (1 / 2) * (4 * μ ^ 2) * (16 * Real.pi * A) * C
            = 32 * Real.pi * A * μ ^ 2 * C := by ring
        rw [ha]
        have hb : 32 * Real.pi * A * μ ^ 2 * C ≤ 32 * Real.pi * A * μ ^ 2 * (q * K⁻¹) :=
          mul_le_mul_of_nonneg_left hCb (by positivity)
        have hc : 32 * Real.pi * A * μ ^ 2 * (q * K⁻¹)
            = 4 * A * (μ ^ 2 * q / ((2 : ℝ) ^ 28 * Real.pi ^ 2)) := by
          rw [hKdef]
          field_simp
          ring
        linarith [hb, hc]
      have e3 : 4 * A * (μ ^ 2 * q / ((2 : ℝ) ^ 28 * Real.pi ^ 2)) ≤ 4 * A * (ρ - μ) ^ 2 := by
        rw [← hδ2]
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      linarith [e1, e2, e3]
    · have hsq : ρ ^ 2 / 4 ≤ (ρ - μ) ^ 2 := by nlinarith [hcase, hρ, hμ]
      have hC8 : C ≤ (8 * Real.pi)⁻¹ := by
        have h1 : q * K⁻¹ ≤ 1 * K⁻¹ := mul_le_mul_of_nonneg_right hq1 (by positivity)
        have hK8 : 8 * Real.pi ≤ K := by
          rw [hKdef]
          have hπ3 : (27 : ℝ) ≤ Real.pi ^ 3 := by
            have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
              (le_of_lt Real.pi_gt_three) 3
            norm_num at h
            exact h
          have h2 := mul_le_mul_of_nonneg_left hπ3 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 31)
          have h3 : (8 : ℝ) * Real.pi ≤ 8 * 4 := by linarith [Real.pi_lt_four]
          have h4 : (8 : ℝ) * 4 ≤ (2 : ℝ) ^ 31 * 27 := by norm_num
          linarith [h2, h3, h4]
        have h2 : 1 * K⁻¹ ≤ (8 * Real.pi)⁻¹ := by
          have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 * Real.pi) hK8
          simpa [one_div, one_mul] using this
        linarith [hCb, h1, h2]
      have e1 : (1 / 2) * ρ ^ 2 * g * C ≤ (1 / 2) * ρ ^ 2 * (16 * Real.pi * A) * C :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hC0
      have e2 : (1 / 2) * ρ ^ 2 * (16 * Real.pi * A) * C
          ≤ (1 / 2) * ρ ^ 2 * (16 * Real.pi * A) * ((8 * Real.pi)⁻¹) :=
        mul_le_mul_of_nonneg_left hC8 (by positivity)
      have e3 : (1 / 2) * ρ ^ 2 * (16 * Real.pi * A) * ((8 * Real.pi)⁻¹) = A * ρ ^ 2 := by
        field_simp
        ring
      have e4 : A * ρ ^ 2 ≤ 4 * A * (ρ - μ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hsq (le_of_lt hA)
        linarith [h]
      linarith [e1, e2, e3, e4]
  calc (1 / 2) * ρ ^ 2 * ℓ ^ 3 * g * C ≤ (4 * A * (ρ - μ) ^ 2) * ℓ ^ 3 := by
        rw [show (1 / 2) * ρ ^ 2 * ℓ ^ 3 * g * C = ((1 / 2) * ρ ^ 2 * g * C) * ℓ ^ 3 by ring]
        exact mul_le_mul_of_nonneg_right key (by positivity)
    _ = 4 * A * (ρ - μ) ^ 2 * ℓ ^ 3 := by ring

/-! ## 3. The row -/

theorem extraLeA {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ε₀ μ ρ S g : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < BoseGases.a v) (hR : 0 < R) (hρ : 0 ≤ ρ)
    (hfar : Work.BoseBoxFock.FarCondFS v μ ρ)
    (hS : 0 ≤ S) (hεS : ε₀ ≤ (BoseGases.a v ^ 2 / ((S + 1) * R ^ 2 * 10 ^ 15)) ^ (323 / 320 : ℝ))
    (hg0 : 0 ≤ g) (hg : g ≤ 16 * Real.pi * BoseGases.a v) :
    (1 / 2) * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * g
        * ((1 + 64 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
            * (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
            * (1 + S * (R / Work.BoseFixR.ell v μ) ^ 2) - 1)
      ≤ 4 * BoseGases.a v * (ρ - μ) ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 := by
  obtain ⟨hμ, htε, _⟩ := hAdm
  have hA : 0 < BoseGases.a v := hav
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hten : μ * (BoseGases.a v) ^ 3 ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := le_trans htε hε₀
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := by
    have h1 : (10 : ℝ) ^ (-(4000 : ℤ)) ≤ 1 := by
      have h2 : ((10 : ℝ) ^ 4000)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10))
      simpa [zpow_neg, one_div] using h2
    exact le_trans hten h1
  have hℓpos : 0 < Work.BoseFixR.ell v μ := Work.BoseBox.sideAt_pos hμ hav
  have hr : Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
      ≤ (μ * (BoseGases.a v) ^ 3) ^ (6 / 323 : ℝ) * ((10 : ℝ) ^ 15)⁻¹ :=
    le_trans (epsFar_sqrt_le hav hμ hρ ht1) (rpow_sixteenth_le ht0 ht1 hten)
  have hz : S * (R / Work.BoseFixR.ell v μ) ^ 2
      ≤ (μ * (BoseGases.a v) ^ 3) ^ (6 / 323 : ℝ) * ((10 : ℝ) ^ 15)⁻¹ := by
    have hSR := S_R2_le hμ hav hR hS htε hεS
    have hℓ2 := ell_sq_eq hμ hav
    have hsplit2 : (μ * (BoseGases.a v) ^ 3) ^ (6 / 323 : ℝ)
          * (μ * (BoseGases.a v) ^ 3) ^ (-(326 / 323) : ℝ)
        = (μ * (BoseGases.a v) ^ 3) ^ (-(320 / 323) : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      norm_num
    rw [div_pow, hℓ2]
    rw [← mul_div_assoc]
    rw [div_le_iff₀ (mul_pos (pow_pos hA 2) (Real.rpow_pos_of_pos ht0 _))]
    calc S * R ^ 2
        ≤ (BoseGases.a v) ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (-(320 / 323) : ℝ)
            * ((10 : ℝ) ^ 15)⁻¹ := hSR
      _ = (μ * (BoseGases.a v) ^ 3) ^ (6 / 323 : ℝ) * ((10 : ℝ) ^ 15)⁻¹
            * ((BoseGases.a v) ^ 2 * (μ * (BoseGases.a v) ^ 3) ^ (-(326 / 323) : ℝ)) := by
          rw [← hsplit2]
          ring
  have hfar' : μ * (μ * (BoseGases.a v) ^ 3) ^ (3 / 323 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi)
      ≤ |ρ - μ| := by
    rw [← closeThresholdFS_eq hμ hav]
    exact hfar
  exact extraLeA_arith hA hμ hρ hS hℓpos hR ht0 ht1 hr hg0 hg hz hfar'

end Work.BoseFixR.All
