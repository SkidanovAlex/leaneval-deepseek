import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1S.cruxCorrB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.corrArithHold` — the `Arith` node of the intersection-mean
correction (FS `eq:BSsliding2`'s mean-mismatch step), **proved**

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

## What this file is

The chapter's one-body kinetic half
(`Work.BoseFixB1.KineticHalf`, FS `eq:BSsliding2` / Bratteli--Solovej Thm 3.10) is reduced,
through `Work.BoseFixB1.KH.kineticHalf_le_mainWord`, to the *single* residual
`Work.BoseFixB1S.CorrInput v` (the `(E2)`+`(E3)` mean-mismatch step of
`FINDING_unprojected_route_B.md`: replacing the intersection-box mean `⨍_{B(u)}g` by the
anchored mean `⍍_{acube ℓ}g` inside the sliding window is paid by the flat anchored mass).

`Work.BoseFixB1S.cruxCorrB1` reduces `CorrInput` to six pieces
`CutWords`, `MeanSq`, `Marginal`, `Arith`, `ChiL2`, `PlanchMarg` via the **proved** assembly
`cruxCorrB1_of_pieces`.  Of those six, `CutWords`, `ChiL2` and `PlanchMarg` are already
proved and axiom-clean (`BoseFixB1S/corrCutWords.lean`, `corrChiScaleL2.lean`,
`corrPlanchMarg.lean`).  **This file closes `Arith`.**

`Arith` is the pure arithmetic of the payment: at FS's parameters
`ℓ = sideAt μ A = A·(μA³)^{-163/323}`, `d = (paramsAt μ A).d = (μA³)^{6/323}`,
`L = 1 + (ℓd)⁻¹ + |log d|`, the two terms produced by the cut-word estimate,

     ((2π)³)⁻¹ · C₀ ℓ⁻² C₁ L³ (ℓd)⁻³        (the `bsW` term) and
     ((2π)³)⁻¹ · 2 √(C₀ℓ⁻²) √(C₁ L³ (ℓd)⁻³ (2π)³ Cχ)   (the cross term),

are together at most the flat anchored mass `bValue/(4ℓ²)`, for all `μ` with `μA³ ≤ ε₀`
(the diluteness window).

## The proof

Everything is a monomial comparison in `t = μA³`.  With `u = |log t|` and
`hu : A⁻¹(μA³)^{157/323} = (ℓd)⁻¹ ≤ 1`:

* `L ≤ 1 + 1 + (6/323)u ≤ 2(1+u)`, so `L³ ≤ 8(1+u)³` (this is the constant `8` of the
  product bound and the `√8` of the cross bound);
* `ℓ⁻² = A⁻² (μA³)^{326/323}`, `((ℓd)³)⁻¹ = A⁻³(μA³)^{471/323}`, and
  `(μA³)^{326/323}·(μA³)^{471/323} = (μA³)^{797/323}`;
* the two estimates therefore read
  `C₀C₁A⁻⁵ t^{797/323}·8(1+u)³` and `2√(8C₀C₁Cχ(2π)³)A^{-5/2}t^{797/646}(1+u)^{3/2}`, and
  each is `(1/128)ℓ⁻²` times a factor which is `≤ 1` once `t^{471/323}(1+u)³` —
  respectively `t^{145/646}(1+u)^{3/2}` — is small.  "A positive power of `t` beats every
  power of `log t`" is `Work.BoseFixB1S.fsXpLogSmall`.

The threshold is `ε₀ = min 1 (min A^{323/157} (min δ_A δ_B))`: `A^{323/157}` makes
`(ℓd)⁻¹ ≤ 1` (i.e. `hu`), and `δ_A`, `δ_B` are the two logarithmic thresholds.

## Relation to the corpus

The two monomial estimates are stated in the corpus, with `sorry`, as
`Work.BoseFixB1S.CorrAux.prodTermBound` and `Work.BoseFixB1S.CorrAux.crossTermBound`
(the consumers of `Work.BoseFixB1S.corrArith`), and were developed -- but left with the
`sorry`-carrying `_local` names -- in the scratch file
`Submission/Work/BoseFixB1S/_corrArithDev.lean`.  This module carries them in a stable,
`sorry`-free place, under the same statements, and adds the assembled `Arith`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixB1B

open Work.BoseBox

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. "A positive power of `t` beats every power of `log t`" -/

/-- `K·(μA³)^{c/323}·(1+|log t|)^M ≤ 1` for all small `t > 0`.  This is
`Work.BoseFixB1S.fsXpLogSmall` at the constant `K⁻¹`, multiplied through by `K`. -/
lemma fsXp_mul_log_le_one_holds {K c M : ℝ} (hK : 0 < K) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      K * fsXp t c * (1 + |Real.log t|) ^ M ≤ 1 := by
  obtain ⟨ε, hε, h⟩ :=
    Work.BoseFixB1S.fsXpLogSmall (c := c) (M := M) (K := K⁻¹) (inv_pos.mpr hK) hc hM
  refine ⟨ε, hε, fun t ht htle => ?_⟩
  have h1 := h t ht htle
  have h2 : K * (fsXp t c * (1 + |Real.log t|) ^ M) ≤ K * K⁻¹ :=
    mul_le_mul_of_nonneg_left h1 hK.le
  rw [mul_inv_cancel₀ hK.ne'] at h2
  calc K * fsXp t c * (1 + |Real.log t|) ^ M
      = K * (fsXp t c * (1 + |Real.log t|) ^ M) := by ring
    _ ≤ 1 := h2

/-! ## 2. The product term -/

/-- **The `bsW`/`ℓ⁻²` term of the cut-word estimate is `8C₀C₁A⁻⁵ t^{797/323}(1+u)³`.**
The only input is `hu : (ℓd)⁻¹ = A⁻¹(μA³)^{157/323} ≤ 1`, which makes
`L = 1 + (ℓd)⁻¹ + |log d| ≤ 2(1+|log t|)` (since `|log d| = (6/323)|log t|`). -/
theorem prodTermBound_holds {C₀ C₁ A t : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (hA : 0 < A)
    (ht : 0 < t) (hu : A⁻¹ * fsXp t 157 ≤ 1) :
    (let ℓ : ℝ := A * fsXp t (-163)
     let d : ℝ := fsXp t 6
     let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
     C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
       ≤ 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3) := by
  have hℓinv : (A * fsXp t (-163))⁻¹ = A⁻¹ * fsXp t 163 := by
    rw [mul_inv, fsXp_inv ht]; norm_num
  have hprod : A * fsXp t (-163) * fsXp t 6 = A * fsXp t (-157) := by
    rw [mul_assoc, fsXp_mul ht]; norm_num
  have hprod0 : 0 < A * fsXp t (-163) * fsXp t 6 := by
    rw [hprod]; exact mul_pos hA (fsXp_pos ht)
  have hinv2 : (A * fsXp t (-163) * fsXp t 6)⁻¹ = A⁻¹ * fsXp t 157 := by
    rw [hprod, mul_inv, fsXp_inv ht]; norm_num
  have hlog : |Real.log (fsXp t 6)| = (6 / 323) * |Real.log t| := by
    have h1 : Real.log (fsXp t 6) = (6 / 323) * Real.log t := by
      rw [fsXp, Real.log_rpow ht]
    rw [h1, abs_mul]
    congr 1
    exact abs_of_nonneg (by norm_num)
  have hlogle : |Real.log (fsXp t 6)| ≤ |Real.log t| := by
    rw [hlog]
    calc (6 / 323) * |Real.log t| ≤ 1 * |Real.log t| :=
          mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
      _ = |Real.log t| := one_mul _
  have hL : 1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|
      ≤ 2 * (1 + |Real.log t|) := by
    rw [hinv2]
    linarith [hu, hlogle, abs_nonneg (Real.log t)]
  have hL0 : 0 ≤ 1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)| := by
    have h1 : 0 ≤ (A * fsXp t (-163) * fsXp t 6)⁻¹ := inv_nonneg.mpr hprod0.le
    linarith [abs_nonneg (Real.log (fsXp t 6))]
  have hsq : ((A * fsXp t (-163))⁻¹) ^ 2 = A ^ (-(2 : ℝ)) * fsXp t 326 := by
    rw [hℓinv, mul_pow]
    congr 1
    · rw [inv_pow, ← Real.rpow_natCast A 2, ← Real.rpow_neg hA.le]
      simp only [Nat.cast_ofNat]
    · rw [fsXp_pow ht.le]; norm_num
  have hcube : ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ = A ^ (-(3 : ℝ)) * fsXp t 471 := by
    rw [hprod, mul_pow]
    have h3 : (fsXp t (-157)) ^ 3 = fsXp t (-471) := by rw [fsXp_pow ht.le]; norm_num
    rw [h3, mul_inv, fsXp_inv ht]
    congr 1
    · rw [← Real.rpow_natCast A 3, ← Real.rpow_neg hA.le]
      simp only [Nat.cast_ofNat]
    · norm_num
  have hAmerge : A ^ (-(2 : ℝ)) * A ^ (-(3 : ℝ)) = A ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_add hA]; norm_num
  have hfmerge : fsXp t 326 * fsXp t 471 = fsXp t 797 := by
    rw [fsXp_mul ht]; norm_num
  have hnonneg : 0 ≤ C₀ * C₁ * ((A ^ (-(2 : ℝ)) * fsXp t 326) * (A ^ (-(3 : ℝ)) * fsXp t 471)) := by
    have h1 : 0 ≤ A ^ (-(2 : ℝ)) := Real.rpow_nonneg hA.le _
    have h2 : 0 ≤ A ^ (-(3 : ℝ)) := Real.rpow_nonneg hA.le _
    have h3 : 0 ≤ fsXp t 326 := fsXp_nonneg ht.le
    have h4 : 0 ≤ fsXp t 471 := fsXp_nonneg ht.le
    have hC : 0 ≤ C₀ * C₁ := mul_nonneg h₀ h₁
    exact mul_nonneg hC (mul_nonneg (mul_nonneg h1 h3) (mul_nonneg h2 h4))
  show C₀ * ((A * fsXp t (-163))⁻¹) ^ 2 * C₁ *
      (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
      ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹
    ≤ 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3
  calc C₀ * ((A * fsXp t (-163))⁻¹) ^ 2 * C₁ *
        (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
        ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹
      = C₀ * C₁ * ((A ^ (-(2 : ℝ)) * fsXp t 326) * (A ^ (-(3 : ℝ)) * fsXp t 471)) *
          (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 := by
        rw [hsq, hcube]; ring
    _ ≤ C₀ * C₁ * ((A ^ (-(2 : ℝ)) * fsXp t 326) * (A ^ (-(3 : ℝ)) * fsXp t 471)) *
          (2 * (1 + |Real.log t|)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 3) hnonneg
    _ = C₀ * C₁ * ((A ^ (-(2 : ℝ)) * A ^ (-(3 : ℝ))) * (fsXp t 326 * fsXp t 471)) *
          (8 * (1 + |Real.log t|) ^ 3) := by ring
    _ = 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3 := by
        rw [hAmerge, hfmerge]; ring

/-! ## 3. The cross term -/

/-- `sqrt` of a product of four nonnegative factors. -/
lemma sqrt_prod4_holds {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) :
    Real.sqrt (a * b * c * e) = Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt e := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg ha hb) hc) e, Real.sqrt_mul (mul_nonneg ha hb) c,
    Real.sqrt_mul ha b]

/-- **The cross term of the cut-word estimate.**  From the product bound: the product of the
two factors is at most `8C₀C₁Cχ(2π)³ A⁻⁵ t^{797/323}(1+u)³`, and taking square roots gives
the claim, since `√(A⁻⁵) = A^{-5/2}`, `√(t^{797/323}) = t^{(797/2)/323}` and
`√((1+u)³) = (1+u)^{3/2}`. -/
theorem crossTermBound_holds {C₀ C₁ Cχ A t : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (hχ : 0 ≤ Cχ)
    (hA : 0 < A) (ht : 0 < t) (hu : A⁻¹ * fsXp t 157 ≤ 1) :
    (let ℓ : ℝ := A * fsXp t (-163)
     let d : ℝ := fsXp t 6
     let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
     2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
       Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
       ≤ 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
           fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by
  have hP := prodTermBound_holds (C₀ := C₀) (C₁ := C₁) (A := A) (t := t) h₀ h₁ hA ht hu
  dsimp only at hP
  have hX0 : 0 ≤ C₀ * ((A * fsXp t (-163))⁻¹) ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  have hmerge : Real.sqrt (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
        Real.sqrt (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
          ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
      = Real.sqrt ((C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
          (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
            ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)) :=
    (Real.sqrt_mul hX0 _).symm
  have hP' : (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
        (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
          ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
      ≤ 8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3 *
          (A ^ (-(5 : ℝ)) * (fsXp t 797 * (1 + |Real.log t|) ^ 3)) := by
    calc (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
          (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
            ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
        = (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2 * C₁ *
            (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
            ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹) * ((2 * Real.pi) ^ 3 * Cχ) := by ring
      _ ≤ (8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3) *
            ((2 * Real.pi) ^ 3 * Cχ) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ = 8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3 *
            (A ^ (-(5 : ℝ)) * (fsXp t 797 * (1 + |Real.log t|) ^ 3)) := by ring
  have hF1 : 0 ≤ 8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3 := by positivity
  have hF2 : 0 ≤ A ^ (-(5 : ℝ)) := Real.rpow_nonneg hA.le _
  have hF3 : 0 ≤ fsXp t 797 := fsXp_nonneg ht.le
  have hF4 : 0 ≤ (1 + |Real.log t|) ^ 3 := pow_nonneg (by positivity) 3
  have hs1 : Real.sqrt (A ^ (-(5 : ℝ))) = A ^ (-(5 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hA.le]
    congr 1
    norm_num
  have hs3 : Real.sqrt (fsXp t 797) = fsXp t (797 / 2) := by
    rw [Real.sqrt_eq_rpow, fsXp, ← Real.rpow_mul ht.le, fsXp]
    congr 1
    norm_num
  have hs4 : Real.sqrt ((1 + |Real.log t|) ^ 3) = (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (1 + |Real.log t|) 3, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + |Real.log t|)]
    congr 1
    norm_num
  show 2 * Real.sqrt (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
      Real.sqrt (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
        ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
    ≤ 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
        fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)
  calc 2 * Real.sqrt (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
        Real.sqrt (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
          ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
      = 2 * (Real.sqrt (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
          Real.sqrt (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
            ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)) := by ring
    _ = 2 * Real.sqrt ((C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
          (C₁ * (1 + (A * fsXp t (-163) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3 *
            ((A * fsXp t (-163) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)) := by rw [hmerge]
    _ ≤ 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3 *
          (A ^ (-(5 : ℝ)) * (fsXp t 797 * (1 + |Real.log t|) ^ 3))) := by
          have h := Real.sqrt_le_sqrt hP'
          linarith
    _ = 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
          fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by
          rw [show 8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3 *
                (A ^ (-(5 : ℝ)) * (fsXp t 797 * (1 + |Real.log t|) ^ 3))
              = (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 : ℝ)) * fsXp t 797 *
                (1 + |Real.log t|) ^ 3 by ring]
          rw [sqrt_prod4_holds hF1 hF2 hF3 hF4, hs1, hs3, hs4]
          ring

/-! ## 4. The assembled `Arith` -/

/-- **The `Arith` node of the intersection-mean correction — PROVED.**

For every `C₀, C₁, Cχ ≥ 0` and every `A > 0` there is `ε₀ > 0` such that for every `μ > 0` with
`μA³ ≤ ε₀` (FS diluteness at `A = a v`) the sum of the `bsW` term and the cross term of the
cut-word estimate is at most the flat anchored mass `bValue/(4ℓ²)`, at FS's parameters
`ℓ = sideAt μ A`, `d = (paramsAt μ A).d`, `L = 1 + (ℓd)⁻¹ + |log d|`.

This is the statement `Work.BoseFixB1S.Arith` (the pure-arithmetic piece of the six into which
`Work.BoseFixB1S.cruxCorrB1` decomposes `Work.BoseFixB1S.CorrInput`, the last residual of the
one-body kinetic half).  The threshold is
`ε₀ = min 1 (min A^{323/157} (min δ_A δ_B))`, where `A^{323/157}` makes
`(ℓd)⁻¹ = A⁻¹(μA³)^{157/323} ≤ 1` and `δ_A`, `δ_B` are the two logarithmic thresholds supplied
by `fsXp_mul_log_le_one_holds` at the constants and exponents
`128·(2π)⁻³·8C₀C₁ · A⁻³`, `t^{471/323}(1+|log t|)³` and
`128·(2π)⁻³·2√(8C₀C₁Cχ(2π)³) · A^{-1/2}`, `t^{145/646}(1+|log t|)^{3/2}`. -/
theorem arith_holds : Work.BoseFixB1S.Arith := by
  intro C₀ C₁ Cχ A h₀ h₁ hχ hA
  set KA : ℝ := (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ))
    with hKAdef
  set KB : ℝ := (128 * (((2 * Real.pi) ^ 3)⁻¹)
      * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1) * A ^ (-(1 / 2 : ℝ))
    with hKBdef
  have hKApos : 0 < KA := by
    rw [hKAdef]
    have hA3 : 0 < A ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hA _
    have hC : 0 ≤ C₀ * C₁ := mul_nonneg h₀ h₁
    have hp : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have hX : 0 ≤ 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) := by nlinarith [hp, hC]
    exact mul_pos (by linarith) hA3
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    have hA3 : 0 < A ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hA _
    have hp : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have hs : 0 ≤ Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) := Real.sqrt_nonneg _
    have hX : 0 ≤ 128 * (((2 * Real.pi) ^ 3)⁻¹)
        * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) := by nlinarith [hp, hs]
    exact mul_pos (by linarith) hA3
  obtain ⟨δA, hδApos, hδA⟩ :=
    fsXp_mul_log_le_one_holds (K := KA) (c := 471) (M := ((3 : ℕ) : ℝ)) hKApos
      (by norm_num) (by norm_num)
  obtain ⟨δB, hδBpos, hδB⟩ :=
    fsXp_mul_log_le_one_holds (K := KB) (c := 145 / 2) (M := 3 / 2) hKBpos
      (by norm_num) (by norm_num)
  refine ⟨min 1 (min (A ^ (323 / 157 : ℝ)) (min δA δB)), ?_, ?_⟩
  · exact lt_min one_pos (lt_min (Real.rpow_pos_of_pos hA _) (lt_min hδApos hδBpos))
  · intro μ hμ hμle
    set t : ℝ := μ * A ^ 3 with ht_def
    have ht : 0 < t := by rw [ht_def]; positivity
    have htm : t ≤ min (A ^ (323 / 157 : ℝ)) (min δA δB) := hμle.trans (min_le_right _ _)
    have htA : t ≤ A ^ (323 / 157 : ℝ) := htm.trans (min_le_left _ _)
    have htδA : t ≤ δA := (htm.trans (min_le_right _ _)).trans (min_le_left _ _)
    have htδB : t ≤ δB := (htm.trans (min_le_right _ _)).trans (min_le_right _ _)
    have hu : A⁻¹ * fsXp t 157 ≤ 1 := by
      have h1 : fsXp t 157 ≤ A := by
        have h2 := Real.rpow_le_rpow ht.le htA (by norm_num : (0 : ℝ) ≤ (157 : ℝ) / 323)
        have h3 : (A ^ (323 / 157 : ℝ)) ^ ((157 : ℝ) / 323) = A := by
          rw [← Real.rpow_mul hA.le]; norm_num
        rw [h3] at h2
        simpa [fsXp] using h2
      calc A⁻¹ * fsXp t 157 ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 := by rw [inv_mul_cancel₀ hA.ne']
    let ℓ : ℝ := Work.BoseBox.sideAt μ A
    let d : ℝ := (Work.BoseBox.paramsAt μ A).d
    let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
    have hℓ : ℓ = A * fsXp t (-163) := by
      show Work.BoseBox.sideAt μ A = A * fsXp t (-163)
      rw [ht_def]
      exact Work.BoseFixB1.sideAt_eq_fsXp hA hμ
    have hd : d = fsXp t 6 := by
      show (Work.BoseBox.paramsAt μ A).d = fsXp t 6
      rw [ht_def]
      exact Work.BoseFixB1.d_eq_fsXp μ A
    have hℓpos : 0 < ℓ := by rw [hℓ]; exact mul_pos hA (fsXp_pos ht)
    have hX : C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
        ≤ 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3 := by
      have h := prodTermBound_holds (C₀ := C₀) (C₁ := C₁) (A := A) (t := t) h₀ h₁ hA ht hu
      dsimp only at h
      simp only [← hℓ, ← hd] at h
      exact h
    have hY : 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
        Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
        ≤ 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
            fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by
      have h := crossTermBound_holds (C₀ := C₀) (C₁ := C₁) (Cχ := Cχ) (A := A) (t := t)
        h₀ h₁ hχ hA ht hu
      dsimp only at h
      simp only [← hℓ, ← hd] at h
      exact h
    have hℓinv : (ℓ⁻¹) ^ 2 = A ^ (-(2 : ℝ)) * fsXp t 326 := by
      have h1 : ℓ⁻¹ = A⁻¹ * fsXp t 163 := by
        rw [hℓ, mul_inv, fsXp_inv ht, neg_neg]
      rw [h1, mul_pow]
      congr 1
      · rw [inv_pow, ← Real.rpow_natCast A 2, ← Real.rpow_neg hA.le]
        simp only [Nat.cast_ofNat]
      · rw [fsXp_pow ht.le]; norm_num
    have hKA : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
        fsXp t 471 * (1 + |Real.log t|) ^ 3 ≤ 1 := by
      have h := hδA t ht htδA
      rw [hKAdef] at h
      rw [Real.rpow_natCast] at h
      have hA3 : 0 ≤ A ^ (-(3 : ℝ)) := Real.rpow_nonneg hA.le _
      have hle : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ))
          ≤ (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ)) := by
        rw [add_mul, one_mul]
        linarith
      calc 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
              fsXp t 471 * (1 + |Real.log t|) ^ 3
          = (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ))) *
              (fsXp t 471 * (1 + |Real.log t|) ^ 3) := by ring
        _ ≤ ((128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ))) *
              (fsXp t 471 * (1 + |Real.log t|) ^ 3) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg (fsXp_nonneg ht.le) (by positivity))
        _ = ((128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ))) *
              fsXp t 471 * (1 + |Real.log t|) ^ 3 := by ring
        _ ≤ 1 := h
    have hKB : 128 * (((2 * Real.pi) ^ 3)⁻¹)
        * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
        A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) ≤ 1 := by
      have h := hδB t ht htδB
      rw [hKBdef] at h
      have hA3 : 0 ≤ A ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hA.le _
      have hle : 128 * (((2 * Real.pi) ^ 3)⁻¹)
            * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) * A ^ (-(1 / 2 : ℝ))
          ≤ (128 * (((2 * Real.pi) ^ 3)⁻¹)
              * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1)
            * A ^ (-(1 / 2 : ℝ)) := by
        rw [add_mul, one_mul]
        linarith
      calc 128 * (((2 * Real.pi) ^ 3)⁻¹)
              * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
              A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)
          = (128 * (((2 * Real.pi) ^ 3)⁻¹)
              * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) * A ^ (-(1 / 2 : ℝ)))
            * (fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by ring
        _ ≤ ((128 * (((2 * Real.pi) ^ 3)⁻¹)
              * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1) * A ^ (-(1 / 2 : ℝ)))
            * (fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg (fsXp_nonneg ht.le) (by positivity))
        _ = ((128 * (((2 * Real.pi) ^ 3)⁻¹)
              * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1) * A ^ (-(1 / 2 : ℝ)))
            * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by ring
        _ ≤ 1 := h
    have hXid : ((2 * Real.pi) ^ 3)⁻¹ *
          (8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3)
        = (1 / 128) * (ℓ⁻¹) ^ 2 *
          (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
            fsXp t 471 * (1 + |Real.log t|) ^ 3) := by
      rw [show (-(5 : ℝ)) = (-(2 : ℝ)) + (-(3 : ℝ)) by norm_num, Real.rpow_add hA]
      rw [show (797 : ℝ) = 326 + 471 by norm_num, ← fsXp_mul ht]
      rw [hℓinv]
      ring
    have hYid : ((2 * Real.pi) ^ 3)⁻¹ *
          (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
            fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ))
        = (1 / 128) * (ℓ⁻¹) ^ 2 *
          (128 * (((2 * Real.pi) ^ 3)⁻¹)
            * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
            A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by
      rw [show (-(5 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-(2 : ℝ)) by norm_num, Real.rpow_add hA]
      rw [show (797 / 2 : ℝ) = 145 / 2 + 326 by norm_num, ← fsXp_mul ht]
      rw [hℓinv]
      ring
    have hXA : ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
        ≤ (1 / 128) * (ℓ⁻¹) ^ 2 := by
      calc ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
              (8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3) :=
              mul_le_mul_of_nonneg_left hX (by positivity)
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 *
              (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
                fsXp t 471 * (1 + |Real.log t|) ^ 3) := hXid
        _ ≤ (1 / 128) * (ℓ⁻¹) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hKA (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 := by ring
    have hYA : ((2 * Real.pi) ^ 3)⁻¹ *
          (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        ≤ (1 / 128) * (ℓ⁻¹) ^ 2 := by
      calc ((2 * Real.pi) ^ 3)⁻¹ *
            (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
              Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
              (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
                fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hY (by positivity)
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 *
              (128 * (((2 * Real.pi) ^ 3)⁻¹)
                * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
                A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := hYid
        _ ≤ (1 / 128) * (ℓ⁻¹) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hKB (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 := by ring
    have hb : Work.BoseBox.bValue / (4 * ℓ ^ 2) = (1 / 64) * (ℓ⁻¹) ^ 2 := by
      rw [Work.BoseBox.bValue, inv_pow]
      field_simp
      ring
    show ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        ≤ Work.BoseBox.bValue / (4 * ℓ ^ 2)
    rw [hb]
    have hsplit : ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        = ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
          + ((2 * Real.pi) ^ 3)⁻¹ * (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)) := by ring
    rw [hsplit]
    linarith [hXA, hYA]

end Work.BoseFixB1B
