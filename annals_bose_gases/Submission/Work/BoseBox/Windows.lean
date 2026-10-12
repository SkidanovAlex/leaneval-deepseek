import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Nodes
import Submission.Work.ModeLatticeR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.Windows` — the a-priori windows and the error absorption at FS's parameters

This module is the **arithmetic layer** of the decoupled chapter: every quantity
that FS's proof of `thm:LHY-Box` compares is a monomial in the diluteness
`t = μa³`, and the comparisons that make the parameter choice *work* are
evaluated here once and for all.  Nothing in this file mentions a box size `L`
or a particle number: the parameters depend on `(μ, a)` only through `t = μa³`.

## Contents

* `nPlusWindow_paramsAt` — the excited-particle window of FS `eq:apriorinn+`,
  second conjunct, at FS's parameters: `K_ℓ⁵K_B³ = (μa³)^{-51/646} = X^{-51/2}`;
* `bigM_paramsAt` — the matrix window of FS `eq:DefM`: `𝓜 = X^{-1}(μa³)^{-1/4} =
  (μa³)^{-327/1292}`;
* `nPlusWindow_le_bigM` — the **nesting** used by FS `lem:LocMatrices` to place
  the `n₊`-interval of the Lieb–Solovej vector inside `[0,𝓜]`: for `μa³ ≤ 1`,
  `nPlusWindow ≤ 𝓜`;
* `inv_bigM_sq_paramsAt` — `𝓜^{-2} = (μa³)^{327/646}`: the reason the
  Lieb–Solovej error `C K_𝓜^{-2}μ²ℓ³(μa³)^{1/2}∫v` is *dominated* by the
  target's own error term `C μ²ℓ³(μa³)^{1/2+η₀}` (FS's `con:KMRKB` slack);
* `exists_lsError_le_slack` — **the absorption**: for `0 ≤ η₀ < 1/2` and small
  diluteness, `K (μa³)^{1/2}/𝓜² ≤ 4πa(μa³)^{1/2+η₀}`, i.e. the Lieb–Solovej
  error of `lem:LocMatrices` is absorbed by the *first* unit of the error
  coefficient of the target `Λ`;
* `Lambda_add_one`, `Lambda_le_of_C_le` — the monotonicity of the target
  `Λ(a,C,η₀,μ)` in `C`, i.e. the exact bookkeeping of that absorption.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The windows at FS's parameters -/

/-- **FS `eq:apriorinn+`'s excited window at FS's parameters**:
`nPlusWindow = K_ℓ⁵K_B³ = X^{-51/2}`.  The box side drops out completely:
`μℓ³ = K_ℓ³(μa³)^{-1/2}/a` contributes the factor `a` that cancels the
`(μa³)^{1/2}` of the window. -/
lemma nPlusWindow_paramsAt {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    nPlusWindow (paramsAt μ a) μ a = fsXp (μ * a ^ 3) (-(51 / 2)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hμa : 0 < μ * a := by positivity
  have hℓ : boxSide (paramsAt μ a) μ a
      = fsXp (μ * a ^ 3) (-(3 / 2)) * (μ * a) ^ (-(1 / 2 : ℝ)) := rfl
  have hKB : (paramsAt μ a).KB = fsXp (μ * a ^ 3) (-6) := rfl
  have hKl : (paramsAt μ a).Kl = fsXp (μ * a ^ 3) (-(3 / 2)) := rfl
  -- `(μa³)^{1/2} = (μa)^{1/2}·a`
  have hsqrt : (μ * a ^ 3) ^ (1 / 2 : ℝ) = (μ * a) ^ (1 / 2 : ℝ) * a := by
    have hsplit : μ * a ^ 3 = (μ * a) * a ^ 2 := by ring
    rw [hsplit, Real.mul_rpow (le_of_lt hμa) (by positivity)]
    have h2 : (a ^ 2 : ℝ) ^ (1 / 2 : ℝ) = a := by
      rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
      norm_num
    rw [h2]
  -- `μ·(μa)^{-3/2}·(μa)^{1/2}·a = 1`
  have hcancel : μ * (μ * a) ^ (-(3 / 2 : ℝ)) * ((μ * a) ^ (1 / 2 : ℝ) * a) = 1 := by
    have h1 : (μ * a) ^ (-(3 / 2 : ℝ)) * (μ * a) ^ (1 / 2 : ℝ) = (μ * a)⁻¹ := by
      rw [← Real.rpow_add hμa, show (-(3 / 2 : ℝ)) + (1 / 2 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    calc μ * (μ * a) ^ (-(3 / 2 : ℝ)) * ((μ * a) ^ (1 / 2 : ℝ) * a)
        = (μ * a) * ((μ * a) ^ (-(3 / 2 : ℝ)) * (μ * a) ^ (1 / 2 : ℝ)) := by ring
      _ = (μ * a) * (μ * a)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hμa)
  have hL3 : ((μ * a) ^ (-(1 / 2 : ℝ))) ^ 3 = (μ * a) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa.le]
    norm_num
  have hK3 : (fsXp (μ * a ^ 3) (-(3 / 2))) ^ 3 = fsXp (μ * a ^ 3) (-(9 / 2)) := by
    rw [fsXp_pow ht.le]
    norm_num
  have hK2 : (fsXp (μ * a ^ 3) (-(3 / 2))) ^ 2 = fsXp (μ * a ^ 3) (-3) := by
    rw [fsXp_pow ht.le]
    norm_num
  have hB3 : (fsXp (μ * a ^ 3) (-6)) ^ 3 = fsXp (μ * a ^ 3) (-18) := by
    rw [fsXp_pow ht.le]
    norm_num
  have hfac : fsXp (μ * a ^ 3) (-(9 / 2)) * fsXp (μ * a ^ 3) (-18)
      * fsXp (μ * a ^ 3) (-3) = fsXp (μ * a ^ 3) (-(51 / 2)) := by
    rw [fsXp_mul ht, fsXp_mul ht]
    norm_num
  dsimp [nPlusWindow]
  rw [hℓ, hKB, hKl, mul_pow, hL3, hK3, hB3, hK2, hsqrt]
  have hassemble : μ * (fsXp (μ * a ^ 3) (-(9 / 2)) * (μ * a) ^ (-(3 / 2 : ℝ)))
        * fsXp (μ * a ^ 3) (-18) * fsXp (μ * a ^ 3) (-3)
        * ((μ * a) ^ (1 / 2 : ℝ) * a)
      = fsXp (μ * a ^ 3) (-(9 / 2)) * fsXp (μ * a ^ 3) (-18) * fsXp (μ * a ^ 3) (-3)
        * (μ * (μ * a) ^ (-(3 / 2 : ℝ)) * ((μ * a) ^ (1 / 2 : ℝ) * a)) := by ring
  rw [hassemble, hcancel, mul_one, hfac]

/-- **The matrix window `𝓜` of FS `eq:DefM` at FS's parameters**:
`𝓜 = K_M(μa³)^{-1/4} = (μa³)^{-327/1292}`, in the `fsXp` monomial form
`X^{-327/4}`. -/
lemma bigM_paramsAt {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    bigM (paramsAt μ a) a μ = fsXp (μ * a ^ 3) (-(327 / 4)) := by
  have h1 : (μ * a ^ 3) ^ (-(1 / 4 : ℝ)) = fsXp (μ * a ^ 3) (-(323 / 4)) := by
    dsimp [fsXp]
    congr 1
    norm_num
  have ht : 0 < μ * a ^ 3 := by positivity
  have hKM : (paramsAt μ a).KM = fsXp (μ * a ^ 3) (-1) := rfl
  dsimp [bigM]
  rw [hKM, h1, fsXp_mul ht]
  norm_num

/-- **Nesting of the windows.**  At FS's parameters the a-priori excited window
`K_ℓ⁵K_B³ = X^{-51/2}` is *below* the matrix window `𝓜 = X^{-327/4}` for every
diluteness `μa³ ≤ 1` — this is the inclusion `[0,𝓜'+C K_B³K_ℓ⁵] ⊆ [0,𝓜]` of
FS's proof of `lem:LocMatrices`. -/
lemma nPlusWindow_le_bigM {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht1 : μ * a ^ 3 ≤ 1) :
    nPlusWindow (paramsAt μ a) μ a ≤ bigM (paramsAt μ a) a μ := by
  rw [nPlusWindow_paramsAt hμ ha, bigM_paramsAt hμ ha]
  exact fsXp_le_fsXp (by positivity) ht1 (by norm_num)

/-- Positivity of the matrix window at FS's parameters. -/
lemma bigM_pos_of_params {a μ : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 < bigM (paramsAt μ a) a μ := by
  have ht : 0 < μ * a ^ 3 := by positivity
  rw [bigM_paramsAt hμ ha]
  exact fsXp_pos ht

/-- **The reciprocal square of the matrix window**: `𝓜^{-2} = X^{327/2} =
(μa³)^{327/646}`.  This factor is what makes FS's Lieb–Solovej error
`C K_𝓜^{-2}μ²ℓ³(μa³)^{1/2}∫v` *smaller* than the target's error
`C μ²ℓ³(μa³)^{1/2+η₀}` (the power `327/646 ≈ 0.506 > 1/2`). -/
lemma inv_bigM_sq_paramsAt {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    1 / bigM (paramsAt μ a) a μ ^ 2 = fsXp (μ * a ^ 3) (327 / 2) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have h2 : (fsXp (μ * a ^ 3) (-(327 / 4))) ^ 2 = fsXp (μ * a ^ 3) (-(327 / 2)) := by
    rw [fsXp_pow ht.le]
    norm_num
  rw [bigM_paramsAt hμ ha, h2, one_div, fsXp_inv ht]
  congr 1
  ring

/-- The window in exponent form: `nPlusWindow = (μa³)^{-51/646}`, the power that
`con:KBellKM` places below `𝓜`. -/
lemma nPlusWindow_paramsAt_neg {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    nPlusWindow (paramsAt μ a) μ a = (μ * a ^ 3) ^ (-(51 / 646) : ℝ) := by
  rw [nPlusWindow_paramsAt hμ ha]
  dsimp [fsXp]
  congr 1
  norm_num

/-! ## 2. The absorption of the Lieb–Solovej error -/

/-- The pure arithmetic core of the absorption: for `0 < t`, `0 ≤ K` and
`t^{2/323−η₀} ≤ 4πa/(K+1)`,

    `K·t^{327/646} ≤ 4πa·t^{1/2+η₀}`,

i.e. FS's Lieb–Solovej loss `K𝓜^{-2} = K t^{327/646}` is paid by the target's error
coefficient `4πa(μa³)^{1/2+η₀}` as soon as `η₀ < 2/323` (the surplus exponent of
`𝓜^{-2} = (μa³)^{327/646}` over `(μa³)^{1/2}` is `4/646 = 2/323`). -/
lemma lsError_arith {t a η₀ K : ℝ} (ht : 0 < t) (ha : 0 < a) (hη₀ : 0 ≤ η₀)
    (hη₂ : η₀ < 2 / 323) (hK : 0 ≤ K)
    (hte : t ^ (2 / 323 - η₀) ≤ 4 * π * a / (K + 1)) :
    K * t ^ (327 / 646 : ℝ) ≤ 4 * π * a * t ^ (1 / 2 + η₀) := by
  set e : ℝ := 2 / 323 - η₀ with hedef
  have he : 0 < e := by rw [hedef]; linarith
  have hKle : K * t ^ e ≤ 4 * π * a := by
    have h1 : K * t ^ e ≤ K * (4 * π * a / (K + 1)) := mul_le_mul_of_nonneg_left hte hK
    have h2 : K * (4 * π * a / (K + 1)) ≤ 4 * π * a := by
      have hK1 : 0 < K + 1 := by linarith
      calc K * (4 * π * a / (K + 1)) ≤ (K + 1) * (4 * π * a / (K + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 4 * π * a := by field_simp
    linarith
  have hA : t ^ (327 / 646 : ℝ) = t ^ e * t ^ (1 / 2 + η₀) := by
    rw [← Real.rpow_add ht]
    congr 1
    rw [hedef]
    norm_num
  rw [hA]
  calc K * (t ^ e * t ^ (1 / 2 + η₀)) = (K * t ^ e) * t ^ (1 / 2 + η₀) := by ring
    _ ≤ (4 * π * a) * t ^ (1 / 2 + η₀) :=
        mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg ht.le _)

/-- **The absorption lemma** (FS `lem:LocMatrices`'s loss against the target's error).
For `0 ≤ η₀ < 2/323` there is `ε₀ > 0` such that for every diluteness `t = μa³ ≤ ε₀`

    `K/𝓜² ≤ 4π a (μa³)^{1/2+η₀}`,

i.e. FS's Lieb–Solovej loss `C K_𝓜^{-2}μ²ℓ³(μa³)^{1/2}∫v = C𝓜^{-2}μ²ℓ³∫v`
(`K_𝓜^{-2} = 𝓜^{-2}(μa³)^{-1/2}`, `𝓜 = K_M(μa³)^{-1/4}`) is dominated by one unit of
the target's error coefficient.  The admissible exponent range is `η₀ < 2/323`
(the surplus `4/646` of `𝓜^{-2}` over `1/2`), which contains the paper's
`η_FS = 1/1615` and the audit's `1/2000`. -/
theorem exists_lsError_le_slack {a η₀ K : ℝ} (ha : 0 < a) (hη₀ : 0 ≤ η₀)
    (hη₂ : η₀ < 2 / 323) (hK : 0 ≤ K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε₀ →
      K / bigM (paramsAt μ a) a μ ^ 2 ≤ 4 * π * a * (μ * a ^ 3) ^ (1 / 2 + η₀) := by
  have hp : 0 < 2 / 323 - η₀ := by linarith
  have hbase : 0 < (4 * π * a) / (K + 1) := by positivity
  refine ⟨min 1 (((4 * π * a) / (K + 1)) ^ (1 / (2 / 323 - η₀))), lt_min one_pos
    (Real.rpow_pos_of_pos hbase _), ?_⟩
  intro μ hμ hle
  have ht : 0 < μ * a ^ 3 := by positivity
  have hle' : μ * a ^ 3 ≤ ((4 * π * a) / (K + 1)) ^ (1 / (2 / 323 - η₀)) :=
    le_trans hle (min_le_right _ _)
  have hte : (μ * a ^ 3) ^ (2 / 323 - η₀) ≤ 4 * π * a / (K + 1) := by
    have h1 : (μ * a ^ 3) ^ (2 / 323 - η₀)
        ≤ (((4 * π * a) / (K + 1)) ^ (1 / (2 / 323 - η₀))) ^ (2 / 323 - η₀) :=
      Real.rpow_le_rpow (le_of_lt ht) hle' hp.le
    have h2 : (((4 * π * a) / (K + 1)) ^ (1 / (2 / 323 - η₀))) ^ (2 / 323 - η₀)
        = 4 * π * a / (K + 1) := by
      rw [← Real.rpow_mul (le_of_lt hbase)]
      have h3 : (1 / (2 / 323 - η₀)) * (2 / 323 - η₀) = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hp)]
      rw [h3, Real.rpow_one]
    linarith [h2]
  have hfs : fsXp (μ * a ^ 3) (327 / 2) = (μ * a ^ 3) ^ (327 / 646 : ℝ) := by
    dsimp [fsXp]
    congr 1
    norm_num
  have hbig : bigM (paramsAt μ a) a μ ^ 2 = fsXp (μ * a ^ 3) (-(327 / 2)) := by
    rw [bigM_paramsAt hμ ha, fsXp_pow ht.le]
    norm_num
  have hbig' : fsXp (μ * a ^ 3) (-(327 / 2)) = ((μ * a ^ 3) ^ (327 / 646 : ℝ))⁻¹ := by
    rw [← hfs, fsXp_inv ht]
  rw [div_eq_mul_inv, hbig, hbig', inv_inv]
  exact lsError_arith ht ha hη₀ hη₂ hK hte

/-! ## 3. The target's error coefficient and its monotonicity in `C` -/

/-- The error coefficient of the target: raising `C` by one adds exactly
`4πρ²a(ρa³)^{1/2+η₀}` to the *negative* value `Λ`. -/
lemma Lambda_add_one (a C η₀ ρ : ℝ) :
    Lambda a (C + 1) η₀ ρ = Lambda a C η₀ ρ - 4 * π * ρ ^ 2 * a * (ρ * a ^ 3) ^ (1 / 2 + η₀) := by
  dsimp [Lambda]
  ring

/-- Monotonicity of `Λ` in the error coefficient. -/
lemma Lambda_le_of_C_le {a η₀ ρ C C' : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (h : C ≤ C') :
    Lambda a C' η₀ ρ ≤ Lambda a C η₀ ρ := by
  have h1 : 0 ≤ 4 * π * ρ ^ 2 * a * (ρ * a ^ 3) ^ (1 / 2 + η₀) := by
    have : 0 ≤ (ρ * a ^ 3) ^ (1 / 2 + η₀) := Real.rpow_nonneg (by positivity) _
    positivity
  have hkey : Lambda a C' η₀ ρ - Lambda a C η₀ ρ
      = -(4 * π * ρ ^ 2 * a * (ρ * a ^ 3) ^ (1 / 2 + η₀)) * (C' - C) := by
    dsimp [Lambda]
    ring
  have : Lambda a C' η₀ ρ - Lambda a C η₀ ρ ≤ 0 := by
    rw [hkey]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h1) (by linarith)
  linarith

/-- **The boundary-loss absorption.**  FS's `thm:CompareBoxEnergy` gives the factor
`((L+ℓ)/ℓ)³` (the localisation region `ℓ⁻¹(Ω+B(0,ℓ/2))` has volume `|Ω+B(0,ℓ/2)|/ℓ³`
in units of the box volume `L³`), whereas the per-state box bound is stated with
`L³`.  The difference `((L+ℓ)/L)³ − 1 → 0` is paid by **one unit** of the error
coefficient of `Λ`: for small density there is `L₀ > 0` with

    `L³·Λ(a, C+1, η₀, ρ) ≤ (L+ℓ)³·Λ(a, C, η₀, ρ)`   for all `L ≥ L₀`.

This is the arithmetic behind FS's remark that `|Ω+B(0,ℓ/2)|/|Ω| → 1` in the
thermodynamic limit.  The hypothesis `lhyC√(ρa³) < 1` makes the LHY bracket
`1 − lhyC√(ρa³) + C(ρa³)^{1/2+η₀}` positive, which is what lets the loss be
inverted. -/
lemma Lambda_factor_absorb {a ρ ℓ C η₀ : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hC : 0 ≤ C) (h1 : lhyC * Real.sqrt (ρ * a ^ 3) < 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      L ^ 3 * Lambda a (C + 1) η₀ ρ ≤ (L + ℓ) ^ 3 * Lambda a C η₀ ρ := by
  set t : ℝ := ρ * a ^ 3 with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  set s : ℝ := 1 / 2 + η₀ with hsdef
  have hts : 0 < t ^ s := Real.rpow_pos_of_pos ht _
  set lam : ℝ := 1 - lhyC * Real.sqrt t + C * t ^ s with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef]
    linarith [mul_nonneg hC hts.le]
  set d : ℝ := t ^ s / lam with hddef
  have hd : 0 < d := div_pos hts hlam
  set e : ℝ := (1 + d) ^ (1 / 3 : ℝ) - 1 with hedef
  have he : 0 < e := by
    have : 1 < (1 + d) ^ (1 / 3 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
    rw [hedef]
    linarith
  refine ⟨max 1 (max ℓ (7 * ℓ / d)), by positivity, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLℓ : ℓ ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL7 : 7 * ℓ / d ≤ L :=
    le_trans (le_trans (le_max_right ℓ (7 * ℓ / d)) (le_max_right 1 (max ℓ (7 * ℓ / d)))) hL
  have hL3 : 0 < L ^ 3 := pow_pos hLpos 3
  have hx0 : 0 ≤ ℓ / L := div_nonneg hℓ hLpos.le
  have hx1 : ℓ / L ≤ 1 := (div_le_one hLpos).mpr hLℓ
  have hx7 : 7 * (ℓ / L) ≤ d := by
    have h1 : 7 * ℓ ≤ d * L := by
      rw [div_le_iff₀ hd] at hL7
      linarith
    rw [mul_div_assoc', div_le_iff₀ hLpos]
    linarith
  have hkey : ((L + ℓ) / L) ^ 3 ≤ 1 + d := by
    have hsplit : (L + ℓ) / L = 1 + ℓ / L := by
      field_simp
    rw [hsplit]
    have hx2 : (ℓ / L) ^ 2 ≤ ℓ / L := by nlinarith [hx0, hx1]
    have hx3 : (ℓ / L) ^ 3 ≤ ℓ / L := by nlinarith [hx0, hx1, hx2]
    have hexp : (1 + ℓ / L) ^ 3 = 1 + 3 * (ℓ / L) + 3 * (ℓ / L) ^ 2 + (ℓ / L) ^ 3 := by
      ring
    rw [hexp]
    linarith
  have hfac : ((L + ℓ) / L) ^ 3 - 1 = ((L + ℓ) ^ 3 - L ^ 3) / L ^ 3 := by
    rw [div_pow]
    field_simp
  have hbound : (L + ℓ) ^ 3 - L ^ 3 ≤ d * L ^ 3 := by
    have h2 : ((L + ℓ) / L) ^ 3 - 1 ≤ d := by linarith
    rw [hfac] at h2
    have h3 := (div_le_iff₀ hL3).mp h2
    linarith
  have hΛl : Lambda a C η₀ ρ = -(4 * π * ρ ^ 2 * a) * lam := by
    rw [hlamdef, htdef, hsdef]
    dsimp [Lambda]
    ring
  have hΛo : Lambda a (C + 1) η₀ ρ = -(4 * π * ρ ^ 2 * a) * (lam + t ^ s) := by
    rw [hlamdef, htdef, hsdef]
    dsimp [Lambda]
    ring
  rw [hΛl, hΛo]
  have hK : 0 < 4 * π * ρ ^ 2 * a := by positivity
  have hmult : ((L + ℓ) ^ 3 - L ^ 3) * lam ≤ t ^ s * L ^ 3 := by
    have h4 : (L + ℓ) ^ 3 - L ^ 3 ≤ (t ^ s / lam) * L ^ 3 := by
      rw [← hddef]
      exact hbound
    have h5 := mul_le_mul_of_nonneg_right h4 hlam.le
    have h6 : (t ^ s / lam) * L ^ 3 * lam = t ^ s * L ^ 3 := by
      field_simp
    linarith [h5, h6]
  have hkey2 : (L + ℓ) ^ 3 * lam ≤ L ^ 3 * (lam + t ^ s) := by nlinarith [hmult]
  nlinarith [hkey2, hK, hL3]

/-- **The a-priori parameter bound `J ≤ K_B³` for small diluteness** (FS
`thm:aprioribounds`'s hypothesis): at FS's parameters `K_B³ = (μa³)^{-18/323}`, so
any *fixed* `J' > 0` satisfies `J' ≤ K_B³` as soon as `μa³ ≤ J'^{-323/18}`. -/
lemma KB_cube_ge {a μ J' : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hJ' : 0 < J')
    (hle : μ * a ^ 3 ≤ J' ^ (-(323 / 18 : ℝ))) :
    J' ≤ (paramsAt μ a).KB ^ 3 := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hKB : (paramsAt μ a).KB ^ 3 = (μ * a ^ 3) ^ (-(18 / 323 : ℝ)) := by
    dsimp [paramsAt, fsParams, fsXp]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  rw [hKB]
  -- raise the hypothesis to a positive power and take reciprocals
  have h4 : J' ^ (323 / 18 : ℝ) ≤ (μ * a ^ 3)⁻¹ := by
    have h5 : ((J' ^ (-(323 / 18 : ℝ)))⁻¹) ≤ ((μ * a ^ 3)⁻¹) :=
      inv_anti₀ (by positivity) hle
    have h6 : (J' ^ (-(323 / 18 : ℝ)))⁻¹ = J' ^ (323 / 18 : ℝ) := by
      rw [← Real.rpow_neg hJ'.le]
      congr 1
      ring
    rwa [h6] at h5
  have h7 : (J' ^ (323 / 18 : ℝ)) ^ (18 / 323 : ℝ) ≤ ((μ * a ^ 3)⁻¹) ^ (18 / 323 : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hJ'.le _) h4 (by norm_num)
  have h8 : (J' ^ (323 / 18 : ℝ)) ^ (18 / 323 : ℝ) = J' := by
    rw [← Real.rpow_mul hJ'.le]
    norm_num
  have h9 : ((μ * a ^ 3)⁻¹) ^ (18 / 323 : ℝ) = (μ * a ^ 3) ^ (-(18 / 323 : ℝ)) := by
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  rwa [h8, h9] at h7

end Work.BoseBox
