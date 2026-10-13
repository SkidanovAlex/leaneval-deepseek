/-
Copyright: work module for the Elgindi finite-time singularity project.

# `poleBoundOfSourcePow`

If `Lzero1 u = g` on `(0, π/2)` and the source obeys the *power* bound

  `|g θ| ≤ C (θ^{-(R+2)} + (π/2 - θ)^{-(R+2)})`,   `R > 1`,

then the slice itself obeys the pole bound with two powers less

  `|u θ| ≤ C' (θ^{-R} + (π/2 - θ)^{-R})`.

This is the two-sided gain-of-two-powers statement for the angular operator
`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, exact at both endpoints: near `θ = 0` (an ordinary
point) the potential solution `θ^{-R}` produces the source `-R(R+1)θ^{-(R+2)}`, and near
`θ = π/2` (a regular singular point with indicial exponents `±1`) the potential solution
`(π/2-θ)^{-R}` produces `-(R²-1)(π/2-θ)^{-(R+2)}`.

## Route

Write `y = sin 2θ` (the regular solution of `Lzero1 y = 0`), `D u = cos θ (u y' - u' y)`
and `R u = u / y`.  The two exact identities (`H2W.Lzero1Growth`)

  `(D u)' = 2 · Lzero1 u · sinθcos²θ`,   `(R u)' = - D u / (cos θ · sin²2θ)`

give, on each half `(0, π/4]` and `[π/4, π/2)` separately:

* `|D u θ| ≤ |D u (π/4)| + 2 ∫ sinθcos²θ |g|` (`truncBounds`), and the source integral is
  bounded by `const · θ^{-R}` resp. `const · (π/2-θ)^{1-R}` (`sourceBounds`);
* the kernel `1/(cos θ sin²2θ)` behaves like `π²/(8θ²)` near `0` and like
  `π³/(32(π/2-θ)³)` near `π/2` (`powToolkit`), so integrating the bound on `D u` against the
  kernel and using `∫_θ^{π/4} s^{-2} ≤ 1/θ` resp. `∫_{π/4}^θ (π/2-s)^{-3} ≤ (π/2-θ)^{-2}`
  gives `|R u θ| ≤ R₀ + const (θ^{-R-1} + ...)`;
* finally `u = R u · sin 2θ` and `sin 2θ ≤ 2θ` (resp. `≤ 2(π/2-θ)`), which converts the
  exponents `-R-1` and `-1` into `-R`.

Since both half-intervals are covered and `R > 1` implies `θ^{-R} ≥ 1` on `(0, π/4]` and
`(π/2-θ)^{-R} ≥ 1` on `[π/4, π/2)`, the intermediate constant pieces are absorbed.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.powToolkit
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.truncBounds
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.sourceBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.H2W.LzeroGrowth

/-! ## Elementary `rpow` algebra -/

/-- `1 ≤ x ^ (-R)` for `0 < x ≤ 1` and `R > 0`. -/
private theorem one_le_rpow_neg {x R : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hR : 0 < R) :
    1 ≤ x ^ (-R) := by
  have hinv : 1 ≤ x⁻¹ := by
    have h := div_le_div_of_nonneg_right hx1 hx.le
    rwa [div_self (ne_of_gt hx), one_div] at h
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hinv hR.le
  rw [Real.inv_rpow hx.le R, ← Real.rpow_neg hx.le R] at h
  simpa using h

/-- `y ^ (-R) ≤ x ^ (-R)` for `0 < x ≤ y` and `R > 0`. -/
private theorem rpow_neg_mono {x y R : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hR : 0 < R) :
    y ^ (-R) ≤ x ^ (-R) :=
  Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)

/-- `y ^ (1 - R) ≤ x ^ (1 - R)` for `0 < x ≤ y` and `1 < R`. -/
private theorem rpow_one_sub_mono {x y R : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hR : 1 < R) :
    y ^ (1 - R) ≤ x ^ (1 - R) :=
  Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)

/-- `x ^ (-2) * x = x ^ (-1)` for `x > 0`. -/
private theorem rpow_neg_two_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ (-2 : ℝ) * x = x ^ (-1 : ℝ) := by
  have h : x ^ (-2 : ℝ) * x = x ^ (-2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
  rw [h, ← Real.rpow_add hx (-2 : ℝ) (1 : ℝ)]
  congr 1
  norm_num

/-- `x ^ (1 - R) * x ^ (-1) = x ^ (-R)` for `x > 0`. -/
private theorem rpow_one_sub_mul_neg_one {x R : ℝ} (hx : 0 < x) :
    x ^ (1 - R) * x ^ (-1 : ℝ) = x ^ (-R) := by
  rw [← Real.rpow_add hx (1 - R) (-1 : ℝ)]
  congr 1
  ring

/-- `x ^ (-1) ≤ x ^ (-R)` for `0 < x ≤ 1` and `1 < R`. -/
private theorem rpow_neg_one_le {x R : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hR : 1 < R) :
    x ^ (-1 : ℝ) ≤ x ^ (-R) := by
  have h1 : 1 ≤ x ^ (-(R - 1)) := one_le_rpow_neg hx hx1 (by linarith)
  have h2 : x ^ (-R) = x ^ (-1 : ℝ) * x ^ (-(R - 1)) := by
    rw [← Real.rpow_add hx (-1 : ℝ) (-(R - 1))]
    congr 1
    ring
  have h3 : 0 ≤ x ^ (-1 : ℝ) := Real.rpow_nonneg hx.le _
  calc x ^ (-1 : ℝ) = x ^ (-1 : ℝ) * 1 := by ring
    _ ≤ x ^ (-1 : ℝ) * x ^ (-(R - 1)) := mul_le_mul_of_nonneg_left h1 h3
    _ = x ^ (-R) := h2.symm

/-- `(π²/8)/s² = (π²/8)·s^(-2)` for `s > 0`. -/
private theorem ker_rewrite (s : ℝ) (hs : 0 < s) :
    (Real.pi ^ 2 / 8) / s ^ 2 = (Real.pi ^ 2 / 8) * s ^ (-2 : ℝ) := by
  have h : s ^ (-2 : ℝ) = 1 / s ^ 2 := by
    rw [one_div, Real.rpow_neg hs.le, Real.rpow_two]
  rw [h]
  simp only [div_eq_mul_inv, one_mul]

/-- `(π³/32)/s³ = (π³/32)·s^(-3)` for `s > 0`. -/
private theorem ker_rewrite' (s : ℝ) (hs : 0 < s) :
    (Real.pi ^ 3 / 32) / s ^ 3 = (Real.pi ^ 3 / 32) * s ^ (-3 : ℝ) := by
  have h : s ^ (-3 : ℝ) = 1 / s ^ 3 := by
    rw [one_div, Real.rpow_neg hs.le]
    congr 1
    exact Real.rpow_natCast s 3
  rw [h]
  simp only [div_eq_mul_inv, one_mul]

/-! ## The left half `(0, π/4]` -/

private theorem poleBound_left {u : ℝ → ℝ} {R Ks : ℝ} (hR : 1 < R)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) (hKs : 0 ≤ Ks)
    (hsL : ∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4),
      (∫ s in θ..(Real.pi / 4), Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|)
        ≤ Ks * θ ^ (-R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4), |u θ| ≤ C * θ ^ (-R) := by
  obtain ⟨hpowL, _hpowR, hIntSq, _hDr1, _hDr2, _hCube, _hDt1, _hDt2⟩ := powToolkit R hR
  obtain ⟨hTB1, _hTB2, hTB3, _hTB4⟩ := truncBounds u hu
  have hpi : 0 < Real.pi := Real.pi_pos
  have hRpos : 0 < R := by linarith
  set D0 : ℝ := |Dfun u (Real.pi / 4)| with hD0def
  set R0 : ℝ := |Rfun u (Real.pi / 4)| with hR0def
  have hD0nn : 0 ≤ D0 := by rw [hD0def]; exact abs_nonneg _
  have hR0nn : 0 ≤ R0 := by rw [hR0def]; exact abs_nonneg _
  set KDL : ℝ := 2 * Ks with hKDLdef
  have hKDLnn : 0 ≤ KDL := by rw [hKDLdef]; linarith
  set C1 : ℝ := 2 * (Real.pi / 4) * R0 + D0 * (Real.pi ^ 2 / 4) + KDL * (Real.pi ^ 2 / 4)
    with hC1def
  have hC1nn : 0 ≤ C1 := by
    rw [hC1def]
    have h1 : 0 ≤ 2 * (Real.pi / 4) * R0 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith [hpi])) hR0nn
    have h2 : 0 ≤ D0 * (Real.pi ^ 2 / 4) := mul_nonneg hD0nn (by positivity)
    have h3 : 0 ≤ KDL * (Real.pi ^ 2 / 4) := mul_nonneg hKDLnn (by positivity)
    linarith
  refine ⟨C1, hC1nn, ?_⟩
  intro θ hθ
  have hθpos : 0 < θ := hθ.1
  have hθle : θ ≤ Real.pi / 4 := hθ.2
  have hθi : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, hpi]⟩
  have hθ1 : θ ≤ 1 := by linarith [hθ.2, Real.pi_lt_four]
  have hθR1 : 1 ≤ θ ^ (-R) := one_le_rpow_neg hθpos hθ1 hRpos
  -- the `Dfun` bound at every `s ∈ (0, π/4]`
  have Dbound : ∀ s ∈ Set.Ioc (0:ℝ) (Real.pi / 4), |Dfun u s| ≤ D0 + KDL * s ^ (-R) := by
    intro s hs
    have hD := hTB1 s hs
    have hsrc := hsL s hs
    have h1 : 2 * (∫ t in s..(Real.pi / 4),
          Work.Elliptic.sinCos2 t * |Work.FTS.EllipticEst.Lzero1 u t|)
        ≤ 2 * (Ks * s ^ (-R)) := mul_le_mul_of_nonneg_left hsrc (by norm_num)
    have h2 : 2 * (Ks * s ^ (-R)) = KDL * s ^ (-R) := by rw [hKDLdef]; ring
    linarith [hD, h1, h2]
  have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro s hs
    rw [Set.uIcc_of_le hθle, Set.mem_Icc] at hs
    exact ⟨lt_of_lt_of_le hθpos hs.1, lt_of_le_of_lt hs.2 (by linarith [hpi])⟩
  -- the pointwise comparison against the kernel
  have hker : ∀ s ∈ Set.Icc θ (Real.pi / 4),
      |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * s ^ (-2 : ℝ)) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hθpos hs.1
    have hs4 : s ≤ Real.pi / 4 := hs.2
    have hsi : s ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hspos, by linarith [hs4, hpi]⟩
    have hdenpos : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
      mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi, hspos], hsi.2⟩)
        (pow_pos (sin_two_pos hsi) 2)
    have hDs : |Dfun u s| ≤ D0 + KDL * s ^ (-R) := Dbound s ⟨hspos, hs4⟩
    have hmono : s ^ (-R) ≤ θ ^ (-R) := rpow_neg_mono hθpos hs.1 hRpos
    have hDle : D0 + KDL * s ^ (-R) ≤ D0 + KDL * θ ^ (-R) := by
      have := mul_le_mul_of_nonneg_left hmono hKDLnn
      linarith
    have hAnn : 0 ≤ D0 + KDL * θ ^ (-R) :=
      add_nonneg hD0nn (mul_nonneg hKDLnn (Real.rpow_nonneg hθpos.le _))
    have hA1 : |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (D0 + KDL * θ ^ (-R)) / (Real.cos s * (Real.sin (2 * s)) ^ 2) :=
      div_le_div_of_nonneg_right (le_trans hDs hDle) hdenpos.le
    have hkerle : 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (Real.pi ^ 2 / 8) * s ^ (-2 : ℝ) := by
      have hh := hpowL s ⟨hspos, hs4⟩
      rwa [ker_rewrite s hspos] at hh
    have hA2 : (D0 + KDL * θ ^ (-R)) / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        = (D0 + KDL * θ ^ (-R)) * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
      rw [one_div, div_eq_mul_inv]
    have hA3 := mul_le_mul_of_nonneg_left hkerle hAnn
    linarith [hA1, hA2, hA3]
  have hcontf : ContinuousOn
      (fun s : ℝ => |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      (Set.uIcc θ (Real.pi / 4)) := by
    refine ContinuousOn.congr (((Lzero1Growth.continuousOn_Rderiv hu).abs).mono hsub) ?_
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (Real.pi / 2) := hsub hs
    have hdenpos : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
      mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi, hs'.1], hs'.2⟩)
        (pow_pos (sin_two_pos hs') 2)
    show |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      = |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
    rw [abs_div, abs_neg, abs_of_pos hdenpos]
  have hint1 : IntervalIntegrable
      (fun s : ℝ => |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      volume θ (Real.pi / 4) := hcontf.intervalIntegrable
  have hcontg : ContinuousOn
      (fun s : ℝ => (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * s ^ (-2 : ℝ)))
      (Set.uIcc θ (Real.pi / 4)) := by
    have hbase : ContinuousOn (fun s : ℝ => s) (Set.uIcc θ (Real.pi / 4)) := by fun_prop
    have hrp : ContinuousOn (fun s : ℝ => s ^ (-2 : ℝ)) (Set.uIcc θ (Real.pi / 4)) :=
      hbase.rpow_const (fun s hs => Or.inl (by
        have hs1 : s ∈ Set.Icc θ (Real.pi / 4) := by rwa [Set.uIcc_of_le hθle] at hs
        exact ne_of_gt (lt_of_lt_of_le hθpos hs1.1)))
    exact continuousOn_const.mul (continuousOn_const.mul hrp)
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * s ^ (-2 : ℝ)))
      volume θ (Real.pi / 4) := hcontg.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hθle hint1 hint2 hker
  have hval : (∫ s in θ..(Real.pi / 4),
        (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * s ^ (-2 : ℝ)))
      = (D0 + KDL * θ ^ (-R))
          * ((Real.pi ^ 2 / 8) * (∫ s in θ..(Real.pi / 4), s ^ (-2 : ℝ))) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  have hIk : (∫ s in θ..(Real.pi / 4),
        |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      ≤ (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ)) := by
    rw [hval] at hmono
    have hc : 0 ≤ (D0 + KDL * θ ^ (-R)) * (Real.pi ^ 2 / 8) :=
      mul_nonneg (add_nonneg hD0nn (mul_nonneg hKDLnn (Real.rpow_nonneg hθpos.le _)))
        (by positivity)
    have hthis := mul_le_mul_of_nonneg_left (hIntSq θ hθpos) hc
    have e1 : (D0 + KDL * θ ^ (-R))
          * ((Real.pi ^ 2 / 8) * (∫ s in θ..(Real.pi / 4), s ^ (-2 : ℝ)))
        = ((D0 + KDL * θ ^ (-R)) * (Real.pi ^ 2 / 8))
          * (∫ s in θ..(Real.pi / 4), s ^ (-2 : ℝ)) := by ring
    have e2 : ((D0 + KDL * θ ^ (-R)) * (Real.pi ^ 2 / 8)) * (1 / θ)
        = (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ)) := by ring
    linarith [hmono, hthis, e1, e2]
  have hRθ := hTB3 θ hθ
  have habs : |u θ| = |Rfun u θ| * Real.sin (2 * θ) := by
    rw [← Lzero1Growth.Rfun_mul_sin (u := u) hθi, abs_mul, abs_of_pos (sin_two_pos hθi)]
  have hsinle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
  have hcoef : |Rfun u θ|
      ≤ R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ)) := by
    linarith [hRθ, hIk]
  have hcoef0 : 0 ≤ R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ)) :=
    add_nonneg hR0nn (mul_nonneg
      (add_nonneg hD0nn (mul_nonneg hKDLnn (Real.rpow_nonneg hθpos.le _)))
      (mul_nonneg (by positivity) (div_nonneg zero_le_one hθpos.le)))
  have hstep : |u θ| ≤
      (R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ))) * (2 * θ) := by
    rw [habs]
    exact le_trans (mul_le_mul_of_nonneg_right hcoef (sin_two_pos hθi).le)
      (mul_le_mul_of_nonneg_left hsinle hcoef0)
  have hθ2 : (1 / θ) * (2 * θ) = 2 := by
    have hh : (1 / θ) * (2 * θ) = 2 * ((1 / θ) * θ) := by ring
    rw [hh, one_div, inv_mul_cancel₀ (ne_of_gt hθpos), mul_one]
  have hcalc : (R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ))) * (2 * θ)
      = 2 * θ * R0 + D0 * (Real.pi ^ 2 / 4) + KDL * (Real.pi ^ 2 / 4) * θ ^ (-R) := by
    calc (R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ))) * (2 * θ)
        = 2 * θ * R0
          + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * ((1 / θ) * (2 * θ))) := by ring
      _ = 2 * θ * R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * 2) := by rw [hθ2]
      _ = 2 * θ * R0 + D0 * (Real.pi ^ 2 / 4) + KDL * (Real.pi ^ 2 / 4) * θ ^ (-R) := by ring
  have hfin : 2 * θ * R0 + D0 * (Real.pi ^ 2 / 4) + KDL * (Real.pi ^ 2 / 4) * θ ^ (-R)
      ≤ C1 * θ ^ (-R) := by
    rw [hC1def]
    have h1 : 2 * θ * R0 ≤ 2 * (Real.pi / 4) * R0 * θ ^ (-R) := by
      have h2θ : 2 * θ ≤ Real.pi / 2 := by linarith
      have hb1 : 2 * θ * R0 ≤ (Real.pi / 2) * R0 := by
        have := mul_le_mul_of_nonneg_right h2θ hR0nn
        linarith [this]
      have hc1 : (Real.pi / 2) * R0 ≤ (Real.pi / 2) * R0 * θ ^ (-R) := by
        have hnn : 0 ≤ (Real.pi / 2) * R0 := mul_nonneg (by linarith [hpi]) hR0nn
        have := mul_le_mul_of_nonneg_left hθR1 hnn
        linarith [this]
      have he : 2 * (Real.pi / 4) * R0 * θ ^ (-R) = (Real.pi / 2) * R0 * θ ^ (-R) := by ring
      linarith [hb1, hc1, he]
    have h2 : D0 * (Real.pi ^ 2 / 4) ≤ D0 * (Real.pi ^ 2 / 4) * θ ^ (-R) := by
      have hnn : 0 ≤ D0 * (Real.pi ^ 2 / 4) := mul_nonneg hD0nn (by positivity)
      simpa using mul_le_mul_of_nonneg_left hθR1 hnn
    have hexp : (2 * (Real.pi / 4) * R0 + D0 * (Real.pi ^ 2 / 4) + KDL * (Real.pi ^ 2 / 4))
          * θ ^ (-R)
        = 2 * (Real.pi / 4) * R0 * θ ^ (-R) + D0 * (Real.pi ^ 2 / 4) * θ ^ (-R)
          + KDL * (Real.pi ^ 2 / 4) * θ ^ (-R) := by ring
    linarith [h1, h2, hexp]
  calc |u θ| ≤
        (R0 + (D0 + KDL * θ ^ (-R)) * ((Real.pi ^ 2 / 8) * (1 / θ))) * (2 * θ) := hstep
    _ = 2 * θ * R0 + D0 * (Real.pi ^ 2 / 4) + KDL * (Real.pi ^ 2 / 4) * θ ^ (-R) := hcalc
    _ ≤ C1 * θ ^ (-R) := hfin

/-! ## The right half `[π/4, π/2)` -/

private theorem poleBound_right {u : ℝ → ℝ} {R Ks : ℝ} (hR : 1 < R)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) (hKs : 0 ≤ Ks)
    (hsR : ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      (∫ s in (Real.pi / 4)..θ, Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|)
        ≤ Ks * (Real.pi / 2 - θ) ^ (1 - R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |u θ| ≤ C * (Real.pi / 2 - θ) ^ (-R) := by
  obtain ⟨_hpowL, hpowR, _hIntSq, _hDr1, _hDr2, hIntCube, _hDt1, _hDt2⟩ := powToolkit R hR
  obtain ⟨_hTB1, hTB2, _hTB3, hTB4⟩ := truncBounds u hu
  have hpi : 0 < Real.pi := Real.pi_pos
  set D0 : ℝ := |Dfun u (Real.pi / 4)| with hD0def
  set R0 : ℝ := |Rfun u (Real.pi / 4)| with hR0def
  have hD0nn : 0 ≤ D0 := by rw [hD0def]; exact abs_nonneg _
  have hR0nn : 0 ≤ R0 := by rw [hR0def]; exact abs_nonneg _
  set KDR : ℝ := 2 * Ks with hKDRdef
  have hKDRnn : 0 ≤ KDR := by rw [hKDRdef]; linarith
  set C2 : ℝ := (Real.pi / 2) * R0 + 2 * (Real.pi ^ 3 / 32) * D0
      + 2 * (Real.pi ^ 3 / 32) * KDR with hC2def
  have hC2nn : 0 ≤ C2 := by
    rw [hC2def]
    have h1 : 0 ≤ (Real.pi / 2) * R0 := mul_nonneg (by linarith [hpi]) hR0nn
    have h2 : 0 ≤ 2 * (Real.pi ^ 3 / 32) * D0 :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hD0nn
    have h3 : 0 ≤ 2 * (Real.pi ^ 3 / 32) * KDR :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hKDRnn
    linarith
  refine ⟨C2, hC2nn, ?_⟩
  intro θ hθ
  have hθlt : θ < Real.pi / 2 := hθ.2
  have hθpos : 0 < θ := by linarith [hθ.1, hpi]
  have hθi : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθlt⟩
  have hd : 0 < Real.pi / 2 - θ := by linarith
  have hd4 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθ.1]
  have hd1 : Real.pi / 2 - θ ≤ 1 := by linarith [hd4, Real.pi_lt_four]
  have hdR1 : 1 ≤ (Real.pi / 2 - θ) ^ (-R) := one_le_rpow_neg hd hd1 (by linarith)
  have hdinv : (Real.pi / 2 - θ) ^ (-1 : ℝ) ≤ (Real.pi / 2 - θ) ^ (-R) :=
    rpow_neg_one_le hd hd1 hR
  -- the `Dfun` bound at every `s ∈ [π/4, π/2)`
  have Dbound : ∀ s ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |Dfun u s| ≤ D0 + KDR * (Real.pi / 2 - s) ^ (1 - R) := by
    intro s hs
    have hD := hTB2 s hs
    have hsrc := hsR s hs
    have h1 : 2 * (∫ t in (Real.pi / 4)..s,
          Work.Elliptic.sinCos2 t * |Work.FTS.EllipticEst.Lzero1 u t|)
        ≤ 2 * (Ks * (Real.pi / 2 - s) ^ (1 - R)) :=
      mul_le_mul_of_nonneg_left hsrc (by norm_num)
    have h2 : 2 * (Ks * (Real.pi / 2 - s) ^ (1 - R)) = KDR * (Real.pi / 2 - s) ^ (1 - R) := by
      rw [hKDRdef]; ring
    linarith [hD, h1, h2]
  have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro s hs
    rw [Set.uIcc_of_le hθ.1, Set.mem_Icc] at hs
    exact ⟨by linarith [hpi, hs.1], lt_of_le_of_lt hs.2 hθlt⟩
  have hker : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
      |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - s) ^ (-3 : ℝ)) := by
    intro s hs
    have hs1 : Real.pi / 4 ≤ s := hs.1
    have hs2 : s ≤ θ := hs.2
    have hspos : 0 < s := by linarith [hpi]
    have hslt : s < Real.pi / 2 := lt_of_le_of_lt hs2 hθlt
    have hsi : s ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hspos, hslt⟩
    have hds : 0 < Real.pi / 2 - s := by linarith
    have hdenpos : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
      mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi, hspos], hslt⟩)
        (pow_pos (sin_two_pos hsi) 2)
    have hDs : |Dfun u s| ≤ D0 + KDR * (Real.pi / 2 - s) ^ (1 - R) :=
      Dbound s ⟨hs1, hslt⟩
    have hmono : (Real.pi / 2 - s) ^ (1 - R) ≤ (Real.pi / 2 - θ) ^ (1 - R) :=
      rpow_one_sub_mono hd (by linarith) hR
    have hDle : D0 + KDR * (Real.pi / 2 - s) ^ (1 - R)
        ≤ D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R) := by
      have := mul_le_mul_of_nonneg_left hmono hKDRnn
      linarith
    have hAnn : 0 ≤ D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R) :=
      add_nonneg hD0nn (mul_nonneg hKDRnn (Real.rpow_nonneg hd.le _))
    have hA1 : |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          / (Real.cos s * (Real.sin (2 * s)) ^ 2) :=
      div_le_div_of_nonneg_right (le_trans hDs hDle) hdenpos.le
    have hkerle : 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (Real.pi ^ 3 / 32) * (Real.pi / 2 - s) ^ (-3 : ℝ) := by
      have hh := hpowR s ⟨hs1, hslt⟩
      rwa [ker_rewrite' (Real.pi / 2 - s) hds] at hh
    have hA2 : (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        = (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
      rw [one_div, div_eq_mul_inv]
    have hA3 := mul_le_mul_of_nonneg_left hkerle hAnn
    linarith [hA1, hA2, hA3]
  have hcontf : ContinuousOn
      (fun s : ℝ => |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      (Set.uIcc (Real.pi / 4) θ) := by
    refine ContinuousOn.congr (((Lzero1Growth.continuousOn_Rderiv hu).abs).mono hsub) ?_
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (Real.pi / 2) := hsub hs
    have hdenpos : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
      mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi, hs'.1], hs'.2⟩)
        (pow_pos (sin_two_pos hs') 2)
    show |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      = |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
    rw [abs_div, abs_neg, abs_of_pos hdenpos]
  have hint1 : IntervalIntegrable
      (fun s : ℝ => |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      volume (Real.pi / 4) θ := hcontf.intervalIntegrable
  have hcontg : ContinuousOn
      (fun s : ℝ => (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
        * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - s) ^ (-3 : ℝ)))
      (Set.uIcc (Real.pi / 4) θ) := by
    have hbase : ContinuousOn (fun s : ℝ => Real.pi / 2 - s) (Set.uIcc (Real.pi / 4) θ) := by
      fun_prop
    have hrp : ContinuousOn (fun s : ℝ => (Real.pi / 2 - s) ^ (-3 : ℝ))
        (Set.uIcc (Real.pi / 4) θ) :=
      hbase.rpow_const (fun s hs => Or.inl (by
        have hs1 : s ∈ Set.Icc (Real.pi / 4) θ := by rwa [Set.uIcc_of_le hθ.1] at hs
        linarith [hs1.2, hθlt]))
    exact continuousOn_const.mul (continuousOn_const.mul hrp)
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
        * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - s) ^ (-3 : ℝ)))
      volume (Real.pi / 4) θ := hcontg.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hθ.1 hint1 hint2 hker
  have hval : (∫ s in (Real.pi / 4)..θ,
        (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - s) ^ (-3 : ℝ)))
      = (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * ((Real.pi ^ 3 / 32)
            * (∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-3 : ℝ))) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  have hD3 : (∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-3 : ℝ))
      ≤ (Real.pi / 2 - θ) ^ (-2 : ℝ) := by
    have hh := hIntCube θ ⟨hθ.1, hθ.2⟩
    have h2 : 0 ≤ (Real.pi / 2 - θ) ^ (-2 : ℝ) := Real.rpow_nonneg hd.le _
    linarith [hh, h2]
  have hIk : (∫ s in (Real.pi / 4)..θ,
        |Dfun u s| / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      ≤ (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
        * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ)) := by
    rw [hval] at hmono
    have hAnn : 0 ≤ D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R) :=
      add_nonneg hD0nn (mul_nonneg hKDRnn (Real.rpow_nonneg hd.le _))
    have hc : 0 ≤ (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R)) * (Real.pi ^ 3 / 32) :=
      mul_nonneg hAnn (by positivity)
    have hthis := mul_le_mul_of_nonneg_left hD3 hc
    have e1 : (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * ((Real.pi ^ 3 / 32)
            * (∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-3 : ℝ)))
        = ((D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R)) * (Real.pi ^ 3 / 32))
          * (∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-3 : ℝ)) := by ring
    have e2 : ((D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R)) * (Real.pi ^ 3 / 32))
          * ((Real.pi / 2 - θ) ^ (-2 : ℝ))
        = (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ)) := by ring
    linarith [hmono, hthis, e1, e2]
  have hRθ := hTB4 θ hθ
  have habs : |u θ| = |Rfun u θ| * Real.sin (2 * θ) := by
    rw [← Lzero1Growth.Rfun_mul_sin (u := u) hθi, abs_mul, abs_of_pos (sin_two_pos hθi)]
  have hsin2 : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
    have h2θ : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
    rw [h2θ, Real.sin_pi_sub]
    exact Real.sin_le (by linarith)
  have hcoef : |Rfun u θ|
      ≤ R0 + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
        * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ)) := by
    linarith [hRθ, hIk]
  have hcoef0 : 0 ≤ R0 + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
      * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ)) :=
    add_nonneg hR0nn (mul_nonneg
      (add_nonneg hD0nn (mul_nonneg hKDRnn (Real.rpow_nonneg hd.le _)))
      (mul_nonneg (by positivity) (Real.rpow_nonneg hd.le _)))
  have hstep : |u θ| ≤ (R0 + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
      * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ))) * (2 * (Real.pi / 2 - θ)) := by
    rw [habs]
    exact le_trans (mul_le_mul_of_nonneg_right hcoef (sin_two_pos hθi).le)
      (mul_le_mul_of_nonneg_left hsin2 hcoef0)
  have hcalc : (R0 + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
        * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ))) * (2 * (Real.pi / 2 - θ))
      = 2 * (Real.pi / 2 - θ) * R0 + 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
        + 2 * (Real.pi ^ 3 / 32) * KDR * (Real.pi / 2 - θ) ^ (-R) := by
    have hs1 : (Real.pi / 2 - θ) ^ (-2 : ℝ) * (Real.pi / 2 - θ)
        = (Real.pi / 2 - θ) ^ (-1 : ℝ) := rpow_neg_two_mul_self hd
    have hs2 : (Real.pi / 2 - θ) ^ (1 - R) * (Real.pi / 2 - θ) ^ (-1 : ℝ)
        = (Real.pi / 2 - θ) ^ (-R) := rpow_one_sub_mul_neg_one hd
    calc (R0 + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
          * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ))) * (2 * (Real.pi / 2 - θ))
        = 2 * (Real.pi / 2 - θ) * R0
          + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
            * (2 * (Real.pi ^ 3 / 32)
              * ((Real.pi / 2 - θ) ^ (-2 : ℝ) * (Real.pi / 2 - θ))) := by ring
      _ = 2 * (Real.pi / 2 - θ) * R0
          + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
            * (2 * (Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-1 : ℝ)) := by rw [hs1]
      _ = 2 * (Real.pi / 2 - θ) * R0
          + 2 * (Real.pi ^ 3 / 32) * (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
            * (Real.pi / 2 - θ) ^ (-1 : ℝ) := by ring
      _ = 2 * (Real.pi / 2 - θ) * R0
          + 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
          + 2 * (Real.pi ^ 3 / 32) * KDR
            * ((Real.pi / 2 - θ) ^ (1 - R) * (Real.pi / 2 - θ) ^ (-1 : ℝ)) := by ring
      _ = 2 * (Real.pi / 2 - θ) * R0
          + 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
          + 2 * (Real.pi ^ 3 / 32) * KDR * (Real.pi / 2 - θ) ^ (-R) := by rw [hs2]
  have hfin : 2 * (Real.pi / 2 - θ) * R0
        + 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
        + 2 * (Real.pi ^ 3 / 32) * KDR * (Real.pi / 2 - θ) ^ (-R)
      ≤ C2 * (Real.pi / 2 - θ) ^ (-R) := by
    rw [hC2def]
    have h1 : 2 * (Real.pi / 2 - θ) * R0
        ≤ (Real.pi / 2) * R0 * (Real.pi / 2 - θ) ^ (-R) := by
      have h2d : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 := by linarith
      have hb1 : 2 * (Real.pi / 2 - θ) * R0 ≤ (Real.pi / 2) * R0 := by
        have := mul_le_mul_of_nonneg_right h2d hR0nn
        linarith [this]
      have hc1 : (Real.pi / 2) * R0 ≤ (Real.pi / 2) * R0 * (Real.pi / 2 - θ) ^ (-R) := by
        have hnn : 0 ≤ (Real.pi / 2) * R0 := mul_nonneg (by linarith [hpi]) hR0nn
        have := mul_le_mul_of_nonneg_left hdR1 hnn
        linarith [this]
      linarith [hb1, hc1]
    have h2 : 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
        ≤ 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-R) := by
      have hnn : 0 ≤ 2 * (Real.pi ^ 3 / 32) * D0 :=
        mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hD0nn
      exact mul_le_mul_of_nonneg_left hdinv hnn
    have hexp : ((Real.pi / 2) * R0 + 2 * (Real.pi ^ 3 / 32) * D0
          + 2 * (Real.pi ^ 3 / 32) * KDR) * (Real.pi / 2 - θ) ^ (-R)
        = (Real.pi / 2) * R0 * (Real.pi / 2 - θ) ^ (-R)
          + 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-R)
          + 2 * (Real.pi ^ 3 / 32) * KDR * (Real.pi / 2 - θ) ^ (-R) := by ring
    linarith [h1, h2, hexp]
  calc |u θ| ≤ (R0 + (D0 + KDR * (Real.pi / 2 - θ) ^ (1 - R))
        * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-2 : ℝ))) * (2 * (Real.pi / 2 - θ)) := hstep
    _ = 2 * (Real.pi / 2 - θ) * R0 + 2 * (Real.pi ^ 3 / 32) * D0 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
          + 2 * (Real.pi ^ 3 / 32) * KDR * (Real.pi / 2 - θ) ^ (-R) := hcalc
    _ ≤ C2 * (Real.pi / 2 - θ) ^ (-R) := hfin

theorem poleBoundOfSourcePow {u g : ℝ → ℝ} {R : ℝ} (hR : 1 < R)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |g θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |u θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) := by
  have hRpos : 0 < R := by linarith
  have hR1pos : 0 < R - 1 := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the source bound, written with `rpow`
  have hbr : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |g θ| ≤ C * (θ ^ (-(R + 2)) + (Real.pi / 2 - θ) ^ (-(R + 2))) := by
    intro θ hθ
    have h1 : θ ^ (-(R + 2)) = 1 / θ ^ (R + 2) := by rw [one_div, Real.rpow_neg hθ.1.le]
    have h2 : (Real.pi / 2 - θ) ^ (-(R + 2)) = 1 / (Real.pi / 2 - θ) ^ (R + 2) := by
      rw [one_div, Real.rpow_neg (le_of_lt (by linarith [hθ.2] : (0 : ℝ) < Real.pi / 2 - θ))]
    rw [h1, h2]
    exact hb θ hθ
  obtain ⟨hsrcL, hsrcR⟩ := sourceBounds hR hC hu h hbr
  -- the two source constants are nonnegative
  have hKSpos : 0 < (4 / Real.pi) ^ (R + 2) :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) hpi) _
  have hKSnn : 0 ≤ (4 / Real.pi) ^ (R + 2) := hKSpos.le
  have hKsrcLnn : 0 ≤ C * (1 / R + (4 / Real.pi) ^ (R + 2) * (Real.pi / 4)) :=
    mul_nonneg hC.le (add_nonneg (div_nonneg zero_le_one hRpos.le)
      (mul_nonneg hKSnn (by linarith [hpi])))
  have hKsrcRnn : 0 ≤ C * ((Real.pi ^ 2 / 16) * (4 / Real.pi) ^ (R + 2) * (Real.pi / 2)
      + 1 / (R - 1)) :=
    mul_nonneg hC.le (add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hKSnn) (by linarith [hpi]))
      (div_nonneg zero_le_one hR1pos.le))
  obtain ⟨C1, hC1nn, h1⟩ := poleBound_left hR hu hKsrcLnn hsrcL
  obtain ⟨C2, hC2nn, h2⟩ := poleBound_right hR hu hKsrcRnn hsrcR
  refine ⟨max C1 C2, le_trans hC1nn (le_max_left _ _), fun θ hθ => ?_⟩
  have hCmaxnn : 0 ≤ max C1 C2 := le_trans hC1nn (le_max_left _ _)
  have hdpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have he : 1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R
      = θ ^ (-R) + (Real.pi / 2 - θ) ^ (-R) := by
    rw [one_div, one_div, Real.rpow_neg hθ.1.le, Real.rpow_neg hdpos.le]
  rw [he]
  by_cases hle : θ ≤ Real.pi / 4
  · have hl := h1 θ ⟨hθ.1, hle⟩
    have h2 : θ ^ (-R) ≤ θ ^ (-R) + (Real.pi / 2 - θ) ^ (-R) :=
      le_add_of_nonneg_right (Real.rpow_nonneg hdpos.le _)
    exact le_trans hl (mul_le_mul (le_max_left C1 C2) h2 (Real.rpow_nonneg hθ.1.le _) hCmaxnn)
  · have hgt : Real.pi / 4 < θ := not_le.mp hle
    have hr := h2 θ ⟨hgt.le, hθ.2⟩
    have h3 : (Real.pi / 2 - θ) ^ (-R) ≤ θ ^ (-R) + (Real.pi / 2 - θ) ^ (-R) :=
      le_add_of_nonneg_left (Real.rpow_nonneg hθ.1.le _)
    exact le_trans hr (mul_le_mul (le_max_right C1 C2) h3 (Real.rpow_nonneg hdpos.le _) hCmaxnn)

end Work.FTS.EllipticEst.H2W.WeakPureAux
